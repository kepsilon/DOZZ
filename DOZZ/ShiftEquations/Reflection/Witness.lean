/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.BrownianPostMaximumPath
public import Mathlib.Probability.BrownianMotion.Basic
import DOZZ.Brownian.Lateral.RadialWindowUniform
import DOZZ.Brownian.Williams.Disintegration
import DOZZ.Brownian.Coupling.RadialTiltDensity

/-!
# One reflection witness for every charge on the supplied space

This is `exists_reflectionData_family`, in the Williams form. A source lateral projection carries a
radial path `A` whose two halves are independent standard Brownian motions, and `A` is independent
of the lateral measure. For a drift `ν > 0`, the path of a Brownian half after the global maximum of
its drifted version has the negative conditioned entrance law (Williams' decomposition). Taking a
measurable version of this post-maximum map and applying it to both halves of `A` gives two
independent conditioned paths, each a measurable function of `A`, hence jointly independent of the
lateral measure. One pair `(B, Z)` thus carries the reflection data of every charge `α < Q` at once,
with `Z` the given projection.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Williams: the post-maximum path of a Brownian path law has the negative conditioned law. -/
theorem map_brownianPostMaximumPath_eq (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (Q : Measure BrownianPath) (hQ : IsNegativeConditionedBrownianLaw ν Q) :
    P.map (brownianPostMaximumPath ν) = Q := by
  have _ := isProbabilityMeasure_brownianWilliamsPrefixLaw P hB ν hν
  have _ := hQ.2.1
  obtain ⟨hM, hPre, hPost, -⟩ :=
    brownian_williams_maximum_disintegration P hB ν hν Q hQ
  have hj := congrArg (fun μ => μ.map Prod.snd)
    (brownianPath_williams_joint_map P hB ν hν Q hQ)
  rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
    ((hM.prodMk hPre).prodMk hPost), Measure.map_snd_prod, measure_univ, one_smul] at hj
  exact hj

/-- **The reflection witness** (Williams form). A source lateral projection with its lateral law
carries reflection data for every charge below `Q`, all with the same lateral measure. -/
theorem exists_reflectionData_family {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hSLP : IsSourceLateralProjection P X γ M Z) (hZ : IsLateralGMCOf P γ Z) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∀ α : ℝ, α < Q γ → IsReflectionData P γ α (B α) Z := by
  obtain ⟨-, -, A, -, hAm, -, hBp, hBn, hInd, -, hAL, hZeq⟩ := hSLP
  have hWp : AEMeasurable (fun ω => radialPositiveHalf (A ω)) P :=
    continuous_radialPositiveHalf.measurable.comp_aemeasurable hAm
  have hWn : AEMeasurable (fun ω => radialNegativeHalf (A ω)) P :=
    continuous_radialNegativeHalf.measurable.comp_aemeasurable hAm
  have hLp := radialPositiveHalf_map_isBrownian P A hAm hBp
  have hLn := radialNegativeHalf_map_isBrownian P A hAm hBn
  have hpn : P.map (fun ω => radialNegativeHalf (A ω)) =
      P.map (fun ω => radialPositiveHalf (A ω)) := brownianPath_measure_unique _ _ hLn hLp
  have key : ∀ ν : ℝ, ∃ g : BrownianPath → BrownianPath, Measurable g ∧
      (0 < ν → IsNegativeConditionedBrownianLaw ν
        ((P.map fun ω => radialPositiveHalf (A ω)).map g)) := by
    intro ν
    by_cases hν : 0 < ν
    · obtain ⟨Qν, hQν, -⟩ := negativeConditionedBrownianLaw_exists ν hν.le
      have hae := aemeasurable_brownianPostMaximumPath _ hLp ν hν
      refine ⟨hae.mk _, hae.measurable_mk, fun _ => ?_⟩
      rw [Measure.map_congr hae.ae_eq_mk.symm,
        map_brownianPostMaximumPath_eq _ hLp ν hν Qν hQν]
      exact hQν
    · exact ⟨id, measurable_id, fun h => absurd h hν⟩
  choose g hgm hg using key
  refine ⟨fun α ω => (g (Q γ - α) (radialPositiveHalf (A ω)),
    g (Q γ - α) (radialNegativeHalf (A ω))), fun α hα => ?_⟩
  have hν : 0 < Q γ - α := sub_pos.mpr hα
  refine ⟨⟨⟨(hgm _).comp_aemeasurable hWp, ?_⟩, ⟨(hgm _).comp_aemeasurable hWn, ?_⟩, ?_⟩,
    hZ, ?_⟩
  · change IsNegativeConditionedBrownianLaw (Q γ - α)
      (P.map ((g (Q γ - α)) ∘ fun ω => radialPositiveHalf (A ω)))
    rw [← AEMeasurable.map_map_of_aemeasurable (hgm _).aemeasurable hWp]
    exact hg _ hν
  · change IsNegativeConditionedBrownianLaw (Q γ - α)
      (P.map ((g (Q γ - α)) ∘ fun ω => radialNegativeHalf (A ω)))
    rw [← AEMeasurable.map_map_of_aemeasurable (hgm _).aemeasurable hWn, hpn]
    exact hg _ hν
  · exact (radialHalves_indepFun P A hInd).comp (hgm _) (hgm _)
  · have hΦ : Measurable (fun a : TwoSidedPath =>
        (g (Q γ - α) (radialPositiveHalf a), g (Q γ - α) (radialNegativeHalf a))) :=
      ((hgm _).comp continuous_radialPositiveHalf.measurable).prodMk
        ((hgm _).comp continuous_radialNegativeHalf.measurable)
    exact (hAL.comp hΦ measurable_id).congr (ae_of_all _ fun _ => rfl)
      (hZeq.mono fun _ h => h.symm)

/-- Reflection data at one physical charge extend to a witness family for every charge below
`Q`, with the same lateral measure. -/
theorem exists_reflectionData_family_of_isReflectionData {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (γ α₀ : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (B₀ : Ω → BrownianPath × BrownianPath)
    (hSLP : IsSourceLateralProjection P X γ M Z) (hData : IsReflectionData P γ α₀ B₀ Z) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∀ α : ℝ, α < Q γ → IsReflectionData P γ α (B α) Z :=
  exists_reflectionData_family P X γ M Z hSLP hData.2.1

end DOZZ.Proofs

end
