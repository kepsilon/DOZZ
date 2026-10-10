/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.JointLawExpectation
public import DOZZ.FourPoint.Dual.WilliamsCutBounds
/-! Finiteness transfers through the joint Williams law, with the source witness retained. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The random maximum/cut Williams mass is finite on the supplied reflection witness. -/
theorem dual_williams_cut_mass_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    ∀ᵐ q : ℝ × Ω ∂(brownianMaximumReferenceLaw (Q γ-α)).prod P,
      ENNReal.ofReal (Real.exp (γ*q.1))*twoSidedReflectionCutMass γ q.1 B Z q.2 ≠ ⊤ := by
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα)
  filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae
    (reflected_reflection_mass_positive_finite_ae P γ α B Z hγ hγ₂ hα hData)] with q hq
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top hq.2.ne (twoSidedReflectionCutMass_le_mass γ q.1 B Z q.2))

/-- Finiteness of the reference inner mass transfers to the actual copied polar integral
through its joint exterior law. -/
theorem dual_copied_joint_law_finite
    {Ω Λ ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace ζ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (Y : Ω → ζ) (hY : AEMeasurable Y P) (V : Ω × Ω → ℝ≥0∞)
    (hV : AEMeasurable V (P.prod P)) (J : Λ → ℝ≥0∞) (hJ : AEMeasurable J R)
    (hLaw : (P.prod P).map (fun ω => (Y ω.1,V ω)) = (P.map Y).prod (R.map J))
    (hfinite : ∀ᵐ ω ∂R, J ω ≠ ⊤) : ∀ᵐ ω ∂P.prod P, V ω ≠ ⊤ := by
  have hs := hY.comp_fst.prodMk hV
  have hr := hY.comp_fst.prodMk hJ.comp_snd
  have hset : MeasurableSet {v : ζ × ℝ≥0∞ | v.2 ≠ ⊤} :=
    (measurable_snd (measurableSet_singleton ⊤)).compl
  have he : ∀ᵐ ω : Ω × Λ ∂P.prod R, (Y ω.1,J ω.2).2 ≠ ⊤ :=
    measurePreserving_snd.quasiMeasurePreserving.ae hfinite
  have hm := (ae_map_iff hr hset).mpr he
  rw [dual_independent_copy_map_law P R Y J hY hJ, ← hLaw] at hm
  exact (ae_map_iff hs hset).mp hm

end DOZZ.Proofs
