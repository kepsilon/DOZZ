/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.SeedOne.TwoChannel
public import DOZZ.ShiftEquations.Shifts.Seeds.Continuation
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.ShiftEquations.Reflection.Witness
import DOZZ.Brownian.Lateral.ReflectionJointLaw
import DOZZ.Correlations.Residue.FullFromUnit
import DOZZ.Correlations.Symmetry.SymmetricExtended
import DOZZ.ShiftEquations.Rbar.Continuation

/-!
# The first dual crossing seed from the dual fusion statement

For `α, ε, α' < Q` with `α + ε + α' > 2Q + 2/γ`:

* the two-channel identity (`dual_first_coefficient_of_classification`, classification
  only) gives `C(α - 2/γ, ε, α') = M · C(ε - 2/γ, α, α') ρ(ε, α, α')`, with `M` the dual crossing
  multiplier;
* the reflection identity at `α₁ = ε` (`dual_reflection_identity_near_Q` from the dual fusion
  statement near `Q`, continued over the whole interval by
  `dual_reflection_identity_continuation`) gives
  `C(ε - 2/γ, α, α') ρ(ε, α, α') = R(ε) C(2Q - ε - 2/γ, α, α')`;
* permutation symmetry of the structure constant reorders the last factor.

This is `dual_crossing_seed_one` ([KRV, Proposition 9.9]), from the conclusion of
`dual_full_fusion_and_asymptotic` alone.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

universe u

namespace DOZZ.Proofs

/-- Swapping the first two charges of a structure constant in the extended Seiberg domain. -/
theorem structureConstant_swap12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ a b c : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (h : ExtendedSeiberg3 γ a b c) :
    structureConstant P M γ μ a b c = structureConstant P M γ μ b a c := by
  rw [residue_structureConstant_eq_unitVolume, residue_structureConstant_eq_unitVolume,
    (unitVolumeStructureConstant_symmetric_extended P X M γ a b c hγ hγ2 hX hM h).1,
    show sExp γ b a c = sExp γ a b c by unfold sExp; ring_nf]

/-- **The first dual crossing seed from the dual fusion statement.** `hFusion` is the
conclusion of `dual_full_fusion_and_asymptotic`, quantified over all probability spaces of the
universe of `Ω`. -/
theorem dual_crossing_seed_one_of_fusion {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hFusion : ∀ {Ω : Type u} [MeasurableSpace Ω]
      {H : ℂ → ℂ → ℂ → ℂ → ℂ}
      (_hH : IsGaussHypergeometricFamily H)
      (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
      (γ μ α₁ α₂ α₃ η ξ : ℝ)
      (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
      (_hη : 0 < η) (_hη₂ : η < γ / 2) (_hξ : 0 < ξ) (_hξ₂ : ξ < 1)
      (_hαlo : Q γ - η < α₁) (_hαhi : α₁ < Q γ)
      (_hα₂ : α₂ < Q γ) (_hα₃ : α₃ < Q γ)
      (_hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
      (_hslack₁ : (4 / γ) * (Q γ - α₁) < ξ)
      (_hslack₂ : (4 / γ) * (Q γ - α₁) <
        (1 - ξ) * (4 - γ * α₁ - 2 * γ * η))
      (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
        ∃ Z : Ω → Measure ℝ,
          IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ α₁ (B α₁) Z ∧
          let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
          let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
          let c := gaussParameterC γ (2 / γ) α₁
          let κ := (4 / γ) * (Q γ - α₁)
          (∃ r : ℂ → ℝ,
            (∀ z, fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
              structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ +
                reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                    (‖z‖ ^ κ : ℝ) + r z) ∧
              Tendsto (fun z => r z / ‖z‖ ^ κ)
                (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0)) ∧
            (∀ z ∈ gaussCutPlane,
              fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
                structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
                    ‖gaussFMinus H a b c z‖ ^ 2 +
                  reflectionR P γ μ α₁ (B α₁) Z *
                    structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                      ‖gaussFPlus H a b c z‖ ^ 2)) :
    ∃ Bε : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        structureConstant P M γ μ (α - 2 / γ) ε α' =
          dualCrossingMultiplier γ α' α ε *
            reflectionR P γ μ ε Bε Z *
              structureConstant P M γ μ α (2 * Q γ - ε - 2 / γ) α' := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  -- the witnesses
  obtain ⟨A, hXcA, hAm, hA0, hBf, hBb, hInd, hLm, hIndL, hLat⟩ :=
    equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ₂ hX hM
  have hSLP : IsSourceLateralProjection P X γ M
      (fun ω => lateralProjectedGMC γ (A ω) (M ω)) :=
    ⟨hX, hM, A, hXcA, hAm, hA0, hBf, hBb, hInd, hLm, hIndL, Eventually.of_forall fun _ => rfl⟩
  obtain ⟨B, hB⟩ := exists_reflectionData_family P X γ M _ hSLP hLat
  refine ⟨B ε, fun ω => lateralProjectedGMC γ (A ω) (M ω), hSLP, hB ε hε, ?_⟩
  -- the reflection identity at `ε` for the spectators `(α, α')`
  have hrefl := dual_reflection_identity_continuation P X M γ μ α α' hγ hγ₂ hμ hα hα' hX hM
    (fun α₁ hα₁ hnear hs₁ B₁ Z₁ hB₁ =>
      dual_reflection_identity_near_Q P X M γ μ α₁ α α' hγ hγ₂ hμ hα₁ hnear hα hα' hs₁ hX hM B₁
        Z₁ hB₁ hFusion)
    ε hε (by linarith) (B ε) _ (hB ε hε)
  -- the two-channel identity
  have htwo := dual_first_coefficient_of_classification P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs
    hX hM
  -- permutation symmetry of the last factor
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have hES : ExtendedSeiberg3 γ (2 * Q γ - ε - 2 / γ) α α' :=
    extendedSeiberg3_of_lt hγ (by linarith) hα hα' (by linarith) (by linarith) (by linarith)
      (by linarith)
  rw [htwo, hrefl, structureConstant_swap12 P X M hγ hγ₂ hX hM hES]
  ring

end DOZZ.Proofs

end
