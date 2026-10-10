/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.RootedInverse
public import DOZZ.Statements.GMC.EquatorGFFRootedGMCIdentity
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic

/-! # Rooting the actual dual retained inverse mass

This is the nonnegative Girsanov identity used in the dual outer correction.
Both spatial restrictions and the supplied chaos measure are retained literally.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual retained dual mass is a measurable functional of its supplied measure. -/
theorem dual_outerMass_measure_measurable (γ α₁ α₂ α₃ ξ : ℝ) (z : ℂ) :
    Measurable (fun μ : Measure ℂ => dualOuterMass γ α₁ α₂ α₃ μ z ξ) := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hf := (measurable_coulombWeight γ ![-2 / γ, α₁, α₂] ![z, 0, 1] α₃).indicator hD
  have hm := Measure.measurable_lintegral hf
  convert hm using 1
  funext μ
  unfold dualOuterMass
  rw [coulombMass_eq_lintegral_coulombWeight, lintegral_indicator hD]

/-- The rooted formula for every nonnegative deterministic spatial weight and inverse order. -/
theorem dual_outerMass_rooted_weight_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ q : ℝ) (z : ℂ) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ u, f u * (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ) ^ (-q) ∂M ω ∂P) =
      ∫⁻ u, ∫⁻ ω, f u *
        (dualOuterMass γ α₁ α₂ α₃ (gmcRootedMeasure γ u (M ω)) z ξ) ^ (-q)
          ∂P ∂gmcReferenceMeasure := by
  apply DOZZ.equatorGFF_rooted_GMC_identity P X hX γ hγ hγ₂ M hM
    (fun u _ μ => f u * (dualOuterMass γ α₁ α₂ α₃ μ z ξ) ^ (-q))
  exact (hf.comp measurable_fst).mul
    (((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp
      (measurable_snd.comp measurable_snd)).pow_const (-q))

/-- The actual weighted inverse moment is bounded by a deterministic spatial integral. -/
theorem dual_outerMass_rooted_weight_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      ∀ f : ℂ → ℝ, Measurable f →
        (∫⁻ ω, ∫⁻ u, ENNReal.ofReal (f u) *
          (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ) ^ (-q) ∂M ω ∂P) ≤
          ENNReal.ofReal C * (∫⁻ u, ENNReal.ofReal (f u) ∂gmcReferenceMeasure) := by
  obtain ⟨C, hC, hb⟩ := dual_rooted_outerMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq
  refine ⟨C, hC, ?_⟩
  intro z ξ hz hr f hf
  rw [dual_outerMass_rooted_weight_identity P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ ξ q z (fun u => ENNReal.ofReal (f u)) (ENNReal.measurable_ofReal.comp hf)]
  calc
    _ ≤ ∫⁻ u, ENNReal.ofReal (f u) * ENNReal.ofReal C ∂gmcReferenceMeasure := by
      apply lintegral_mono
      intro u
      dsimp only
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact mul_le_mul' le_rfl (hb z u ξ hz hr)
    _ = _ := by
      have he := lintegral_mul_const (μ := gmcReferenceMeasure) (ENNReal.ofReal C) (ENNReal.measurable_ofReal.comp hf)
      simpa only [Function.comp_def, mul_comm] using he

end DOZZ.Proofs
