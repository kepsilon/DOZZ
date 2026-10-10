/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.RelativeKernel
public import DOZZ.FourPoint.Dual.RetainedZeroRelations
import Mathlib.Tactic

/-! # Relative comparison of the actual retained masses -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The literal moving and zero masses have two additive comparisons and a common quarter
lower bound. The radius is exactly the outer cutoff. -/
theorem dual_outerMass_relative_comparison (γ α₁ α₂ α₃ ξ : ℝ)
    (hγ : γ ≠ 0) (z : ℂ) (μ : Measure ℂ)
    (hr : 0 < ‖z‖ ^ (1 - ξ)) (hz : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    ENNReal.ofReal (1 / 4 : ℝ) * dualRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ ≤
        dualOuterMass γ α₁ α₂ α₃ μ z ξ ∧
    dualOuterMass γ α₁ α₂ α₃ μ z ξ ≤
      dualRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ +
        ENNReal.ofReal (4 * (‖z‖ / ‖z‖ ^ (1 - ξ))) *
          dualRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ ∧
    dualRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ ≤
      dualOuterMass γ α₁ α₂ α₃ μ z ξ +
        ENNReal.ofReal (4 * (‖z‖ / ‖z‖ ^ (1 - ξ))) *
          dualRetainedZeroMass γ α₁ α₂ α₃ (‖z‖ ^ (1 - ξ)) μ := by
  let r : ℝ := ‖z‖ ^ (1 - ξ)
  let d : ℝ := 4 * (‖z‖ / r)
  let D : Set ℂ := {x | r ≤ ‖x‖}
  let K : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)
  let K₀ : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x)
  have hd : 0 ≤ d := by dsimp only [d]; positivity
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hK : Measurable K := ENNReal.measurable_ofReal.comp (dual_kernel_measurable γ α₁ α₂ α₃ z)
  have hK₀ : Measurable K₀ := ENNReal.measurable_ofReal.comp (dual_kernel_measurable γ α₁ α₂ α₃ 0)
  have hs : ‖z‖ < r := by linarith only [hr, hz]
  rw [dual_retainedZero_kernel_integral γ α₁ α₂ α₃ r hγ μ h0 h1,
    dual_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ hγ z μ h0 h1 hs]
  have hp (x : ℂ) (hx : x ∈ D) :
      ENNReal.ofReal (1 / 4 : ℝ) * K₀ x ≤ K x ∧
        K x ≤ K₀ x + ENNReal.ofReal d * K₀ x ∧
          K₀ x ≤ K x + ENNReal.ofReal d * K₀ x := by
    have hn : 0 < ‖x‖ := hr.trans_le hx
    have hsep : ‖z‖ ≤ ‖x‖ / 2 := hz.trans (div_le_div_of_nonneg_right hx (by norm_num))
    have hbase : 0 ≤ dualFusionKernel γ α₁ α₂ α₃ 0 x := by unfold dualFusionKernel normPlus; positivity
    have hmove : 0 ≤ dualFusionKernel γ α₁ α₂ α₃ z x := by unfold dualFusionKernel normPlus; positivity
    have herr : |dualFusionKernel γ α₁ α₂ α₃ z x - dualFusionKernel γ α₁ α₂ α₃ 0 x| ≤
        d * dualFusionKernel γ α₁ α₂ α₃ 0 x := by
      apply (dual_kernel_relative_difference γ α₁ α₂ α₃ z x hn hsep).trans
      apply mul_le_mul_of_nonneg_right _ hbase
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_left (norm_nonneg _) hr hx
    have hl := dual_kernel_relative_lower γ α₁ α₂ α₃ z x hn hsep
    have hu := le_abs_self (dualFusionKernel γ α₁ α₂ α₃ z x - dualFusionKernel γ α₁ α₂ α₃ 0 x)
    have hv := neg_le_abs (dualFusionKernel γ α₁ α₂ α₃ z x - dualFusionKernel γ α₁ α₂ α₃ 0 x)
    dsimp only [K, K₀]
    refine ⟨?_, ?_, ?_⟩
    · rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hl])
    · rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_add hbase (mul_nonneg hd hbase)]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hu, herr])
    · rw [← ENNReal.ofReal_mul hd, ← ENNReal.ofReal_add hmove (mul_nonneg hd hbase)]
      exact ENNReal.ofReal_le_ofReal (by linarith only [hv, herr])
  refine ⟨?_, ?_, ?_⟩
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact setLIntegral_mono' hD fun x hx => (hp x hx).1
  · calc
      _ ≤ ∫⁻ x in D, K₀ x + ENNReal.ofReal d * K₀ x ∂μ :=
        setLIntegral_mono' hD fun x hx => (hp x hx).2.1
      _ = _ := by rw [lintegral_add_left hK₀, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · calc
      _ ≤ ∫⁻ x in D, K x + ENNReal.ofReal d * K₀ x ∂μ :=
        setLIntegral_mono' hD fun x hx => (hp x hx).2.2
      _ = _ := by rw [lintegral_add_left hK, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end DOZZ.Proofs
