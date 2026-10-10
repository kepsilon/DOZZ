/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.SingularMoment
public import DOZZ.Correlations.Tails.SingularMassMeasurability

/-! Bounded multipliers preserve the uniform mixed moment estimate of the separated joint-tail
argument. -/

@[expose] public section
open MeasureTheory Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The literal extended-real insertion mass is dominated by the bare singular mass. -/
theorem separatedTail_localSingularMass_le
    {Ω : Type*} (M : Ω → Measure ℂ) (F : ℂ → ℝ) (z : ℂ) (γ α : ℝ)
    (S : ℝ≥0∞) (hS : S ≠ ⊤) (hF : ∀ x, ENNReal.ofReal (F x) ≤ S) (ω : Ω) :
    localSingularMass M F z γ α ω ≤ S * weightedGmcBallMass γ (M ω) α z 1 := by
  classical
  unfold localSingularMass weightedGmcBallMass
  rw [← lintegral_const_mul' S _ hS, ← lintegral_indicator measurableSet_ball]
  apply lintegral_mono
  intro x
  by_cases hx : x ∈ ball z 1
  · simpa only [hx, ite_true, Set.indicator_of_mem] using
      mul_le_mul_left (hF x) ((ENNReal.ofReal ‖x-z‖).rpow (-γ*α))
  · simp only [hx, ite_false]
    exact zero_le

/-- One finite constant works for all bounded multipliers and all insertion orders below `T`. -/
theorem separatedTail_local_mixed_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (F2 F3 : ℂ → ℝ) (z2 z3 : ℂ) (γ α2 α3 a2 a3 T : ℝ)
    (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (ha2T : a2 ≤ T) (ha3T : a3 ≤ T)
    (S B : ℝ≥0∞) (hS1 : 1 ≤ S) (hS : S ≠ ⊤)
    (hF2 : ∀ x, ENNReal.ofReal (F2 x) ≤ S) (hF3 : ∀ x, ENNReal.ofReal (F3 x) ≤ S)
    (hB : (∫⁻ ω, weightedGmcBallMass γ (M ω) α2 z2 1 ^ a2 *
      weightedGmcBallMass γ (M ω) α3 z3 1 ^ a3 ∂P) ≤ B) :
    (∫⁻ ω, localSingularMass M F2 z2 γ α2 ω ^ a2 *
      localSingularMass M F3 z3 γ α3 ω ^ a3 ∂P) ≤ S^(2*T)*B := by
  have hSn : S ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hS1)
  calc
    _ ≤ ∫⁻ ω, (S*weightedGmcBallMass γ (M ω) α2 z2 1)^a2 *
        (S*weightedGmcBallMass γ (M ω) α3 z3 1)^a3 ∂P := by
      apply lintegral_mono
      intro ω
      exact mul_le_mul' (ENNReal.rpow_le_rpow (separatedTail_localSingularMass_le M F2 z2 γ α2 S hS hF2 ω) ha2)
        (ENNReal.rpow_le_rpow (separatedTail_localSingularMass_le M F3 z3 γ α3 S hS hF3 ω) ha3)
    _ = S^(a2+a3) * ∫⁻ ω, weightedGmcBallMass γ (M ω) α2 z2 1 ^ a2 *
        weightedGmcBallMass γ (M ω) α3 z3 1 ^ a3 ∂P := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ ha2, ENNReal.mul_rpow_of_nonneg _ _ ha3]
      rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (add_nonneg ha2 ha3) hS)]
      apply lintegral_congr
      intro ω
      rw [ENNReal.rpow_add _ _ hSn hS]
      ac_rfl
    _ ≤ S^(2*T)*B := mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_le hS1
      (by linarith)) hB

end DOZZ.Proofs
