/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedCompactSingularLaw
public import DOZZ.Correlations.Tails.OffCenterMultiplier

/-! Compact copied tests built from the literal locally C1 multiplier family. -/

@[expose] public section
open MeasureTheory Set

namespace DOZZ.Proofs

/-- Localizing inside the common C1 neighborhood produces the exact compact test used
in the copied singular law; global continuity of the original multiplier is unnecessary. -/
theorem localized_translated_test
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hzk : z ∈ K) (F : ℂ → ℝ) (hF : F ∈ Family z) (γ : ℝ)
    (χ : BoundedContinuousFunction ℂ ℝ) (hχc : HasCompactSupport (χ : ℂ → ℝ))
    (hχ0 : ∀ x, 0 ≤ χ x) (hχs : tsupport (χ : ℂ → ℝ) ⊆ Metric.ball 0 (min radius 1)) :
    ∃ g : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (g : ℂ → ℝ) ∧
      (∀ x, g x = χ x * F (z+x) * Real.exp (-(γ^2+4)*Real.log (normPlus (z+x)))) ∧
      (∀ x, 0 ≤ g x) ∧ tsupport (g : ℂ → ℝ) ⊆ Metric.ball 0 1 := by
  let V : ℂ → ℝ := fun x => Real.exp (-(γ^2+4)*Real.log (normPlus (z+x)))
  have hV : Continuous V :=
    (((continuous_const.max (continuous_const.add continuous_id).norm).log
      (fun _ => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))).const_mul
        (-(γ^2+4))).rexp
  let G : ℂ → ℝ := fun x => χ x * (F (z+x)*V x)
  have hs : tsupport G ⊆ tsupport (χ : ℂ → ℝ) := tsupport_mul_subset_left
  have hsu : tsupport G ⊆ Metric.ball 0 (2*radius) := by
    intro x hx
    have h := hχs (hs hx)
    have hn : ‖x‖ < min radius 1 := by simpa only [Metric.mem_ball, dist_zero_right] using h
    have hr := hFamily.1
    simp only [Metric.mem_ball, dist_zero_right]
    exact hn.trans_le ((min_le_left _ _).trans (by linarith))
  have hFc : ContinuousOn (fun x => F (z+x)) (Metric.ball 0 (2*radius)) := by
    have hcont := (hFamily.2.2.2.2 z hzk F hF).2.2.2.1.continuousOn
    exact hcont.comp (continuous_const.add continuous_id).continuousOn (by
      intro x hx
      simpa only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hx)
  have hGc : Continuous G :=
    (χ.continuous.continuousOn.mul (hFc.mul hV.continuousOn)).continuous_of_tsupport_subset
      Metric.isOpen_ball hsu
  have hGs : HasCompactSupport G := hχc.mul_right
  let hb := hGc.bounded_above_of_compact_support hGs
  let g := BoundedContinuousFunction.ofNormedAddCommGroup G hGc hb.choose hb.choose_spec
  refine ⟨g, hGs, ?_, ?_, ?_⟩
  · intro x
    change χ x * (F (z+x)*V x) = _
    rw [mul_assoc]
  · intro x
    change 0 ≤ χ x * (F (z+x)*V x)
    exact mul_nonneg (hχ0 x) (mul_nonneg
      ((hFamily.2.2.2.2 z hzk F hF).2.1 (z+x)).1 (Real.exp_nonneg _))
  · exact hs.trans (hχs.trans (Metric.ball_subset_ball (min_le_right _ _)))


end DOZZ.Proofs
