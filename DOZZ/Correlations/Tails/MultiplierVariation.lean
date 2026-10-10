/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.UniformPositiveC1Family
public import DOZZ.Correlations.Tails.PinWickBound
public import Mathlib.Analysis.Calculus.MeanValue

/-! Quantitative local variation of the multiplier on the domain of
`DOZZ.UniformPositiveC1Family`. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The derivative bound in a `DOZZ.UniformPositiveC1Family` gives its stated linear local
variation, including points on the smaller closed ball. -/
theorem uniform_family_local_variation
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hz : z ∈ K) (F : ℂ → ℝ) (hF : F ∈ Family z)
    (x : ℂ) (hx : ‖x‖ ≤ radius) :
    |F (z + x) - F z| ≤ derivBound * ‖x‖ := by
  obtain ⟨hr, _, _, _, h⟩ := hFamily
  obtain ⟨_, _, _, hc, hd⟩ := h z hz F hF
  have hdiff := hc.differentiableOn (by norm_num)
  have hdiffAt : ∀ w ∈ Metric.closedBall z radius, DifferentiableAt ℝ F w := by
    intro w hw
    have hw' := Metric.closedBall_subset_ball (by linarith : radius < 2 * radius) hw
    exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hw')
  have hx' : z + x ∈ Metric.closedBall z radius := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hx
  have hz' : z ∈ Metric.closedBall z radius := Metric.mem_closedBall_self hr.le
  have hb := Convex.norm_image_sub_le_of_norm_fderiv_le hdiffAt hd
    (convex_closedBall z radius) hz' hx'
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hb

/-- Combining a linear multiplier bound with a first-order exponential correction retains
linear decay. This deterministic estimate is applied before the Gaussian moment bound. -/
theorem multiplier_exponential_variation
    (f f0 t L S D d : ℝ) (hf : |f - f0| ≤ L * d) (hf0 : |f0| ≤ S)
    (ht : |t| ≤ D * d) (hL : 0 ≤ L) (hd : 0 ≤ d) (hd1 : d ≤ 1) (hD : 0 ≤ D) :
    |f * Real.exp t - f0| ≤ (L + S * D) * Real.exp D * d := by
  have hS : 0 ≤ S := (abs_nonneg _).trans hf0
  have htD := ht.trans (mul_le_of_le_one_right hD hd1)
  have he : Real.exp t ≤ Real.exp D := Real.exp_le_exp.mpr ((le_abs_self t).trans htD)
  have hexp : |Real.exp t - 1| ≤ D * Real.exp D * d := by
    calc
      _ ≤ |t| * Real.exp |t| := exp_sub_one_bound t
      _ ≤ (D*d) * Real.exp D := mul_le_mul ht (Real.exp_le_exp.mpr htD)
        (Real.exp_nonneg _) (mul_nonneg hD hd)
      _ = _ := by ring
  calc
    _ = |(f - f0) * Real.exp t + f0 * (Real.exp t - 1)| := by congr 1; ring
    _ ≤ |(f - f0) * Real.exp t| + |f0 * (Real.exp t - 1)| := abs_add_le _ _
    _ = |f - f0| * Real.exp t + |f0| * |Real.exp t - 1| := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ (L*d) * Real.exp D + S * (D * Real.exp D * d) := add_le_add
      (mul_le_mul hf he (Real.exp_nonneg _) (mul_nonneg hL hd))
      (mul_le_mul hf0 hexp (abs_nonneg _) hS)
    _ = _ := by ring

end DOZZ.Proofs
