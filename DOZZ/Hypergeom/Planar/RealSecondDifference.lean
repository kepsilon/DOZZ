/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorFiniteDifference
public import DOZZ.Hypergeom.Planar.RieszConvolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The real second derivative is dominated by the positive Riesz kernel. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- Centered real second difference of the radial power. -/
noncomputable def normPowerRealSecondDifference (k t : ℝ) (x : ℂ) : ℝ :=
  (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k) / t ^ 2

/-- The centered second difference of the parent kernel at the normalized center `1`. -/
noncomputable def planarRealSecondDifferenceQuotient (k β t : ℝ) (u : ℂ) : ℝ :=
  ‖u‖ ^ (-β) * normPowerRealSecondDifference k t (u - 1)

/-- Pointwise limit of the radial real second difference, multiplied by the singular weight. -/
noncomputable def planarRealSecondDifferenceLimit (k β : ℝ) (u : ℂ) : ℝ :=
  ‖u‖ ^ (-β) *
    ((k / 2) * (k / 2 - 1) * (‖u - 1‖ ^ 2) ^ (k / 2 - 2) *
        (2 * (u - 1).re) ^ 2 +
      (k / 2) * (‖u - 1‖ ^ 2) ^ (k / 2 - 1) * 2)

private theorem measurable_nonneg_rpow {f : ℂ → ℝ} (hf : Measurable f)
    (hfn : ∀ u, 0 ≤ f u) (p : ℝ) : Measurable (fun u => f u ^ p) := by
  have hrepr : (fun u => f u ^ p) =
      fun u => if f u = 0 then 0 ^ p else Real.exp (p * Real.log (f u)) := by
    funext u
    by_cases hu : f u = 0
    · simp [hu]
    · rw [ite_eq_right hu,
        Real.rpow_def_of_pos (lt_of_le_of_ne (hfn u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) hf
  · exact measurable_const
  · fun_prop

private theorem measurable_complex_norm_rpow (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) :=
  measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg u) p

private theorem measurable_normPowerRealSecondDifference (k t : ℝ) :
    Measurable (fun u : ℂ => normPowerRealSecondDifference k t (u - 1)) := by
  unfold normPowerRealSecondDifference
  have h₁ : Measurable (fun u : ℂ => ‖u - 1 + (t : ℂ)‖ ^ k) :=
    measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg _) k
  have h₂ : Measurable (fun u : ℂ => ‖u - 1 - (t : ℂ)‖ ^ k) :=
    measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg _) k
  have h₃ : Measurable (fun u : ℂ => ‖u - 1‖ ^ k) :=
    measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg _) k
  fun_prop

private theorem measurable_planarRealSecondDifferenceQuotient (k β t : ℝ) :
    Measurable (planarRealSecondDifferenceQuotient k β t) := by
  unfold planarRealSecondDifferenceQuotient
  exact (measurable_complex_norm_rpow (-β)).mul
    (measurable_normPowerRealSecondDifference k t)

/-- A global Riesz majorant for the real second difference at nonzero steps. -/
theorem normPowerRealSecondDifference_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (x : ℂ) (t : ℝ) (hx : x ≠ 0) (ht : t ≠ 0) :
    |normPowerRealSecondDifference k t x| ≤
      (2 * (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) +
        (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
  let C : ℝ := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  let B : ℝ := 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k)
  have hglobal := norm_rpow_centered_difference_le_global k hk hk₂ x (t : ℂ) hx
  have htNorm : ‖(t : ℂ)‖ ^ 2 = t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  change |(‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k -
    2 * ‖x‖ ^ k) / t ^ 2| ≤ _
  rw [abs_div, abs_of_pos ht2]
  have hupper :
      |‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k - 2 * ‖x‖ ^ k| ≤
        (2 * C + B) * ‖(t : ℂ)‖ ^ 2 * ‖x‖ ^ (k - 2) := by
    simpa [C, B] using hglobal
  calc
    _ ≤ ((2 * C + B) * ‖(t : ℂ)‖ ^ 2 * ‖x‖ ^ (k - 2)) / t ^ 2 :=
      div_le_div_of_nonneg_right hupper (le_of_lt ht2)
    _ = (2 * C + B) * ‖x‖ ^ (k - 2) := by
      rw [htNorm]
      calc
        _ = (2 * C + B) * ‖x‖ ^ (k - 2) * (t ^ 2 / t ^ 2) := by ring
        _ = _ := by rw [div_self ht2.ne']; ring
    _ = (2 * (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) +
        (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) * ‖x‖ ^ (k - 2) := by
          dsimp [C, B]
          ring

/-- Integrability of the centered quotient at every step. -/
theorem integrable_planarRealSecondDifferenceQuotient (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (t : ℝ) :
    Integrable (planarRealSecondDifferenceQuotient k β t) volume := by
  by_cases ht : t = 0
  · subst t
    have hzero : planarRealSecondDifferenceQuotient k β 0 = fun _ : ℂ => (0 : ℝ) := by
      funext u
      simp [planarRealSecondDifferenceQuotient, normPowerRealSecondDifference]
    rw [hzero]
    exact integrable_zero ℂ ℝ volume
  · let C : ℝ := 2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
        (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
    let bound : ℂ → ℝ := fun u => C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
    have hC : 0 ≤ C := by
      dsimp [C]
      have hk₂ : 0 < 1 - k / 2 := by linarith [hβ, hβ₂]
      positivity
    have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
    have hboundInt : Integrable bound volume := by
      simpa [bound, C, mul_assoc] using hRiesz.const_mul C
    have hpoint : ∀ᵐ u ∂volume,
        ‖planarRealSecondDifferenceQuotient k β t u‖ ≤ bound u := by
      filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
      have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
      have hk₂ : k < 2 := by linarith [hβ, hβ₂]
      have hnorm : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
      rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg hnorm]
      have hdiff := normPowerRealSecondDifference_le k hk hk₂ (u - 1) t hx ht
      have hmul := mul_le_mul_of_nonneg_left hdiff hnorm
      exact hmul.trans_eq (by dsimp only [bound, C]; ring)
    apply hboundInt.mono'
      (measurable_planarRealSecondDifferenceQuotient k β t).aestronglyMeasurable
    exact hpoint

/-- Pointwise second derivative limit of the weighted radial kernel. -/
theorem planarRealSecondDifferenceQuotient_tendsto (k β : ℝ) (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (planarRealSecondDifferenceLimit k β u)) := by
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  let w : ℝ := ‖u‖ ^ (-β)
  have hrad := norm_rpow_real_centered_difference_tendsto k (u - 1) hx
  have hmul : Tendsto
      (fun t : ℝ => w * normPowerRealSecondDifference k t (u - 1))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (w * ((k / 2) * (k / 2 - 1) * (‖u - 1‖ ^ 2) ^ (k / 2 - 2) *
        (2 * (u - 1).re) ^ 2 + (k / 2) * (‖u - 1‖ ^ 2) ^ (k / 2 - 1) * 2))) :=
    tendsto_const_nhds.mul hrad
  simpa [w, planarRealSecondDifferenceQuotient, planarRealSecondDifferenceLimit,
    normPowerRealSecondDifference, mul_assoc] using hmul

/-- Dominated convergence for the real second derivative of the normalized parent. -/
theorem planarRealSecondDifferenceQuotient_integral_tendsto (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (∫ u : ℂ, planarRealSecondDifferenceLimit k β u)) := by
  let C : ℝ := 2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2))) + (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  have hC : 0 ≤ C := by
    dsimp [C]
    have hk₂ : 0 < 1 - k / 2 := by linarith [hβ, hβ₂]
    positivity
  have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
  have hboundInt : Integrable bound volume := by
    simpa [bound, C, mul_assoc] using hRiesz.const_mul C
  have hmeas : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (planarRealSecondDifferenceQuotient k β t) volume := by
    filter_upwards [] with t
    exact (integrable_planarRealSecondDifferenceQuotient k β hk hβ hβ₂ t).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarRealSecondDifferenceQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
    have hk₂ : k < 2 := by linarith [hβ, hβ₂]
    have hnorm : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
    rw [planarRealSecondDifferenceQuotient, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hnorm]
    have hdiff := normPowerRealSecondDifference_le k hk hk₂ (u - 1) t hx ht0
    have hmul := mul_le_mul_of_nonneg_left hdiff hnorm
    exact hmul.trans_eq (by dsimp only [bound, C]; ring)
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun t : ℝ => planarRealSecondDifferenceQuotient k β t u)
      (𝓝[≠] (0 : ℝ)) (𝓝 (planarRealSecondDifferenceLimit k β u)) := by
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    exact planarRealSecondDifferenceQuotient_tendsto k β u hu
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    hmeas hbound hboundInt hlim

end DOZZ.Proofs
