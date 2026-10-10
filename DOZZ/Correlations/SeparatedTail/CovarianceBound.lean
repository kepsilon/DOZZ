/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.MarkovAssembly
public import DOZZ.GMC.SharpMoments.CircleField
public import DOZZ.GMC.CirclePotential

/-! The finite-circle equator/Dirichlet covariance discrepancy on the unit disks of the separated
joint-tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Metric Set

namespace DOZZ.Proofs


/-- On a unit disk inside the disk of radius `5/4`, the regular Green numerator stays
uniformly separated from zero, including at the coincident pair. -/
theorem separatedTail_green_numerator_bounds (c x y : ℂ)
    (hx : ‖x-c‖ ≤ 1) (hy : ‖y-c‖ ≤ 1) :
    (9/16 : ℝ) ≤ ‖((5/4 : ℝ) : ℂ)^2-(x-c)*star (y-c)‖ ∧
      ‖((5/4 : ℝ) : ℂ)^2-(x-c)*star (y-c)‖ ≤ 41/16 := by
  have hprod : ‖(x-c)*star (y-c)‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    nlinarith [norm_nonneg (x-c), norm_nonneg (y-c)]
  have hs : ‖((5/4 : ℝ) : ℂ)^2‖ = (25/16 : ℝ) := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  have hupper := norm_sub_le (((5/4 : ℝ) : ℂ)^2) ((x-c)*star (y-c))
  have hlower := norm_sub_norm_le (((5/4 : ℝ) : ℂ)^2) ((x-c)*star (y-c))
  rw [hs] at hupper hlower
  constructor <;> linarith

/-- The regular Green logarithm has an absolute bound independent of the disk center. -/
theorem separatedTail_green_regular_log_abs_le (c x y : ℂ)
    (hx : ‖x-c‖ ≤ 1) (hy : ‖y-c‖ ≤ 1) :
    |Real.log ‖((5/4 : ℝ) : ℂ)^2-(x-c)*star (y-c)‖| ≤ 3 := by
  obtain ⟨hl, hu⟩ := separatedTail_green_numerator_bounds c x y hx hy
  have h0 : 0 < ‖((5/4 : ℝ) : ℂ)^2-(x-c)*star (y-c)‖ := by linarith
  have hlogu := Real.log_le_sub_one_of_pos h0
  have hlogl := Real.one_sub_inv_le_log_of_pos h0
  have hinv : ‖((5/4 : ℝ) : ℂ)^2-(x-c)*star (y-c)‖⁻¹ ≤ (16/9 : ℝ) := by
    calc
      _ ≤ (9/16 : ℝ)⁻¹ := (inv_le_inv₀ h0 (by norm_num)).mpr hl
      _ = _ := by norm_num
  rw [abs_le]
  constructor <;> linarith

/-- The equator regular circle term is bounded on every bounded chart. -/
theorem separatedTail_circle_regular_bounds (c x : ℂ) (R r : ℝ)
    (hR : 1 < R) (hpin : ‖c‖+5/4 ≤ R) (hx : ‖x-c‖+Real.exp (-r) < 5/4) :
    0 ≤ (∫ z, Real.log (normPlus z) ∂circleMeasure x r) ∧
      (∫ z, Real.log (normPlus z) ∂circleMeasure x r) ≤ R := by
  let _ := circleMeasure_isProbability x r
  have hi : Integrable (fun z => Real.log (normPlus z)) (circleMeasure x r) :=
    integrable_circleMeasure_of_circleIntegrable x r continuous_log_normPlus.measurable
      continuous_log_normPlus.continuousOn.circleIntegrable'
  refine ⟨integral_nonneg (fun z => Real.log_nonneg (le_max_left _ _)), ?_⟩
  have hb : ∀ᵐ z ∂circleMeasure x r, Real.log (normPlus z) ≤ R := by
    filter_upwards [interior_circle_norm_le_pin c x R (5/4) r hpin hx] with z hz
    have hnorm : normPlus z ≤ R := max_le hR.le hz
    have hp : 0 < normPlus z := zero_lt_one.trans_le (le_max_left _ _)
    exact (Real.log_le_sub_one_of_pos hp).trans (by linarith)
  simpa only [integral_const, probReal_univ, one_smul] using
    integral_mono_ae hi (integrable_const R) hb

/-- The literal finite-cutoff covariance difference cancels the same circle logarithmic
potential on both sides. This also applies on the diagonal. -/
theorem separatedTail_circle_covariance_discrepancy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (Dc : Ω → ℂ → ℝ → ℝ) (c : ℂ) (R r : ℝ) (hR : 1 < R)
    (hpin : ‖c‖+5/4 ≤ R)
    (hDc : ∀ x y, ‖x-c‖+Real.exp (-r) < 5/4 → ‖y-c‖+Real.exp (-r) < 5/4 →
      (∫ ω, Dc ω x r * Dc ω y r ∂P) =
        ∫ v, ∫ w, diskGreenKernel c (5/4) (by norm_num) v w
          ∂circleMeasure y r ∂circleMeasure x r)
    (x y : ℂ) (hx : ‖x-c‖ ≤ 1) (hy : ‖y-c‖ ≤ 1)
    (hr : Real.exp (-r) < 1/4) :
    |(∫ ω, Xc ω x r * Xc ω y r ∂P) -
      (∫ ω, Dc ω x r * Dc ω y r ∂P)| ≤ 4+2*R := by
  have hxi : ‖x-c‖+Real.exp (-r) < 5/4 := by linarith
  have hyi : ‖y-c‖+Real.exp (-r) < 5/4 := by linarith
  rw [circleField_covariance_eq P X hX Xc hc x y r]
  unfold circleKernel
  rw [integral_integral_gffKernel_eq_logmax, hDc x y hxi hyi,
    integral_integral_diskGreenKernel c x y (5/4) r r (by norm_num) hxi hyi]
  obtain ⟨hxl, hxu⟩ := separatedTail_circle_regular_bounds c x R r hR hpin hxi
  obtain ⟨hyl, hyu⟩ := separatedTail_circle_regular_bounds c y R r hR hpin hyi
  have hreg := abs_le.mp (separatedTail_green_regular_log_abs_le c x y hx hy)
  have hlogl : 0 ≤ Real.log (5/4 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogu : Real.log (5/4 : ℝ) ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  rw [abs_le]
  constructor <;> linarith

end DOZZ.Proofs
