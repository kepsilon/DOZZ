/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorTimeIntegration

/-! # Integrability of signed Taylor time integrals -/

@[expose] public section
open MeasureTheory Set Filter
namespace DOZZ.Proofs

/-- A measurable spatial expectation with a power bound gives an integrable Taylor time
integrand. The value at time zero is irrelevant. -/
theorem fusion_time_integrable_of_power_bound (F : ℂ → ℂ) (hFm : Measurable F)
    (C e r : ℝ) (he : -1 < e)
    (hF : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ r → ‖F w‖ ≤ C * ‖w‖ ^ e)
    (z : ℂ) (hz : z ≠ 0) (hzr : ‖z‖ ≤ r) :
    IntegrableOn (fun t : ℝ => (1 - t : ℝ) * F ((t : ℂ) * z)) (Icc 0 1) volume := by
  have hmeas : Measurable (fun t : ℝ => (1 - t : ℝ) * F ((t : ℂ) * z)) :=
    (Complex.measurable_ofReal.comp (measurable_const.sub measurable_id)).mul
      (hFm.comp (Complex.measurable_ofReal.mul_const z))
  have hint := (time_rpow_integral e he).1.const_mul (C * ‖z‖ ^ e)
  apply hint.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
  have htz : ‖(t : ℂ) * z‖ = t * ‖z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
  have htr : ‖(t : ℂ) * z‖ ≤ r := by
    rw [htz]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hzr
  have hfn := hF ((t : ℂ) * z) (mul_ne_zero (Complex.ofReal_ne_zero.mpr ht0) hz) htr
  rw [htz, Real.mul_rpow ht.1 (norm_nonneg _)] at hfn
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr ht.2)]
  calc
    (1 - t) * ‖F ((t : ℂ) * z)‖ ≤ ‖F ((t : ℂ) * z)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (by linarith only [ht.1])
    _ ≤ C * (t ^ e * ‖z‖ ^ e) := hfn
    _ = (C * ‖z‖ ^ e) * t ^ e := by ring

/-- Integrable local and exterior expectations can be split inside the time integral. -/
theorem fusion_time_split (F L E : ℂ → ℂ) (z : ℂ)
    (hL : IntegrableOn (fun t : ℝ => (1 - t : ℝ) * L ((t : ℂ) * z)) (Icc 0 1) volume)
    (hE : IntegrableOn (fun t : ℝ => (1 - t : ℝ) * E ((t : ℂ) * z)) (Icc 0 1) volume)
    (h : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1), F ((t : ℂ) * z) = L ((t : ℂ) * z) + E ((t : ℂ) * z)) :
    (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * F ((t : ℂ) * z)) =
      (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * L ((t : ℂ) * z)) +
      (∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * E ((t : ℂ) * z)) := by
  calc
    _ = ∫ t in Icc (0 : ℝ) 1,
        ((1 - t : ℝ) * L ((t : ℂ) * z) + (1 - t : ℝ) * E ((t : ℂ) * z)) := by
      apply integral_congr_ae
      filter_upwards [h] with t ht
      rw [ht, mul_add]
    _ = _ := integral_add hL hE

end DOZZ.Proofs
