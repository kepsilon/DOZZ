/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.DualFusionRadialThreeCase
public import DOZZ.FourPoint.TwoRootedDomination
public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero

/-! Integrating an absolute Taylor majorant and turning a strict power margin into little-o. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The corrected time power is integrable whenever its exponent is greater than -1. -/
theorem time_rpow_integral (e : ℝ) (he : -1 < e) :
    IntegrableOn (fun t : ℝ => t ^ e) (Icc 0 1) volume ∧
      (∫ t in Icc (0 : ℝ) 1, t ^ e) = 1 / (e + 1) := by
  refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
    (intervalIntegral.intervalIntegrable_rpow' he), ?_⟩
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simpa only [Real.one_rpow, Real.zero_rpow (by linarith only [he] : e + 1 ≠ 0), sub_zero]
    using integral_rpow (a := 0) (b := 1) (Or.inl he)

/-- The time integration requires neither continuity nor a value for the integrand at t=0. -/
theorem time_integral_bound (F : ℂ → ℂ) (C e r : ℝ)
    (_hC : 0 ≤ C) (he : -1 < e) (_hr : 0 < r)
    (hF : ∀ w : ℂ, w ≠ 0 → ‖w‖ ≤ r → ‖F w‖ ≤ C * ‖w‖ ^ e)
    (z : ℂ) (hz : z ≠ 0) (hzr : ‖z‖ ≤ r) :
    ‖∫ t in Icc (0 : ℝ) 1, (1 - t : ℝ) * F ((t : ℂ) * z)‖ ≤
      C * ‖z‖ ^ e / (e + 1) := by
  obtain ⟨hint, hval⟩ := time_rpow_integral e he
  have hbound : IntegrableOn (fun t : ℝ => (C * ‖z‖ ^ e) * t ^ e) (Icc 0 1) volume :=
    hint.const_mul _
  have hae : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton (μ := volume) (0 : ℝ))
  have hdom : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖(1 - t : ℝ) * F ((t : ℂ) * z)‖ ≤ (C * ‖z‖ ^ e) * t ^ e := by
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hae] with t ht ht0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
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
  have h := norm_integral_le_of_norm_le hbound hdom
  rw [integral_const_mul, hval] at h
  simpa only [mul_one_div] using h

/-- A uniform strict power bound implies the literal punctured-origin little-o convention. -/
theorem power_bound_littleO (f : ℂ → ℂ) (κ η C r : ℝ)
    (hη : 0 < η) (hr : 0 < r)
    (hf : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ r → ‖f z‖ ≤ C * ‖z‖ ^ (κ + η)) :
    IsComplexLittleOAtZero κ f := by
  have hlim : Tendsto (fun z : ℂ => C * ‖z‖ ^ η)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
    have h := ((Real.continuous_rpow_const hη.le).continuousAt.tendsto.comp
      (tendsto_norm_zero : Tendsto (fun z : ℂ => ‖z‖) (nhds 0) (nhds 0))).const_mul C
    simpa only [Function.comp_apply, Real.zero_rpow hη.ne', mul_zero] using h.mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun z => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
  · have hradius : ∀ᶠ z : ℂ in nhds (0 : ℂ), ‖z‖ < r := by
      have hball : ∀ᶠ z : ℂ in nhds (0 : ℂ), z ∈ Metric.ball 0 r :=
        Metric.ball_mem_nhds (0 : ℂ) hr
      filter_upwards [hball] with z hz
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    filter_upwards [hradius.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hzr hz
    have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h := div_le_div_of_nonneg_right (hf z hz hzr.le) (Real.rpow_pos_of_pos hnz κ).le
    rw [Real.rpow_add hnz] at h
    have heq : C * (‖z‖ ^ κ * ‖z‖ ^ η) / ‖z‖ ^ κ = C * ‖z‖ ^ η := by
      field_simp [(Real.rpow_pos_of_pos hnz κ).ne']
    rw [heq] at h
    exact h

end DOZZ.Proofs
