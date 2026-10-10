/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneMultiNegativeMellin
public import DOZZ.GMC.KahaneLowerEnvelope
public import DOZZ.GMC.KahaneEnvelopeTonelli

/-! Mellin transforms of lower measurable Laplace envelopes. -/

@[expose] public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace DOZZ.Proofs

noncomputable def mellinEnvelope (q : ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.Gamma q) * ∫⁻ t in Ioi (0 : ℝ),
    ENNReal.ofReal (t ^ (q - 1)) * r ^ (t / q) ∂volume

noncomputable def inverseMellinEnvelope (q : ℝ) (z : ℝ≥0∞) : ℝ≥0∞ :=
  if z = 0 then 0 else ENNReal.ofReal (Real.exp (-q * (z ^ (-q⁻¹)).toReal))

/-- The envelope Mellin transform recovers the negative power of a nonnegative mass. -/
theorem mellinEnvelope_exp (q m : ℝ) (hq : 0 < q) (hm : 0 ≤ m) :
    mellinEnvelope q (ENNReal.ofReal (Real.exp (-q * m))) = ENNReal.ofReal m ^ (-q) := by
  change mellinEnvelope q (ENNReal.ofReal (Real.exp (-q * m))) =
    ENNReal.rpow (ENNReal.ofReal m) (-q)
  rw [nonneg_rpow_neg_eq_mellin_lintegral hm hq]
  unfold mellinEnvelope
  congr 1
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
  congr 2
  field_simp

theorem mellinEnvelope_zero (q : ℝ) (hq : 0 < q) : mellinEnvelope q 0 = 0 := by
  unfold mellinEnvelope
  have hz : (fun t : ℝ => ENNReal.ofReal (t ^ (q - 1)) * (0 : ℝ≥0∞) ^ (t / q)) =ᵐ[
      volume.restrict (Ioi (0 : ℝ))] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [ENNReal.zero_rpow_of_pos (div_pos ht hq)]
  rw [lintegral_congr_ae hz]
  simp only [Pi.zero_apply, lintegral_zero, mul_zero]

theorem mellinEnvelope_monotone (q : ℝ) (hq : 0 < q) : Monotone (mellinEnvelope q) := by
  intro r s hrs
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow hrs (div_nonneg ht.le hq.le)) (by positivity)

theorem inverseMellinEnvelope_measurable (q : ℝ) : Measurable (inverseMellinEnvelope q) := by
  unfold inverseMellinEnvelope
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  fun_prop

/-- Mellin and its inverse also agree at zero and at infinity. -/
theorem mellinEnvelope_inverse (q : ℝ) (hq : 0 < q) (z : ℝ≥0∞) :
    mellinEnvelope q (inverseMellinEnvelope q z) = z := by
  by_cases hz0 : z = 0
  · simp [inverseMellinEnvelope, hz0, mellinEnvelope_zero q hq]
  have hfinite : z ^ (-q⁻¹) ≠ ∞ := by
    simp only [Ne, ENNReal.rpow_eq_top_iff]
    simp [hz0, (neg_neg_of_pos (inv_pos.mpr hq)).not_gt]
  rw [inverseMellinEnvelope, ite_eq_right hz0, mellinEnvelope_exp q _ hq ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hfinite, ← ENNReal.rpow_mul]
  have hprod : (-q⁻¹) * (-q) = 1 := by field_simp
  rw [hprod, ENNReal.rpow_one]

/-- A lower moment minorant pulls back to a lower Laplace-envelope minorant. -/
theorem inverseMellinEnvelope_le_exp (q m : ℝ) (hq : 0 < q) (hm : 0 ≤ m)
    (z : ℝ≥0∞) (hz : z ≤ mellinEnvelope q (ENNReal.ofReal (Real.exp (-q * m)))) :
    inverseMellinEnvelope q z ≤ ENNReal.ofReal (Real.exp (-q * m)) := by
  by_cases hz0 : z = 0
  · simp [inverseMellinEnvelope, hz0]
  have hfinite : z ^ (-q⁻¹) ≠ ∞ := by
    simp only [Ne, ENNReal.rpow_eq_top_iff]
    simp [hz0, (neg_neg_of_pos (inv_pos.mpr hq)).not_gt]
  rw [mellinEnvelope_exp q m hq hm] at hz
  have hp : (ENNReal.ofReal m ^ (-q)) ^ (-q⁻¹) ≤ z ^ (-q⁻¹) := by
    simp only [ENNReal.rpow_neg] at hz ⊢
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hz (inv_nonneg.mpr hq.le))
  have hprod : (-q) * (-q⁻¹) = 1 := by field_simp
  rw [← ENNReal.rpow_mul, hprod, ENNReal.rpow_one] at hp
  have hmle : m ≤ (z ^ (-q⁻¹)).toReal := by
    simpa only [ENNReal.toReal_ofReal hm] using ENNReal.toReal_mono hfinite hp
  rw [inverseMellinEnvelope, ite_eq_right hz0]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left hmle (neg_nonpos.mpr hq.le)

/-- Mellin integration of a finite lower Laplace envelope is justified by its own density. -/
theorem lintegral_mellinEnvelope_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (g : Ω → ℝ≥0∞)
    (hg : Measurable g) (hgfinite : ∀ ω, g ω ≠ ∞)
    (hInt : (∫⁻ ω, g ω ∂P) < ∞) (q : ℝ) (hq : 0 < q) :
    (∫⁻ ω, mellinEnvelope q (g ω) ∂P) = ENNReal.ofReal (1 / Real.Gamma q) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) *
        (∫⁻ ω, g ω ^ (t / q) ∂P) ∂volume := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let e : ℝ → ℝ := fun t => if 0 < t then t / q else 1
  let K : Ω → ℝ → ℝ≥0∞ := fun ω t => ENNReal.ofReal (t ^ (q - 1)) * g ω ^ e t
  have hepos (t : ℝ) : 0 < e t := by
    dsimp [e]
    split_ifs with ht
    · exact div_pos ht hq
    · exact zero_lt_one
  have hK : Measurable (Function.uncurry K) := by
    have he : Measurable e := by
      apply Measurable.ite measurableSet_Ioi (by fun_prop) measurable_const
    exact (by fun_prop : Measurable (fun p : Ω × ℝ => ENNReal.ofReal (p.2 ^ (q - 1)))).mul
      ((hg.comp measurable_fst).pow (he.comp measurable_snd))
  have hinner (ω : Ω) : (∫⁻ t, K ω t ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 1)) * g ω ^ (t / q) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    simp only [K, e, ite_eq_left ht0]
  have hswap := lintegral_swap_of_finite_density P ν g hg hgfinite hInt K hK
    (fun ω hω => by intro t; simp [K, hω, ENNReal.zero_rpow_of_pos (hepos t)])
  simp_rw [mellinEnvelope]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  simp_rw [← hinner]
  rw [hswap]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  simp only [K, e, ite_eq_left ht0]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- A Laplace kernel at parameter q is bounded by the negative q power, including a zero mass. -/
theorem exp_neg_mul_le_negative_power (q m : ℝ) (hq : 0 < q) (hm : 0 ≤ m) :
    ENNReal.ofReal (Real.exp (-q * m)) ≤ ENNReal.ofReal m ^ (-q) := by
  by_cases hm0 : m = 0
  · simp [hm0, ENNReal.zero_rpow_of_neg (neg_neg_of_pos hq)]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  rw [ENNReal.ofReal_rpow_of_pos hmpos]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.rpow_def_of_pos hmpos]
  apply Real.exp_le_exp.mpr
  have hlog : Real.log m ≤ m := (Real.log_le_sub_one_of_pos hmpos).trans (by linarith)
  nlinarith only [hlog, hq]

end DOZZ.Proofs
