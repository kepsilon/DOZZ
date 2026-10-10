/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftLimitB

/-! # Pathwise bounds for the near-root parts of the derivative masses

For a measure without an atom at the root `z`, the near-root parts of the first and second
derivative masses are bounded by integrals of `|x - z|^{2a-1}` and `|x - z|^{2a-2}` against the
near weight, and the square of the first is bounded, by Cauchy–Schwarz, by the product of the
integrals of `|x - z|^{2a}` and `|x - z|^{2a-2}`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin


/-- The near part of the first derivative mass, bounded pathwise. -/
theorem norm_bpzSoftMassDeriv_le_near {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 1)) m) :
    ‖bpzSoftMassDeriv a ε w m z‖ ≤ 2 * a * ∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m := by
  unfold bpzSoftMassDeriv
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
  have hae : ∀ᵐ x ∂m, x ≠ z := by rw [ae_iff]; simpa using hz
  filter_upwards [hae] with x hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
  calc w x * ‖bpzSoftDeriv a ε x z‖ ≤ w x * (2 * a * ‖x - z‖ ^ (2 * a - 1)) :=
        mul_le_mul_of_nonneg_left (norm_bpzSoftDeriv_le_uniform ha ha1 hx) (hw0 x)
    _ = 2 * a * (w x * ‖x - z‖ ^ (2 * a - 1)) := by ring

/-- The near part of the second derivative mass, bounded pathwise. -/
theorem norm_bpzSoftMassDeriv2_le_near {a ε : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 2)) m) :
    ‖bpzSoftMassDeriv2 a ε w m z‖ ≤
      (4 * a * (1 - a) + 2 * a) * ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := by
  unfold bpzSoftMassDeriv2
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul _) ?_
  have hae : ∀ᵐ x ∂m, x ≠ z := by rw [ae_iff]; simpa using hz
  filter_upwards [hae] with x hx
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
  calc w x * ‖bpzSoftDeriv2 a ε x z‖ ≤ w x * ((4 * a * (1 - a) + 2 * a) * ‖x - z‖ ^ (2 * a - 2)) :=
        mul_le_mul_of_nonneg_left (norm_bpzSoftDeriv2_le_uniform ha ha1 hx) (hw0 x)
    _ = (4 * a * (1 - a) + 2 * a) * (w x * ‖x - z‖ ^ (2 * a - 2)) := by ring

/-- Cauchy–Schwarz for the near weight: `(∫ w t^{2a-1})² ≤ (∫ w t^{2a})(∫ w t^{2a-2})`. -/
theorem bpz_near_cauchySchwarz {a : ℝ} {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (h0 : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a)) m)
    (h2 : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 2)) m) :
    (∫ x, w x * ‖x - z‖ ^ (2 * a - 1) ∂m) ^ 2 ≤
      (∫ x, w x * ‖x - z‖ ^ (2 * a) ∂m) * ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := by
  set f : ℂ → ℝ := fun x => Real.sqrt (w x * ‖x - z‖ ^ (2 * a)) with hf
  set g : ℂ → ℝ := fun x => Real.sqrt (w x * ‖x - z‖ ^ (2 * a - 2)) with hg
  have hae : ∀ᵐ x ∂m, x ≠ z := by rw [ae_iff]; simpa using hz
  have hfg : (fun x => w x * ‖x - z‖ ^ (2 * a - 1)) =ᵐ[m] fun x => f x * g x := by
    filter_upwards [hae] with x hx
    have hxz : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
    simp only [hf, hg]
    rw [← Real.sqrt_mul (mul_nonneg (hw0 x) (Real.rpow_nonneg hxz.le _))]
    rw [show w x * ‖x - z‖ ^ (2 * a) * (w x * ‖x - z‖ ^ (2 * a - 2)) =
      (w x * ‖x - z‖ ^ (2 * a - 1)) ^ 2 by
        rw [mul_pow, ← Real.rpow_natCast (‖x - z‖ ^ (2 * a - 1)), ← Real.rpow_mul hxz.le]
        rw [show (2 * a - 1) * ((2 : ℕ) : ℝ) = 2 * a + (2 * a - 2) by push_cast; ring,
          Real.rpow_add hxz]
        ring]
    rw [Real.sqrt_sq (mul_nonneg (hw0 x) (Real.rpow_nonneg hxz.le _))]
  have hf2 : ∀ x, f x ^ (2 : ℝ) = w x * ‖x - z‖ ^ (2 * a) := fun x => by
    simp only [hf]
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw0 x) (Real.rpow_nonneg (norm_nonneg _) _))]
  have hg2 : ∀ x, g x ^ (2 : ℝ) = w x * ‖x - z‖ ^ (2 * a - 2) := fun x => by
    simp only [hg]
    rw [Real.rpow_two, Real.sq_sqrt (mul_nonneg (hw0 x) (Real.rpow_nonneg (norm_nonneg _) _))]
  have hfm : Measurable f := (hw.mul ((measurable_id.sub measurable_const).norm.pow_const _)).sqrt
  have hgm : Measurable g := (hw.mul ((measurable_id.sub measurable_const).norm.pow_const _)).sqrt
  have hfL : MemLp f (ENNReal.ofReal 2) m := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr ?_
    have : (fun x => f x ^ 2) = fun x => w x * ‖x - z‖ ^ (2 * a) := by
      funext x; rw [← hf2 x, Real.rpow_two]
    rw [this]; exact h0
  have hgL : MemLp g (ENNReal.ofReal 2) m := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
    have : (fun x => g x ^ 2) = fun x => w x * ‖x - z‖ ^ (2 * a - 2) := by
      funext x; rw [← hg2 x, Real.rpow_two]
    rw [this]; exact h2
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (f := f) (g := g) Real.HolderConjugate.two_two
    (Eventually.of_forall fun x => Real.sqrt_nonneg _)
    (Eventually.of_forall fun x => Real.sqrt_nonneg _) hfL hgL
  simp only [hf2, hg2] at hH
  rw [integral_congr_ae hfg]
  have hA : 0 ≤ ∫ x, w x * ‖x - z‖ ^ (2 * a) ∂m :=
    integral_nonneg fun x => mul_nonneg (hw0 x) (Real.rpow_nonneg (norm_nonneg _) _)
  have hB : 0 ≤ ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m :=
    integral_nonneg fun x => mul_nonneg (hw0 x) (Real.rpow_nonneg (norm_nonneg _) _)
  have hfg0 : 0 ≤ ∫ x, f x * g x ∂m :=
    integral_nonneg fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc (∫ x, f x * g x ∂m) ^ 2
      ≤ ((∫ x, w x * ‖x - z‖ ^ (2 * a) ∂m) ^ (1 / 2 : ℝ) *
          (∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫ x, w x * ‖x - z‖ ^ (2 * a) ∂m) * ∫ x, w x * ‖x - z‖ ^ (2 * a - 2) ∂m := by
        rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (_ ^ (1 / 2 : ℝ)),
          ← Real.rpow_mul hA, ← Real.rpow_mul hB]
        norm_num

end DOZZ.Proofs
