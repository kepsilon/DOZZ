/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarTaylorRemainder
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Analysis.Complex.Norm
public import DOZZ.Hypergeom.Planar.RadialCriteria

/-! Uniform second-order tail bounds for the corrected planar Taylor numerator. -/

@[expose] public section

open Set
open Metric
open MeasureTheory

namespace DOZZ.Proofs

private theorem rpow_lipschitz_on {p : ℝ} (hp : p < 0) :
    LipschitzOnWith ((-p * (1/4 : ℝ) ^ (p - 1)).toNNReal)
      (fun x : ℝ => x ^ p) (Icc (1/4 : ℝ) (9/4)) := by
  apply (convex_Icc (1/4 : ℝ) (9/4)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro x hx
    exact (Real.hasDerivAt_rpow_const
      (Or.inl (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)))).differentiableAt
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
    have hpow : x ^ (p - 1) ≤ (1/4 : ℝ) ^ (p - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1 (by linarith only [hp])
    have hB : 0 ≤ (-p) * (1/4 : ℝ) ^ (p - 1) :=
      mul_nonneg (le_of_lt (neg_pos.mpr hp)) (Real.rpow_nonneg (by norm_num) _)
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm, Real.coe_toNNReal _ hB]
    change ‖deriv (fun y : ℝ => y ^ p) x‖ ≤ _
    rw [Real.deriv_rpow_const, Real.norm_eq_abs, abs_mul, abs_of_neg hp,
      abs_of_nonneg (Real.rpow_nonneg (le_of_lt hxpos) _)]
    exact mul_le_mul_of_nonneg_left hpow (by linarith only [hp])

private def segmentNormSq (u z : ℂ) (t : ℝ) : ℝ :=
  Complex.normSq (u - (t : ℂ) * z)

private theorem segmentNormSq_formula (u z : ℂ) (t : ℝ) :
    segmentNormSq u z t = ‖u‖ ^ 2 - 2 * t * (z * star u).re + t ^ 2 * ‖z‖ ^ 2 := by
  dsimp [segmentNormSq]
  rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hstar : star ((t : ℂ) * z) = (t : ℂ) * star z := by simp
  simp only [starRingEnd_apply, hstar]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring_nf

private theorem segmentNormSq_hasDerivAt (u z : ℂ) (t : ℝ) :
    HasDerivAt (segmentNormSq u z) (2 * t * ‖z‖ ^ 2 - 2 * (z * star u).re) t := by
  have hformula : (fun s : ℝ => segmentNormSq u z s) =
      fun s => ‖u‖ ^ 2 - 2 * s * (z * star u).re + s ^ 2 * ‖z‖ ^ 2 := by
    funext s
    exact segmentNormSq_formula u z s
  change HasDerivAt (fun s : ℝ => segmentNormSq u z s) _ _
  rw [hformula]
  convert (((hasDerivAt_const t (‖u‖ ^ 2)).sub
    ((hasDerivAt_id t).const_mul (2 * (z * star u).re))).add
    (((hasDerivAt_id t).pow 2).const_mul (‖z‖ ^ 2))) using 1
  · ext s
    simp
    ring_nf
  · simp
    ring_nf

private noncomputable def segmentRpow (k : ℝ) (u z : ℂ) (t : ℝ) : ℝ :=
  segmentNormSq u z t ^ (k / 2)

private theorem segmentRpow_hasDerivAt (k : ℝ) (u z : ℂ) (t : ℝ)
    (hq : 0 < segmentNormSq u z t) :
    HasDerivAt (segmentRpow k u z)
      (k * segmentNormSq u z t ^ (k / 2 - 1) *
        (t * ‖z‖ ^ 2 - (z * star u).re)) t := by
  unfold segmentRpow
  change HasDerivAt ((fun x : ℝ => x ^ (k / 2)) ∘ segmentNormSq u z) _ _
  have hqderiv := segmentNormSq_hasDerivAt u z t
  have hpow := (Real.hasDerivAt_rpow_const (x := segmentNormSq u z t)
    (p := k / 2) (Or.inl hq.ne')).comp t hqderiv
  convert hpow using 1
  all_goals ring_nf

private theorem unitSegment_normSq_bounds (w : ℂ) (hw : ‖w‖ ≤ 1 / 2)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 / 4 ≤ segmentNormSq 1 w t ∧ segmentNormSq 1 w t ≤ 9 / 4 := by
  have ht₀ : 0 ≤ t := ht.1
  have ht₁ : t ≤ 1 := ht.2
  have hs : 0 ≤ ‖w‖ := norm_nonneg w
  have hv : ‖(t : ℂ) * w‖ ≤ 1 / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht₀]
    exact (mul_le_of_le_one_left hs ht₁).trans hw
  have hlow : 1 / 2 ≤ ‖(1 : ℂ) - (t : ℂ) * w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * w)
    rw [norm_one] at h
    have h' : 1 / 2 ≤ 1 - ‖(t : ℂ) * w‖ := by linarith only [hv]
    exact h'.trans h
  have hupp : ‖(1 : ℂ) - (t : ℂ) * w‖ ≤ 3 / 2 := by
    have h := norm_sub_le (1 : ℂ) ((t : ℂ) * w)
    rw [norm_one] at h
    linarith only [h, hv]
  have hqnorm : segmentNormSq 1 w t = ‖(1 : ℂ) - (t : ℂ) * w‖ ^ 2 := by
    dsimp [segmentNormSq]
    rw [Complex.normSq_eq_norm_sq]
  rw [hqnorm]
  have hlo2 := pow_le_pow_left₀ (by norm_num) hlow 2
  have hup2 := pow_le_pow_left₀ (norm_nonneg _) hupp 2
  exact ⟨by linarith only [hlo2], by linarith only [hup2]⟩

private noncomputable def unitTaylorPath (k : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  segmentRpow k 1 w t - 1 + k * t * w.re

private theorem unitTaylorPath_hasDerivAt (k : ℝ) (w : ℂ) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hw : ‖w‖ ≤ 1 / 2) :
    HasDerivAt (unitTaylorPath k w)
      (k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
        (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)) t := by
  have hbounds := unitSegment_normSq_bounds w hw ht
  have hq : 0 < segmentNormSq 1 w t := lt_of_lt_of_le (by norm_num) hbounds.1
  have hp := segmentRpow_hasDerivAt k 1 w t hq
  have hlinear : HasDerivAt (fun s : ℝ => k * s * w.re) (k * w.re) t := by
    convert (hasDerivAt_id t).const_mul (k * w.re) using 1
    · ext s
      simp
      ring
    · ring
  unfold unitTaylorPath
  have h := (hp.sub_const 1).add hlinear
  convert h using 1
  · simp [star_one]
    ring_nf

private theorem unitTaylorPath_deriv_bound (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)‖ ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
  let p : ℝ := k / 2 - 1
  let L : ℝ := (-p) * (1 / 4 : ℝ) ^ (p - 1)
  have hp : p < 0 := by dsimp [p]; linarith only [hk₂]
  have hL : 0 ≤ L := by
    dsimp [L]
    exact mul_nonneg (by linarith only [hp]) (Real.rpow_nonneg (by norm_num) _)
  have hbounds := unitSegment_normSq_bounds w hw ht
  have hqmem : segmentNormSq 1 w t ∈ Icc (1 / 4 : ℝ) (9 / 4) := hbounds
  have hone : (1 : ℝ) ∈ Icc (1 / 4 : ℝ) (9 / 4) := by norm_num
  have hLpos : 0 ≤ (-p) * (1 / 4 : ℝ) ^ (p - 1) := by
    exact mul_nonneg (by linarith only [hp]) (Real.rpow_nonneg (by norm_num) _)
  have hpowdiff : |segmentNormSq 1 w t ^ p - 1| ≤ L * |segmentNormSq 1 w t - 1| := by
    have hLip := rpow_lipschitz_on hp
    have h := hLip.norm_sub_le hqmem hone
    rw [Real.coe_toNNReal _ hLpos] at h
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
    rw [Real.one_rpow] at h
    change |segmentNormSq 1 w t ^ p - 1| ≤ L * |segmentNormSq 1 w t - 1| at h
    exact h
  have ht₀ : 0 ≤ t := ht.1
  have ht₁ : t ≤ 1 := ht.2
  have hs : 0 ≤ ‖w‖ := norm_nonneg w
  have hRe : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  have hss : ‖w‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖w‖ := by
    linarith only [mul_le_mul_of_nonneg_left hw hs]
  have hts : t * ‖w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    exact mul_le_of_le_one_left (sq_nonneg ‖w‖) ht₁
  have htSq : t ^ 2 ≤ 1 := pow_le_one₀ ht₀ ht₁
  have htw : |t * w.re| ≤ ‖w‖ := by
    calc
      |t * w.re| = t * |w.re| := by rw [abs_mul, abs_of_nonneg ht₀]
      _ ≤ |w.re| := mul_le_of_le_one_left (abs_nonneg _) ht₁
      _ ≤ ‖w‖ := hRe
  have hqdiff : |segmentNormSq 1 w t - 1| ≤ (5 / 2 : ℝ) * ‖w‖ := by
    have hqformula : segmentNormSq 1 w t - 1 =
        -(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2 := by
      rw [segmentNormSq_formula]
      simp
      ring
    rw [hqformula]
    calc
      |-(2 * (t * w.re)) + t ^ 2 * ‖w‖ ^ 2| ≤
          |-(2 * (t * w.re))| + |t ^ 2 * ‖w‖ ^ 2| := abs_add_le _ _
      _ = 2 * |t * w.re| + t ^ 2 * ‖w‖ ^ 2 := by
        rw [abs_neg, abs_mul, abs_of_pos (by norm_num),
          abs_of_nonneg (mul_nonneg (sq_nonneg t) (sq_nonneg ‖w‖))]
      _ ≤ 2 * ‖w‖ + (1 / 2 : ℝ) * ‖w‖ := by
        linarith only [htw, hss, mul_le_of_le_one_left (sq_nonneg ‖w‖) htSq]
      _ = (5 / 2 : ℝ) * ‖w‖ := by ring
  have hlin : |t * ‖w‖ ^ 2 - w.re| ≤ (3 / 2 : ℝ) * ‖w‖ := by
    calc
      |t * ‖w‖ ^ 2 - w.re| ≤ |t * ‖w‖ ^ 2| + |w.re| := abs_sub _ _
      _ = t * ‖w‖ ^ 2 + |w.re| := by rw [abs_of_nonneg (mul_nonneg ht₀ (sq_nonneg _))]
      _ ≤ (1 / 2 : ℝ) * ‖w‖ + ‖w‖ := by linarith only [hts, hRe, hss]
      _ = (3 / 2 : ℝ) * ‖w‖ := by ring
  have hpowdiff' : |segmentNormSq 1 w t ^ p - 1| ≤ (5 / 2 : ℝ) * L * ‖w‖ := by
    calc
      _ ≤ L * |segmentNormSq 1 w t - 1| := hpowdiff
      _ ≤ L * ((5 / 2 : ℝ) * ‖w‖) := mul_le_mul_of_nonneg_left hqdiff hL
      _ = _ := by ring
  have hlast : |t * ‖w‖ ^ 2| ≤ ‖w‖ ^ 2 := by
    rw [abs_of_nonneg (mul_nonneg ht₀ (sq_nonneg _))]
    exact hts
  have hmain : |(segmentNormSq 1 w t ^ p - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| ≤
        ((15 / 4 : ℝ) * L + 1) * ‖w‖ ^ 2 := by
    calc
      _ ≤ |segmentNormSq 1 w t ^ p - 1| *
          |t * ‖w‖ ^ 2 - w.re| + |t * ‖w‖ ^ 2| := by
            calc
              _ ≤ |(segmentNormSq 1 w t ^ p - 1) * (t * ‖w‖ ^ 2 - w.re)| +
                  |t * ‖w‖ ^ 2| := abs_add_le _ _
              _ = _ := by rw [abs_mul]
      _ = |segmentNormSq 1 w t ^ p - 1| *
          |t * ‖w‖ ^ 2 - w.re| + |t * ‖w‖ ^ 2| := by rw [abs_mul]
      _ ≤ ((5 / 2 : ℝ) * L * ‖w‖) * ((3 / 2 : ℝ) * ‖w‖) + ‖w‖ ^ 2 := by
            apply add_le_add
            · exact mul_le_mul hpowdiff' hlin (abs_nonneg _) (by positivity)
            · exact hlast
      _ = _ := by ring
  rw [Real.norm_eq_abs]
  have hk_nonneg : 0 ≤ k := le_of_lt hk
  calc
    _ = k * |(segmentNormSq 1 w t ^ p - 1) *
        (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2| := by rw [abs_mul, abs_of_nonneg hk_nonneg]
    _ ≤ k * (((15 / 4 : ℝ) * L + 1) * ‖w‖ ^ 2) := mul_le_mul_of_nonneg_left hmain hk_nonneg
    _ = _ := by dsimp [L, p]; ring_nf

/-- The normalized corrected Taylor remainder is quadratically small on the half-unit disk. -/
theorem norm_unit_taylor_remainder_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (w : ℂ) (hw : ‖w‖ ≤ 1 / 2) :
    |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
  let D : ℝ → ℝ := fun t =>
    k * ((segmentNormSq 1 w t ^ (k / 2 - 1) - 1) *
      (t * ‖w‖ ^ 2 - w.re) + t * ‖w‖ ^ 2)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (unitTaylorPath k w) (D t) (Icc 0 1) t := by
    intro t ht
    have h := unitTaylorPath_hasDerivAt k w t ht hw
    exact h.hasDerivWithinAt
  have hbound : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖D t‖ ≤ (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2 := by
    intro t ht
    have h := unitTaylorPath_deriv_bound k hk hk₂ w hw (Ico_subset_Icc_self ht)
    simpa [D] using h
  have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound
    (1 : ℝ) (right_mem_Icc.2 (by norm_num : (0 : ℝ) ≤ 1))
  have hzero : unitTaylorPath k w 0 = 0 := by
    simp [unitTaylorPath, segmentRpow, segmentNormSq]
  have hone : unitTaylorPath k w 1 = ‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re := by
    simp [unitTaylorPath, segmentRpow, segmentNormSq, Complex.normSq_eq_norm_sq]
    have htwo : ‖(1 : ℂ) - w‖ ^ ((2 : ℕ) : ℝ) = ‖(1 : ℂ) - w‖ ^ 2 :=
      Real.rpow_natCast _ 2
    calc
      (‖(1 : ℂ) - w‖ ^ 2) ^ (k / 2) =
          (‖(1 : ℂ) - w‖ ^ ((2 : ℕ) : ℝ)) ^ (k / 2) := by rw [← htwo]
      _ = ‖(1 : ℂ) - w‖ ^ ((2 : ℝ) * (k / 2)) :=
        (Real.rpow_mul (norm_nonneg _) 2 (k / 2)).symm
      _ = _ := by congr 1; ring_nf
  simpa [hzero, hone, Real.norm_eq_abs] using hmean

/-- The corrected numerator has a pointwise quadratic tail bound, with no angular averaging. -/
theorem abs_planarTaylorNumerator_le (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (z u : ℂ) (hu : u ≠ 0) (hlarge : 2 * ‖z‖ ≤ ‖u‖) :
    |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
        ‖u‖ ^ k * ‖z / u‖ ^ 2 := by
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let w : ℂ := z / u
  have hw : ‖w‖ ≤ 1 / 2 := by
    dsimp [w]
    rw [norm_div]
    apply (div_le_iff₀ hr).2
    linarith only [hlarge]
  have hfactor : ‖u - z‖ ^ k = ‖u‖ ^ k * ‖(1 : ℂ) - w‖ ^ k := by
    have heq : u - z = u * ((1 : ℂ) - w) := by
      dsimp [w]
      field_simp [hu]
    rw [heq, norm_mul, Real.mul_rpow (norm_nonneg u) (norm_nonneg (1 - w))]
  have hstar : star z / star u = star w := by
    dsimp [w]
    simp
  have hlinear : (z / u + star z / star u).re = 2 * w.re := by
    rw [hstar]
    simp [Complex.add_re]
    change (z / u).re + (z / u).re = 2 * (z / u).re
    ring
  have hnum : ‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re =
      ‖u‖ ^ k * (‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re) := by
    rw [hfactor, hlinear]
    ring
  rw [hnum]
  have hunit := norm_unit_taylor_remainder_le k hk hk₂ w hw
  have hconst : 0 ≤ k * (1 + (15 / 4) *
      ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) := by
    have hfirst : 0 ≤ 1 - k / 2 := by linarith only [hk₂]
    positivity
  have hnorm : 0 ≤ ‖u‖ ^ k := Real.rpow_nonneg (norm_nonneg u) k
  calc
    _ = ‖u‖ ^ k * |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| := by
      rw [abs_mul, abs_of_nonneg hnorm]
    _ ≤ ‖u‖ ^ k * ((k * (1 + (15 / 4) *
          ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) * ‖w‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hunit hnorm
    _ = _ := by dsimp [w]; ring

private theorem rpow_tail_normalize (r s k β : ℝ) (hr : 0 < r) :
    r ^ k * (s / r) ^ 2 / r ^ β = s ^ 2 * r ^ (k - 2 - β) := by
  have hpow1 : r ^ k / r ^ 2 = r ^ (k - 2) := by
    simpa using (Real.rpow_sub hr k (2 : ℝ)).symm
  have hpow2 : r ^ (k - 2) / r ^ β = r ^ (k - 2 - β) :=
    (Real.rpow_sub hr (k - 2) β).symm
  calc
    _ = r ^ k * (s ^ 2 / r ^ 2) / r ^ β := by rw [div_pow]
    _ = s ^ 2 * ((r ^ k / r ^ 2) / r ^ β) := by ring
    _ = _ := by rw [hpow1, hpow2]

/-- The full Taylor kernel inherits the same pointwise tail comparison. -/
theorem abs_planarTaylorRemainder_le (k β : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (z u : ℂ) (hu : u ≠ 0) (hlarge : 2 * ‖z‖ ≤ ‖u‖) :
    |DOZZ.planarTaylorRemainder k β z u| ≤
      (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
        ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnum := abs_planarTaylorNumerator_le k hk hk₂ z u hu hlarge
  change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos hr β)]
  have htail := div_le_div_of_nonneg_right hnum (Real.rpow_nonneg hr.le β)
  calc
    _ ≤ (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
        ‖u‖ ^ k * ‖z / u‖ ^ 2 / ‖u‖ ^ β := by simpa using htail
    _ = (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
        ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
      rw [norm_div]
      have hpower : ‖u‖ ^ k * (‖z‖ / ‖u‖) ^ 2 / ‖u‖ ^ β =
          ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := by
        exact rpow_tail_normalize ‖u‖ ‖z‖ k β hr
      calc
        _ = (k * (1 + (15 / 4) * ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))) *
            (‖u‖ ^ k * (‖z‖ / ‖u‖) ^ 2 / ‖u‖ ^ β) := by ring
        _ = _ := by rw [hpower]; ring

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

private theorem measurable_planarTaylorRemainder (k β : ℝ) (z : ℂ) :
    Measurable (DOZZ.planarTaylorRemainder k β z) := by
  change Measurable (fun u : ℂ =>
    (‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re) / ‖u‖ ^ β)
  apply Measurable.div
  · have hshift : Measurable (fun u : ℂ => ‖u - z‖ ^ k) :=
      measurable_nonneg_rpow (by fun_prop) (fun u => norm_nonneg (u - z)) k
    exact (hshift.sub (measurable_complex_norm_rpow k)).add
      ((measurable_const.mul (measurable_complex_norm_rpow k)).mul (by fun_prop))
  · exact measurable_complex_norm_rpow β

theorem integrableOn_planarTaylorRemainder_tail (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (DOZZ.planarTaylorRemainder k β z)
      (ball (0 : ℂ) (2 * ‖z‖))ᶜ volume := by
  let p : ℝ := k - 2 - β
  let C : ℝ := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  let B : ℝ := C * ‖z‖ ^ 2
  have hr : 0 < 2 * ‖z‖ := by positivity
  have hp : p < -2 := by dsimp [p]; linarith only [hβ]
  have hB : 0 ≤ B := by
    dsimp [B, C]
    have hfirst : 0 ≤ 1 - k / 2 := by linarith only [hβ, hβ₂]
    positivity
  have hrad : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (ball (0 : ℂ) (2 * ‖z‖))ᶜ volume :=
    (integrableOn_norm_rpow_ball_compl_iff p (2 * ‖z‖) hr).2 hp
  have hmajor : IntegrableOn (fun u : ℂ => B * ‖u‖ ^ p)
      (ball (0 : ℂ) (2 * ‖z‖))ᶜ volume := hrad.const_mul B
  have hk₂ : k < 2 := lt_trans hβ hβ₂
  change Integrable (DOZZ.planarTaylorRemainder k β z)
      (volume.restrict (ball (0 : ℂ) (2 * ‖z‖))ᶜ)
  apply hmajor.mono' (measurable_planarTaylorRemainder k β z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.compl)] with u hu
  have hlarge : 2 * ‖z‖ ≤ ‖u‖ := by
    by_contra h
    have : ‖u‖ < 2 * ‖z‖ := lt_of_not_ge h
    exact hu (by simpa [Metric.mem_ball, dist_zero_right] using this)
  have hu : u ≠ 0 := by
    intro hu0
    subst u
    have hlarge0 : 2 * ‖z‖ ≤ 0 := by simpa using hlarge
    linarith only [hlarge0, hr]
  have hpoint := abs_planarTaylorRemainder_le k β hk hk₂ z u hu hlarge
  rw [Real.norm_eq_abs]
  change |DOZZ.planarTaylorRemainder k β z u| ≤ B * ‖u‖ ^ p
  calc
    _ ≤ C * ‖z‖ ^ 2 * ‖u‖ ^ p := by simpa [C, p] using hpoint
    _ = B * ‖u‖ ^ p := by dsimp [B]

private theorem abs_planarTaylorNumerator_local_le (k : ℝ) (hk : 0 < k)
    (z u : ℂ) (hu : u ≠ 0) (hball : ‖u‖ < 2 * ‖z‖) :
    |‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re| ≤
      (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) := by
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ha : 0 ≤ ‖z‖ := norm_nonneg z
  have hrpow : 0 ≤ ‖u‖ ^ k := Real.rpow_nonneg hr.le k
  have hshift : ‖u - z‖ ^ k ≤ (3 * ‖z‖) ^ k := by
    have hnorm : ‖u - z‖ ≤ 3 * ‖z‖ := by
      calc
        ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 3 * ‖z‖ := by linarith only [hball]
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm (le_of_lt hk)
  let w : ℂ := z / u
  have hstar : star z / star u = star w := by
    dsimp [w]
    simp
  have hlin : |(z / u + star z / star u).re| ≤ 2 * (‖z‖ / ‖u‖) := by
    rw [hstar]
    calc
      |(w + star w).re| ≤ ‖w + star w‖ := Complex.abs_re_le_norm _
      _ ≤ ‖w‖ + ‖star w‖ := norm_add_le _ _
      _ = 2 * ‖w‖ := by simp [two_mul]
      _ = 2 * (‖z‖ / ‖u‖) := by rw [norm_div]
  have hpow : ‖u‖ ^ (k - 1) = ‖u‖ ^ k / ‖u‖ := by
    have h := Real.rpow_sub hr k 1
    simpa using h
  have hscale : ‖u‖ ^ k * (‖z‖ / ‖u‖) = ‖z‖ * ‖u‖ ^ (k - 1) := by
    rw [hpow]
    field_simp [hr.ne']
  have hcounter : |(k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re| ≤ k * ‖z‖ * ‖u‖ ^ (k - 1) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (k / 2) * ‖u‖ ^ k)]
    calc
      (k / 2) * ‖u‖ ^ k * |(z / u + star z / star u).re|
          ≤ (k / 2) * ‖u‖ ^ k * (2 * (‖z‖ / ‖u‖)) := by
              exact mul_le_mul_of_nonneg_left hlin (by positivity)
      _ = k * (‖u‖ ^ k * (‖z‖ / ‖u‖)) := by ring
      _ = k * ‖z‖ * ‖u‖ ^ (k - 1) := by rw [hscale]; ring
  have hshift' : |‖u - z‖ ^ k| ≤ (3 * ‖z‖) ^ k := by
    rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) k)]
    exact hshift
  have hrad' : |‖u‖ ^ k| = ‖u‖ ^ k := abs_of_nonneg hrpow
  calc
    _ ≤ |‖u - z‖ ^ k - ‖u‖ ^ k| +
        |(k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re| := abs_add_le _ _
    _ ≤ |‖u - z‖ ^ k| + |‖u‖ ^ k| +
        k * ‖z‖ * ‖u‖ ^ (k - 1) := by
          exact add_le_add (abs_sub _ _) hcounter
    _ ≤ (3 * ‖z‖) ^ k + ‖u‖ ^ k + k * ‖z‖ * ‖u‖ ^ (k - 1) := by
          exact add_le_add (add_le_add hshift' (le_of_eq hrad')) le_rfl

private theorem abs_planarTaylorRemainder_local_le (k β : ℝ)
    (hk : 0 < k) (hβ : k < β)
    (z u : ℂ) (hball : ‖u‖ < 2 * ‖z‖) :
    |DOZZ.planarTaylorRemainder k β z u| ≤
      (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) +
        ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
  by_cases hu : u = 0
  · subst u
    have hβpos : 0 < β := lt_trans hk hβ
    simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk,
      ne_of_gt hβpos, ne_of_lt (by linarith only [hβ] : k - β < 0),
      ne_of_lt (by linarith only [hβ] : k - 1 - β < 0)]
  · have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hnum := abs_planarTaylorNumerator_local_le k hk z u hu hball
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos hr β
    have hpow₀ : ‖u‖ ^ (-β) = 1 / ‖u‖ ^ β := by
      calc
        ‖u‖ ^ (-β) = ‖u‖ ^ (0 - β) := by congr 1; ring
        _ = ‖u‖ ^ (0 : ℝ) / ‖u‖ ^ β := Real.rpow_sub hr 0 β
        _ = 1 / ‖u‖ ^ β := by rw [Real.rpow_zero]
    have hpow₁ : ‖u‖ ^ k / ‖u‖ ^ β = ‖u‖ ^ (k - β) :=
      (Real.rpow_sub hr k β).symm
    have hpow₂ : ‖u‖ ^ (k - 1) / ‖u‖ ^ β =
        ‖u‖ ^ (k - 1 - β) := (Real.rpow_sub hr (k - 1) β).symm
    change |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re) / ‖u‖ ^ β| ≤ _
    rw [abs_div, abs_of_pos hden]
    calc
      _ ≤ ((3 * ‖z‖) ^ k + ‖u‖ ^ k +
          k * ‖z‖ * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β :=
            div_le_div_of_nonneg_right hnum hden.le
      _ = (3 * ‖z‖) ^ k * (1 / ‖u‖ ^ β) +
          ‖u‖ ^ k / ‖u‖ ^ β +
          k * ‖z‖ * (‖u‖ ^ (k - 1) / ‖u‖ ^ β) := by ring
      _ = (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) +
          ‖u‖ ^ (k - β) + k * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
            rw [← hpow₀, hpow₁, hpow₂]

theorem integrableOn_planarTaylorRemainder_ball (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1)
    (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (DOZZ.planarTaylorRemainder k β z)
      (ball (0 : ℂ) (2 * ‖z‖)) volume := by
  let R : ℝ := 2 * ‖z‖
  let A : ℝ := (3 * ‖z‖) ^ k
  let p₀ : ℝ := -β
  let p₁ : ℝ := k - β
  let p₂ : ℝ := k - 1 - β
  have hR : 0 < R := by dsimp [R]; positivity
  have hp₀ : -2 < p₀ := by dsimp [p₀]; linarith only [hβ₂]
  have hp₁ : -2 < p₁ := by dsimp [p₁]; linarith only [hβ₂, hk]
  have hp₂ : -2 < p₂ := by dsimp [p₂]; linarith only [hβlin]
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ k * ‖z‖ := mul_nonneg (le_of_lt hk) (norm_nonneg z)
  have h₀ : IntegrableOn (fun u : ℂ => A * ‖u‖ ^ p₀) (ball 0 R) volume :=
    ((integrableOn_norm_rpow_ball_iff p₀ R hR).2 hp₀).const_mul A
  have h₁ : IntegrableOn (fun u : ℂ => ‖u‖ ^ p₁) (ball 0 R) volume :=
    (integrableOn_norm_rpow_ball_iff p₁ R hR).2 hp₁
  have h₂ : IntegrableOn (fun u : ℂ => (k * ‖z‖) * ‖u‖ ^ p₂)
      (ball 0 R) volume :=
    ((integrableOn_norm_rpow_ball_iff p₂ R hR).2 hp₂).const_mul (k * ‖z‖)
  have hmajor : IntegrableOn (fun u : ℂ =>
      A * ‖u‖ ^ p₀ + ‖u‖ ^ p₁ + (k * ‖z‖) * ‖u‖ ^ p₂)
      (ball 0 R) volume := (h₀.add h₁).add h₂
  change Integrable (DOZZ.planarTaylorRemainder k β z)
    (volume.restrict (ball 0 R))
  apply hmajor.mono' (measurable_planarTaylorRemainder k β z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with u hu
  rw [Real.norm_eq_abs]
  have hball : ‖u‖ < 2 * ‖z‖ := by
    dsimp [R] at hu
    simpa [Metric.mem_ball, dist_zero_right] using hu
  have hpoint := abs_planarTaylorRemainder_local_le k β hk hβ z u hball
  change |DOZZ.planarTaylorRemainder k β z u| ≤
    A * ‖u‖ ^ p₀ + ‖u‖ ^ p₁ + (k * ‖z‖) * ‖u‖ ^ p₂
  simpa [A, p₀, p₁, p₂, mul_assoc, mul_left_comm, mul_comm] using hpoint

/-- The corrected Taylor kernel is absolutely integrable in the convergence window of
`DOZZ.planar_taylor_integral`. -/
theorem integrable_planarTaylorRemainder (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    ∀ z : ℂ, Integrable (DOZZ.planarTaylorRemainder k β z) volume := by
  intro z
  by_cases hz : z = 0
  · subst z
    have hzero : DOZZ.planarTaylorRemainder k β 0 = fun _ : ℂ => (0 : ℝ) := by
      funext u
      simp [DOZZ.planarTaylorRemainder]
    rw [hzero]
    exact integrable_zero ℂ ℝ volume
  · have hball := integrableOn_planarTaylorRemainder_ball k β hk hβ hβ₂ hβlin z hz
    have htail := integrableOn_planarTaylorRemainder_tail k β hk hβ hβ₂ z hz
    rw [← integrableOn_univ, ← Set.union_compl_self (ball (0 : ℂ) (2 * ‖z‖)),
      integrableOn_union]
    exact ⟨hball, htail⟩

end DOZZ.Proofs
