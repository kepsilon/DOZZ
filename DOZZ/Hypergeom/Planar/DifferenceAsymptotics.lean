/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
public import DOZZ.Hypergeom.Planar.TaylorTail
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Complex.Isometry

/-! First-order lower estimate for the planar difference numerator on a sector. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

private noncomputable def quarterTurnCircle : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

private noncomputable def quarterTurn : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation quarterTurnCircle

private theorem quarterTurn_measurePreserving :
    MeasurePreserving quarterTurn volume volume :=
  LinearIsometryEquiv.measurePreserving quarterTurn

private theorem norm_rpow_measurable (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) := by
  have hrepr : (fun u : ℂ => ‖u‖ ^ p) =
      fun u => if ‖u‖ = 0 then 0 ^ p else Real.exp (p * Real.log ‖u‖) := by
    funext u
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    · rw [ite_eq_right hu,
        Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)
  · exact measurable_const
  · fun_prop

private def differenceTailSector (z : ℂ) (R : ℝ) : Set ℂ :=
  {u | R ≤ ‖u‖ ∧ ‖z / u‖ / 2 ≤ |(z / u).re|}

private theorem differenceTailSector_measurable (z : ℂ) (R : ℝ) :
    MeasurableSet (differenceTailSector z R) := by
  have hnorm : Measurable (fun u : ℂ => ‖u‖) := by fun_prop
  have hqre : Measurable (fun u : ℂ => |(z / u).re|) := by fun_prop
  exact (measurableSet_le measurable_const hnorm).inter
    (measurableSet_le (by fun_prop) hqre)

private theorem norm_sq_eq_re_sq_add_im_sq (w : ℂ) :
    ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq]
  ring

private theorem sector_or_quarterTurn_sector (z : ℂ) (R : ℝ) {u : ℂ}
    (hu : u ≠ 0) (hR : R ≤ ‖u‖) :
    u ∈ differenceTailSector z R ∨
      u ∈ quarterTurn '' differenceTailSector z R := by
  let w : ℂ := z / u
  by_cases hsector : ‖w‖ / 2 ≤ |w.re|
  · exact Or.inl ⟨hR, by simpa [w] using hsector⟩
  · have hRe : |w.re| < ‖w‖ / 2 := lt_of_not_ge hsector
    have hIm : ‖w‖ / 2 ≤ |w.im| := by
      by_contra h
      have hIm' : |w.im| < ‖w‖ / 2 := lt_of_not_ge h
      have hsqRe : |w.re| ^ 2 < (‖w‖ / 2) ^ 2 :=
        (sq_lt_sq₀ (abs_nonneg _) (by positivity)).2 hRe
      have hsqIm : |w.im| ^ 2 < (‖w‖ / 2) ^ 2 :=
        (sq_lt_sq₀ (abs_nonneg _) (by positivity)).2 hIm'
      have habsRe : |w.re| ^ 2 = w.re ^ 2 := sq_abs _
      have habsIm : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
      rw [habsRe] at hsqRe
      rw [habsIm] at hsqIm
      have hnormSq := norm_sq_eq_re_sq_add_im_sq w
      linarith only [hsqRe, hsqIm, hnormSq, sq_nonneg ‖w‖]
    have hturn : quarterTurn.symm u = -Complex.I * u := by
      change (rotation quarterTurnCircle).symm u = _
      rw [rotation_symm, rotation_apply]
      rw [Circle.coe_inv_eq_conj]
      simp [quarterTurnCircle, Complex.conj_I]
    have hmem : quarterTurn.symm u ∈ differenceTailSector z R := by
      constructor
      · rw [show quarterTurn.symm u = -Complex.I * u from hturn]
        simp [norm_neg]
        exact hR
      · rw [show quarterTurn.symm u = -Complex.I * u from hturn]
        have hquot : z / (-Complex.I * u) = Complex.I * w := by
          dsimp [w]
          field_simp [hu, Complex.I_ne_zero]
          ring_nf
          simp [Complex.I_sq]
        rw [hquot]
        simp [abs_neg]
        exact hIm
    exact Or.inr ⟨quarterTurn.symm u, hmem, by simp⟩

theorem abs_norm_sub_rpow_lower_of_sector (k : ℝ) (hk : 0 < k) (hk₂ : k < 2)
    (z u : ℂ) (hu : u ≠ 0)
    (hw₁ : ‖z / u‖ ≤ 1 / 2)
    (hw₂ : ‖z / u‖ ≤ k /
      (4 * (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))))))
    (hsector : ‖z / u‖ / 2 ≤ |(z / u).re|) :
    (k / 4) * ‖z‖ * ‖u‖ ^ (k - 1) ≤
      |‖u - z‖ ^ k - ‖u‖ ^ k| := by
  let w : ℂ := z / u
  let T : ℝ := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hT : 0 < T := by
    dsimp [T]
    have hfactor : 0 < 1 - k / 2 := by linarith only [hk₂]
    positivity
  have hwNorm : ‖w‖ ≤ 1 / 2 := by simpa [w] using hw₁
  have hwSmall : ‖w‖ ≤ k / (4 * T) := by
    simpa [w, T, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hw₂
  have hTaylor := norm_unit_taylor_remainder_le k hk hk₂ w hwNorm
  have hsector' : ‖w‖ / 2 ≤ |w.re| := by simpa [w] using hsector
  have hlin : k / 2 * ‖w‖ ≤ |k * w.re| := by
    rw [abs_mul, abs_of_pos hk]
    calc
      k / 2 * ‖w‖ = k * (‖w‖ / 2) := by ring
      _ ≤ k * |w.re| := mul_le_mul_of_nonneg_left hsector' hk.le
  have hquad : T * ‖w‖ ^ 2 ≤ k / 4 * ‖w‖ := by
    have hnormSq : ‖w‖ ^ 2 ≤ k / (4 * T) * ‖w‖ := by
      simpa [pow_two] using mul_le_mul_of_nonneg_right hwSmall (norm_nonneg w)
    calc
      _ ≤ T * (k / (4 * T) * ‖w‖) := mul_le_mul_of_nonneg_left hnormSq hT.le
      _ = _ := by field_simp [ne_of_gt hT]
  have hfirst : k / 4 * ‖w‖ ≤ |‖1 - w‖ ^ k - 1| := by
    have htri : |k * w.re| ≤ |‖1 - w‖ ^ k - 1| +
        |‖1 - w‖ ^ k - 1 + k * w.re| := by
      calc
        |k * w.re| = |(‖1 - w‖ ^ k - 1 + k * w.re) -
            (‖1 - w‖ ^ k - 1)| := by congr 1; ring
        _ ≤ |‖1 - w‖ ^ k - 1 + k * w.re| + |‖1 - w‖ ^ k - 1| := abs_sub _ _
        _ = _ := by ring
    have hE : |‖1 - w‖ ^ k - 1 + k * w.re| ≤ k / 4 * ‖w‖ :=
      hTaylor.trans hquad
    have hsum : |‖1 - w‖ ^ k - 1| +
        |‖1 - w‖ ^ k - 1 + k * w.re| ≤
          |‖1 - w‖ ^ k - 1| + k / 4 * ‖w‖ := add_le_add_right hE _
    linarith only [hlin, htri, hsum]
  have hfactor : ‖u - z‖ ^ k = ‖u‖ ^ k * ‖1 - w‖ ^ k := by
    have heq : u - z = u * (1 - w) := by
      dsimp [w]
      field_simp [hu]
    rw [heq, norm_mul, Real.mul_rpow (norm_nonneg u) (norm_nonneg (1 - w))]
  have hnormPower : 0 ≤ ‖u‖ ^ k := Real.rpow_nonneg (norm_nonneg u) k
  have hnum : |‖u - z‖ ^ k - ‖u‖ ^ k| =
      ‖u‖ ^ k * |‖1 - w‖ ^ k - 1| := by
    rw [hfactor]
    rw [show ‖u‖ ^ k * ‖1 - w‖ ^ k - ‖u‖ ^ k =
      ‖u‖ ^ k * (‖1 - w‖ ^ k - 1) by ring, abs_mul, abs_of_nonneg hnormPower]
  have hwScale : ‖u‖ ^ k * ‖w‖ = ‖z‖ * ‖u‖ ^ (k - 1) := by
    have hpow : ‖u‖ ^ (k - 1) = ‖u‖ ^ k / ‖u‖ := by
      simpa [Real.rpow_one] using (Real.rpow_sub huNorm k 1)
    rw [hpow]
    dsimp [w]
    rw [norm_div]
    field_simp [huNorm.ne']
  rw [hnum]
  calc
    (k / 4) * ‖z‖ * ‖u‖ ^ (k - 1) =
        (k / 4) * (‖u‖ ^ k * ‖w‖) := by rw [hwScale]; ring
    _ ≤ ‖u‖ ^ k * |‖1 - w‖ ^ k - 1| := by
      calc
        (k / 4) * (‖u‖ ^ k * ‖w‖) = ‖u‖ ^ k * (k / 4 * ‖w‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hfirst hnormPower

theorem abs_planarDifferenceKernel_lower_of_sector (k β : ℝ)
    (hk : 0 < k) (hk₂ : k < 2) (z u : ℂ) (hu : u ≠ 0)
    (hw₁ : ‖z / u‖ ≤ 1 / 2)
    (hw₂ : ‖z / u‖ ≤ k /
      (4 * (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))))))
    (hsector : ‖z / u‖ / 2 ≤ |(z / u).re|) :
    (k / 4) * ‖z‖ * ‖u‖ ^ (k - 1 - β) ≤
      |DOZZ.planarDifferenceKernel k β z u| := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnum := abs_norm_sub_rpow_lower_of_sector k hk hk₂ z u hu hw₁ hw₂ hsector
  have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos huNorm β
  have hpow : ‖u‖ ^ (k - 1 - β) = ‖u‖ ^ (k - 1) / ‖u‖ ^ β :=
    Real.rpow_sub huNorm (k - 1) β
  change (k / 4) * ‖z‖ * ‖u‖ ^ (k - 1 - β) ≤
    |(‖u - z‖ ^ k - ‖u‖ ^ k) / ‖u‖ ^ β|
  rw [abs_div, abs_of_pos hden]
  calc
    (k / 4) * ‖z‖ * ‖u‖ ^ (k - 1 - β) =
        ((k / 4) * ‖z‖ * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β := by rw [hpow]; ring
    _ ≤ |‖u - z‖ ^ k - ‖u‖ ^ k| / ‖u‖ ^ β :=
      div_le_div_of_nonneg_right hnum hden.le

theorem abs_norm_sub_rpow_lower_of_sector_ge_one (k : ℝ) (hk : 1 ≤ k)
    (z u : ℂ) (hu : u ≠ 0) (hw : ‖z / u‖ ≤ 1 / 2)
    (hsector : ‖z / u‖ / 2 ≤ |(z / u).re|) :
    (1 / 5) * ‖z‖ * ‖u‖ ^ (k - 1) ≤
      |‖u - z‖ ^ k - ‖u‖ ^ k| := by
  let w : ℂ := z / u
  let x : ℝ := ‖(1 : ℂ) - w‖
  let r : ℝ := ‖u‖
  have hr : 0 < r := by dsimp [r]; exact norm_pos_iff.mpr hu
  have hnormw : ‖w‖ ≤ 1 / 2 := by simpa [w] using hw
  have hsector' : ‖w‖ ≤ |2 * w.re| := by
    have hs : ‖w‖ / 2 ≤ |w.re| := by simpa [w] using hsector
    have h := mul_le_mul_of_nonneg_left hs (by norm_num : 0 ≤ (2 : ℝ))
    calc
      ‖w‖ = 2 * (‖w‖ / 2) := by ring
      _ ≤ 2 * |w.re| := h
      _ = |2 * w.re| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hxlower : 1 / 2 ≤ x := by
    dsimp [x]
    have h := norm_sub_norm_le (1 : ℂ) w
    rw [norm_one] at h
    linarith only [h, hnormw]
  have hxupper : x ≤ 3 / 2 := by
    dsimp [x]
    have h := norm_sub_le (1 : ℂ) w
    rw [norm_one] at h
    linarith only [h, hnormw]
  have hnormSq : x ^ 2 - 1 = -2 * w.re + ‖w‖ ^ 2 := by
    dsimp [x]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq, Complex.conj_re, norm_sq_eq_re_sq_add_im_sq]
    ring
  have hquadratic : ‖w‖ / 2 ≤ |x ^ 2 - 1| := by
    have hlin : ‖w‖ ≤ |2 * w.re| := hsector'
    have hdecomp : |2 * w.re| ≤ |x ^ 2 - 1| + ‖w‖ ^ 2 := by
      calc
        |2 * w.re| = |‖w‖ ^ 2 - (x ^ 2 - 1)| := by
          rw [hnormSq]
          congr 1
          ring
        _ ≤ |‖w‖ ^ 2| + |x ^ 2 - 1| := abs_sub _ _
        _ = |x ^ 2 - 1| + ‖w‖ ^ 2 := by
          rw [abs_of_nonneg (sq_nonneg _)]
          ring
    have hnormsq : ‖w‖ ^ 2 ≤ ‖w‖ / 2 := by
      linarith only [mul_le_mul_of_nonneg_left hnormw (norm_nonneg w)]
    linarith only [hlin, hdecomp, hnormsq]
  have hfactor : |x ^ 2 - 1| = |x - 1| * (x + 1) := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring, abs_mul,
      abs_of_nonneg (by linarith only [hxlower] : 0 ≤ x + 1)]
  have hxplus : x + 1 ≤ 5 / 2 := by linarith only [hxupper]
  have hxfirst : ‖w‖ / 5 ≤ |x - 1| := by
    have hmul := mul_le_mul_of_nonneg_left hxplus (abs_nonneg (x - 1))
    rw [mul_comm] at hmul
    rw [hfactor] at hquadratic
    linarith only [hquadratic, hmul]
  have hfac : u - z = u * ((1 : ℂ) - w) := by
    dsimp [w]
    field_simp [hu]
  have hnormFac : ‖u - z‖ = r * x := by
    rw [hfac, norm_mul]
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxlower
  have hxpow : |x - 1| ≤ |x ^ k - 1| := by
    by_cases hxone : 1 ≤ x
    · have hpow : x ≤ x ^ k := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hxone hk
      have hpow1 : 1 ≤ x ^ k := le_trans hxone hpow
      calc
        |x - 1| = x - 1 := abs_of_nonneg (sub_nonneg.mpr hxone)
        _ ≤ x ^ k - 1 := by linarith only [hpow]
        _ = |x ^ k - 1| := (abs_of_nonneg (sub_nonneg.mpr hpow1)).symm
    · have hxle : x ≤ 1 := le_of_not_ge hxone
      have hpow : x ^ k ≤ x := by
        simpa [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hxpos hxle hk
      have hpow1 : x ^ k ≤ 1 := le_trans hpow hxle
      calc
        |x - 1| = -(x - 1) := abs_of_nonpos (sub_nonpos.mpr hxle)
        _ = 1 - x := by ring
        _ ≤ 1 - x ^ k := by linarith only [hpow]
        _ = |x ^ k - 1| := by
          rw [abs_of_nonpos (sub_nonpos.mpr hpow1)]
          ring
  have hpowFac : ‖u - z‖ ^ k = r ^ k * x ^ k := by
    rw [hnormFac, Real.mul_rpow hr.le (le_of_lt hxpos)]
  have hnum : |‖u - z‖ ^ k - r ^ k| = r ^ k * |x ^ k - 1| := by
    rw [hpowFac]
    have hrpow : 0 ≤ r ^ k := Real.rpow_nonneg hr.le k
    rw [show r ^ k * x ^ k - r ^ k = r ^ k * (x ^ k - 1) by ring,
      abs_mul, abs_of_nonneg hrpow]
  have hscale : r ^ k * ‖w‖ = ‖z‖ * r ^ (k - 1) := by
    have hpow : r ^ (k - 1) = r ^ k / r := by
      simpa [Real.rpow_one] using (Real.rpow_sub hr k 1)
    rw [hpow]
    dsimp [w, r]
    rw [norm_div]
    field_simp [hr.ne']
  calc
    (1 / 5) * ‖z‖ * ‖u‖ ^ (k - 1) = (1 / 5) * (r ^ k * ‖w‖) := by
      rw [hscale]
      dsimp [r]
      ring
    _ = r ^ k * (‖w‖ / 5) := by ring
    _ ≤ r ^ k * |x - 1| := mul_le_mul_of_nonneg_left hxfirst
      (Real.rpow_nonneg hr.le k)
    _ ≤ r ^ k * |x ^ k - 1| := mul_le_mul_of_nonneg_left hxpow
      (Real.rpow_nonneg hr.le k)
    _ = |‖u - z‖ ^ k - ‖u‖ ^ k| := by rw [hnum]

theorem abs_planarDifferenceKernel_lower_of_sector_ge_one (k β : ℝ)
    (hk : 1 ≤ k) (z u : ℂ) (hu : u ≠ 0)
    (hw : ‖z / u‖ ≤ 1 / 2)
    (hsector : ‖z / u‖ / 2 ≤ |(z / u).re|) :
    (1 / 5) * ‖z‖ * ‖u‖ ^ (k - 1 - β) ≤
      |DOZZ.planarDifferenceKernel k β z u| := by
  have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnum := abs_norm_sub_rpow_lower_of_sector_ge_one k hk z u hu hw hsector
  have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos huNorm β
  have hpow : ‖u‖ ^ (k - 1 - β) = ‖u‖ ^ (k - 1) / ‖u‖ ^ β :=
    Real.rpow_sub huNorm (k - 1) β
  change (1 / 5) * ‖z‖ * ‖u‖ ^ (k - 1 - β) ≤
    |(‖u - z‖ ^ k - ‖u‖ ^ k) / ‖u‖ ^ β|
  rw [abs_div, abs_of_pos hden]
  calc
    (1 / 5) * ‖z‖ * ‖u‖ ^ (k - 1 - β) =
        ((1 / 5) * ‖z‖ * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β := by rw [hpow]; ring
    _ ≤ |‖u - z‖ ^ k - ‖u‖ ^ k| / ‖u‖ ^ β :=
      div_le_div_of_nonneg_right hnum hden.le

theorem planarDifferenceKernel_tail_exponent_lt (k β : ℝ)
    (hk : 0 < k) (hk₂ : k < 2) (z : ℂ) (hz : z ≠ 0)
    (hK : Integrable (DOZZ.planarDifferenceKernel k β z) volume) :
    k - 1 - β < -2 := by
  let T : ℝ := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2)))
  let R : ℝ := (2 + 4 * T / k) * ‖z‖
  let p : ℝ := k - 1 - β
  let C : ℝ := (k / 4) * ‖z‖
  let S : Set ℂ := differenceTailSector z R
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hT : 0 < T := by
    dsimp [T]
    have hfactor : 0 < 1 - k / 2 := by linarith only [hk₂]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    positivity
  have hR₂ : 2 * ‖z‖ ≤ R := by
    dsimp [R]
    have hcoef : 0 ≤ 4 * T / k := by positivity
    linarith only [mul_nonneg hcoef (norm_nonneg z)]
  have hRcoef : 4 * T * ‖z‖ ≤ k * R := by
    dsimp [R]
    field_simp [ne_of_gt hk]
    linarith only [hk]
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact differenceTailSector_measurable z R
  have hKabs : Integrable (fun u : ℂ => |DOZZ.planarDifferenceKernel k β z u|) volume := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmajor : IntegrableOn
      (fun u : ℂ => C⁻¹ * |DOZZ.planarDifferenceKernel k β z u|) S volume := by
    apply (integrableOn_univ.mpr (hKabs.const_mul C⁻¹)).mono_set
    exact Set.subset_univ S
  have hSectorRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ p) S volume := by
    apply hmajor.mono' (norm_rpow_measurable p).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hSmeas] with u hu
    rcases hu with ⟨huR, hsector⟩
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      simp at huR
      linarith only [huR, hR]
    have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hlarge : 2 * ‖z‖ ≤ ‖u‖ := le_trans hR₂ huR
    have hw₁ : ‖z / u‖ ≤ 1 / 2 := by
      rw [norm_div]
      apply (div_le_iff₀ huNorm).2
      linarith only [hlarge]
    have hprod : 4 * T * ‖z‖ ≤ k * ‖u‖ := by
      calc
        4 * T * ‖z‖ ≤ k * R := hRcoef
        _ ≤ k * ‖u‖ := mul_le_mul_of_nonneg_left huR hk.le
    have hden : 0 < 4 * T := by positivity
    have hratio : ‖z‖ ≤ k * ‖u‖ / (4 * T) := by
      apply (le_div_iff₀ hden).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    have hw₂ : ‖z / u‖ ≤ k / (4 * T) := by
      rw [norm_div]
      apply (div_le_iff₀ huNorm).2
      calc
        ‖z‖ ≤ k * ‖u‖ / (4 * T) := hratio
        _ = k / (4 * T) * ‖u‖ := by ring
    have hkernel := abs_planarDifferenceKernel_lower_of_sector
      k β hk hk₂ z u hu0 hw₁ hw₂ hsector
    have hpoint : ‖u‖ ^ p ≤ C⁻¹ *
        |DOZZ.planarDifferenceKernel k β z u| := by
      have hdiv : ‖u‖ ^ p ≤
          |DOZZ.planarDifferenceKernel k β z u| / C := by
        apply (le_div_iff₀ hC).2
        simpa [C, p, mul_comm, mul_left_comm, mul_assoc] using hkernel
      calc
        ‖u‖ ^ p ≤ |DOZZ.planarDifferenceKernel k β z u| / C := hdiv
        _ = C⁻¹ * |DOZZ.planarDifferenceKernel k β z u| := by
          rw [div_eq_mul_inv, mul_comm]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) p)]
    exact hpoint
  have hSectorRot : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (quarterTurn '' S) volume := by
    apply (quarterTurn_measurePreserving.integrableOn_image
      quarterTurn.toHomeomorph.measurableEmbedding
      (f := fun u : ℂ => ‖u‖ ^ p) (s := S)).2
    simpa [Function.comp_def, quarterTurn] using hSectorRadial
  have hcover : (Metric.ball (0 : ℂ) R)ᶜ ⊆ S ∪ quarterTurn '' S := by
    intro u hu
    have huR : R ≤ ‖u‖ := by
      by_contra h
      apply hu
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      exact (not_le_of_gt hR) (by simpa using huR)
    rcases sector_or_quarterTurn_sector z R hu0 huR with hs | hs
    · exact Or.inl (by simpa [S] using hs)
    · exact Or.inr (by simpa [S] using hs)
  have hExterior : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (Metric.ball (0 : ℂ) R)ᶜ volume := by
    apply (integrableOn_union.mpr ⟨hSectorRadial, hSectorRot⟩).mono_set hcover
  have hexp := (integrableOn_norm_rpow_ball_compl_iff p R hR).1 hExterior
  dsimp [p] at hexp
  exact hexp

theorem planarDifferenceKernel_tail_exponent_lt_of_ge_one (k β : ℝ)
    (hk : 1 ≤ k) (z : ℂ) (hz : z ≠ 0)
    (hK : Integrable (DOZZ.planarDifferenceKernel k β z) volume) :
    k - 1 - β < -2 := by
  let R : ℝ := 64 * ‖z‖
  let p : ℝ := k - 1 - β
  let C : ℝ := (1 / 5) * ‖z‖
  let S : Set ℂ := differenceTailSector z R
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hR : 0 < R := by dsimp [R]; positivity
  have hR₂ : 2 * ‖z‖ ≤ R := by dsimp [R]; linarith only [hzNorm]
  have hC : 0 < C := by dsimp [C]; positivity
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact differenceTailSector_measurable z R
  have hKabs : Integrable (fun u : ℂ => |DOZZ.planarDifferenceKernel k β z u|) volume := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmajor : IntegrableOn
      (fun u : ℂ => C⁻¹ * |DOZZ.planarDifferenceKernel k β z u|) S volume := by
    apply (integrableOn_univ.mpr (hKabs.const_mul C⁻¹)).mono_set
    exact Set.subset_univ S
  have hSectorRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ p) S volume := by
    apply hmajor.mono' (norm_rpow_measurable p).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hSmeas] with u hu
    rcases hu with ⟨huR, hsector⟩
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      simp at huR
      linarith only [huR, hR]
    have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hw : ‖z / u‖ ≤ 1 / 2 := by
      rw [norm_div]
      apply (div_le_iff₀ huNorm).2
      dsimp [R] at huR
      linarith only [huR, hzNorm]
    have hkernel := abs_planarDifferenceKernel_lower_of_sector_ge_one
      k β hk z u hu0 hw hsector
    have hpoint : ‖u‖ ^ p ≤ C⁻¹ *
        |DOZZ.planarDifferenceKernel k β z u| := by
      have hdiv : ‖u‖ ^ p ≤
          |DOZZ.planarDifferenceKernel k β z u| / C := by
        apply (le_div_iff₀ hC).2
        simpa [C, p, mul_comm, mul_left_comm, mul_assoc] using hkernel
      calc
        ‖u‖ ^ p ≤ |DOZZ.planarDifferenceKernel k β z u| / C := hdiv
        _ = C⁻¹ * |DOZZ.planarDifferenceKernel k β z u| := by
          rw [div_eq_mul_inv, mul_comm]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) p)]
    exact hpoint
  have hSectorRot : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (quarterTurn '' S) volume := by
    apply (quarterTurn_measurePreserving.integrableOn_image
      quarterTurn.toHomeomorph.measurableEmbedding
      (f := fun u : ℂ => ‖u‖ ^ p) (s := S)).2
    simpa [Function.comp_def, quarterTurn] using hSectorRadial
  have hcover : (Metric.ball (0 : ℂ) R)ᶜ ⊆ S ∪ quarterTurn '' S := by
    intro u hu
    have huR : R ≤ ‖u‖ := by
      by_contra h
      apply hu
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h
    have hu0 : u ≠ 0 := by
      intro hu0
      subst u
      exact (not_le_of_gt hR) (by simpa using huR)
    rcases sector_or_quarterTurn_sector z R hu0 huR with hs | hs
    · exact Or.inl (by simpa [S] using hs)
    · exact Or.inr (by simpa [S] using hs)
  have hExterior : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (Metric.ball (0 : ℂ) R)ᶜ volume := by
    apply (integrableOn_union.mpr ⟨hSectorRadial, hSectorRot⟩).mono_set hcover
  have hexp := (integrableOn_norm_rpow_ball_compl_iff p R hR).1 hExterior
  dsimp [p] at hexp
  exact hexp

theorem planarDifferenceKernel_local_exponent_gt_neg_two (k β : ℝ)
    (hk : 0 < k) (z : ℂ) (hz : z ≠ 0)
    (hK : Integrable (DOZZ.planarDifferenceKernel k β z) volume) :
    β < 2 := by
  let A : ℝ := ‖z‖ ^ k
  let C : ℝ := A / 2
  let f : ℂ → ℝ := fun u => ‖u - z‖ ^ k - ‖u‖ ^ k
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hA : 0 < A := by
    dsimp [A]
    exact Real.rpow_pos_of_pos hzNorm k
  have hC : 0 < C := by dsimp [C]; positivity
  have hf₀ : f 0 = A := by
    dsimp [f, A]
    simp [Real.zero_rpow, ne_of_gt hk]
  have hnormShift : ContinuousAt (fun u : ℂ => ‖u - z‖) 0 := by fun_prop
  have hpowShift : ContinuousAt (fun u : ℂ => ‖u - z‖ ^ k) 0 :=
    hnormShift.rpow_const (Or.inl (by simpa using hzNorm.ne'))
  have hpowNorm : ContinuousAt (fun u : ℂ => ‖u‖ ^ k) 0 :=
    (continuous_norm.continuousAt).rpow_const (Or.inr hk.le)
  have hfcont : ContinuousAt f 0 := by
    exact hpowShift.sub hpowNorm
  have hevent : ∀ᶠ u : ℂ in 𝓝 0, |f u - A| < A / 2 := by
    have hball := hfcont (Metric.ball_mem_nhds (f 0) (by positivity : 0 < A / 2))
    filter_upwards [hball] with u hu
    simpa [hf₀, Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hu
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.mp hevent
  have hKabs : Integrable (fun u : ℂ => |DOZZ.planarDifferenceKernel k β z u|) volume := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmajor : IntegrableOn
      (fun u : ℂ => C⁻¹ * |DOZZ.planarDifferenceKernel k β z u|)
      (Metric.ball (0 : ℂ) δ) volume := by
    apply (integrableOn_univ.mpr (hKabs.const_mul C⁻¹)).mono_set
    exact Set.subset_univ _
  have hLocalRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ (-β))
      (Metric.ball (0 : ℂ) δ) volume := by
    apply hmajor.mono' (norm_rpow_measurable (-β)).aestronglyMeasurable
    have hzero : volume.restrict (Metric.ball (0 : ℂ) δ) {0} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton (0 : ℂ))]
      exact measure_mono_null Set.inter_subset_left (by simp)
    have huNe : ∀ᵐ u ∂volume.restrict (Metric.ball (0 : ℂ) δ), u ≠ 0 := by
      rw [ae_iff]
      simp [hzero]
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, huNe]
      with u huBall huNe
    have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr huNe
    have huδ : dist u 0 < δ := by simpa [Metric.mem_ball] using huBall
    have huBallδ : u ∈ Metric.ball (0 : ℂ) δ := by
      simpa [Metric.mem_ball] using huδ
    have hclose := hδball u huBallδ
    have hnum : C ≤ |f u| := by
      have htri : A ≤ |f u - A| + |f u| := by
        calc
          A = |A| := (abs_of_nonneg hA.le).symm
          _ = |(A - f u) + f u| := by congr 1; ring
          _ ≤ |A - f u| + |f u| := abs_add_le _ _
          _ = |f u - A| + |f u| := by rw [abs_sub_comm]
      dsimp [C]
      linarith only [htri, hclose]
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos huNorm β
    have hrecip : ‖u‖ ^ (-β) = 1 / ‖u‖ ^ β := by
      rw [show -β = 0 - β by ring, Real.rpow_sub huNorm, Real.rpow_zero]
    have hkernel : C * ‖u‖ ^ (-β) ≤
        |DOZZ.planarDifferenceKernel k β z u| := by
      change C * ‖u‖ ^ (-β) ≤ |f u / ‖u‖ ^ β|
      rw [abs_div, abs_of_pos hden]
      calc
        C * ‖u‖ ^ (-β) = C / ‖u‖ ^ β := by rw [hrecip]; ring
        _ ≤ |f u| / ‖u‖ ^ β := div_le_div_of_nonneg_right hnum hden.le
    have hpoint : ‖u‖ ^ (-β) ≤ C⁻¹ *
        |DOZZ.planarDifferenceKernel k β z u| := by
      have hdiv : ‖u‖ ^ (-β) ≤
          |DOZZ.planarDifferenceKernel k β z u| / C := by
        apply (le_div_iff₀ hC).2
        simpa [mul_comm] using hkernel
      calc
        ‖u‖ ^ (-β) ≤
            |DOZZ.planarDifferenceKernel k β z u| / C := hdiv
        _ = C⁻¹ * |DOZZ.planarDifferenceKernel k β z u| := by
          rw [div_eq_mul_inv, mul_comm]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) (-β))]
    exact hpoint
  have hexp := (integrableOn_norm_rpow_ball_iff (-β) δ hδ).1 hLocalRadial
  linarith only [hexp]

end DOZZ.Proofs
