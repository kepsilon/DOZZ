/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RealSecondParent
public import DOZZ.Hypergeom.Planar.TaylorIntegral
public import DOZZ.Hypergeom.Planar.DifferenceIntegral
public import DOZZ.Hypergeom.Planar.RieszNormalization
public import DOZZ.Hypergeom.Planar.DerivativeIntegrable
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! The pure Wirtinger integral follows from the real second derivative and the mixed Riesz
convolution. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

private theorem continuousAt_realGamma_of_pos (x : ℝ) (hx : 0 < x) :
    ContinuousAt Real.Gamma x := by
  have hnoPole : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := by
    intro m hm
    have hxEq : x = -(m : ℝ) := by exact_mod_cast hm
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGamma : ContinuousAt (fun y : ℝ => Complex.Gamma (y : ℂ)) x :=
    (Complex.continuousAt_Gamma (x : ℂ) hnoPole).comp
      Complex.continuous_ofReal.continuousAt
  have hReal := Complex.continuous_re.continuousAt.comp hGamma
  have hEq : (fun y : ℝ => Complex.re (Complex.Gamma (y : ℂ))) = Real.Gamma := by
    funext y
    rw [Complex.Gamma_ofReal]
    simp
  rw [← hEq]
  exact hReal

private noncomputable def planarRieszCoefficientReal (k β : ℝ) : ℝ :=
  ((k / 2) ^ 2 / ((2 + k - β) / 2) ^ 2) * Real.pi *
    (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
      Real.Gamma ((β - k) / 2) /
        (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
          Real.Gamma (1 + (k - β) / 2)))

private noncomputable def planarWirtingerTargetReal (k β : ℝ) : ℝ :=
  ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
    planarRieszCoefficientReal k β

private theorem planarWirtingerKernel_reflection (k β : ℝ) (u : ℂ) :
    DOZZ.planarWirtingerKernel k β 1 (star u) =
      star (DOZZ.planarWirtingerKernel k β 1 u) := by
  rw [DOZZ.planarWirtingerKernel, DOZZ.planarWirtingerKernel]
  have hsub : star u - (1 : ℂ) = star (u - 1) := by simp
  have hnum : ‖star u - 1‖ ^ k = ‖u - 1‖ ^ k := by
    rw [hsub, norm_star]
  rw [hnum]
  simp

private theorem half_cancel (x : ℝ) : x * (1 / 2) + x * (-1 / 2) = 0 := by ring

private theorem planarRealSecondDifferenceLimit_decompose (k β : ℝ) (u : ℂ)
    (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    planarRealSecondDifferenceLimit k β u =
      2 * ((k / 2) * (k / 2 - 1) *
          (DOZZ.planarWirtingerKernel k β 1 u).re +
        (k / 2) ^ 2 * DOZZ.planarMixedKernel k β 1 u) := by
  let v : ℂ := u - 1
  let r : ℝ := ‖u‖
  let s : ℝ := ‖v‖
  have hv : v ≠ 0 := by
    dsimp [v]
    exact sub_ne_zero.mpr hu1
  have hr : 0 < r := by dsimp [r]; exact norm_pos_iff.mpr hu0
  have hs : 0 < s := by dsimp [s]; exact norm_pos_iff.mpr hv
  have hrβ : 0 < r ^ β := Real.rpow_pos_of_pos hr β
  have hW : (DOZZ.planarWirtingerKernel k β 1 u).re =
      r ^ (-β) * (((s ^ k : ℝ) : ℂ) / v ^ 2).re := by
    unfold DOZZ.planarWirtingerKernel
    have hshift : (1 : ℂ) - u = -v := by dsimp [v]; ring
    rw [hshift, neg_sq]
    have hdiv : (((s ^ k : ℝ) : ℂ) / (v ^ 2 * ((r ^ β : ℝ) : ℂ))) =
        (((s ^ k : ℝ) : ℂ) / v ^ 2) / (r ^ β : ℝ) := by
      field_simp [pow_ne_zero 2 hv, hrβ.ne']
    rw [hdiv, Complex.div_ofReal_re, Real.rpow_neg (norm_nonneg u)]
    dsimp [r]
    ring
  have hsqre : (v ^ 2).re = 2 * v.re ^ 2 - s ^ 2 := by
    rw [pow_two, Complex.mul_re]
    have hnorm : s ^ 2 = v.re ^ 2 + v.im ^ 2 := by
      calc
        s ^ 2 = Complex.normSq v := by
          dsimp [s]
          exact (Complex.normSq_eq_norm_sq v).symm
        _ = v.re ^ 2 + v.im ^ 2 := by simp [Complex.normSq_apply, pow_two]
    linear_combination hnorm
  have hsqnorm : Complex.normSq (v ^ 2) = s ^ 4 := by
    rw [pow_two, Complex.normSq_mul, Complex.normSq_eq_norm_sq]
    dsimp [s]
    ring
  have hRe : (((s ^ k : ℝ) : ℂ) / v ^ 2).re =
      s ^ (k - 4) * (2 * v.re ^ 2 - s ^ 2) := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    rw [hsqre, hsqnorm]
    simp only [zero_div, add_zero]
    calc
      s ^ k * (2 * v.re ^ 2 - s ^ 2) / s ^ 4 =
          (s ^ k / s ^ 4) * (2 * v.re ^ 2 - s ^ 2) := by ring
      _ = s ^ (k - 4) * (2 * v.re ^ 2 - s ^ 2) := by
        have hpow : s ^ k / s ^ (4 : ℕ) = s ^ (k - 4) := by
          rw [← Real.rpow_natCast s 4]
          exact (Real.rpow_sub hs k 4).symm
        rw [hpow]
  have hM : DOZZ.planarMixedKernel k β 1 u =
      r ^ (-β) * s ^ (k - 2) := by
    unfold DOZZ.planarMixedKernel
    have hshift : u - (1 : ℂ) = v := by dsimp [v]
    rw [hshift, div_eq_mul_inv, Real.rpow_neg (norm_nonneg u)]
    dsimp [r, s]
    ring
  have hpow₁ : (s ^ (2 : ℕ)) ^ (k / 2 - 2) = s ^ (k - 4) := by
    have hbase : s ^ (2 : ℕ) = s ^ (2 : ℝ) := (Real.rpow_natCast s 2).symm
    calc
      (s ^ (2 : ℕ)) ^ (k / 2 - 2) = (s ^ (2 : ℝ)) ^ (k / 2 - 2) := by
        rw [hbase]
      _ = s ^ (2 * (k / 2 - 2)) := (Real.rpow_mul hs.le 2 (k / 2 - 2)).symm
      _ = s ^ (k - 4) := by congr 1; ring
  have hpow₂ : (s ^ (2 : ℕ)) ^ (k / 2 - 1) = s ^ (k - 2) := by
    have hbase : s ^ (2 : ℕ) = s ^ (2 : ℝ) := (Real.rpow_natCast s 2).symm
    calc
      (s ^ (2 : ℕ)) ^ (k / 2 - 1) = (s ^ (2 : ℝ)) ^ (k / 2 - 1) := by
        rw [hbase]
      _ = s ^ (2 * (k / 2 - 1)) := (Real.rpow_mul hs.le 2 (k / 2 - 1)).symm
      _ = s ^ (k - 2) := by congr 1; ring
  have hpowAdd : s ^ (k - 4) * s ^ (2 : ℕ) = s ^ (k - 2) := by
    calc
      s ^ (k - 4) * s ^ (2 : ℕ) = s ^ (k - 4) * s ^ (2 : ℝ) := by
        exact congrArg (fun x : ℝ => s ^ (k - 4) * x)
          (Real.rpow_natCast s 2).symm
      _ = s ^ ((k - 4) + 2) := (Real.rpow_add hs (k - 4) 2).symm
      _ = s ^ (k - 2) := by congr 1; ring
  rw [planarRealSecondDifferenceLimit, hW, hRe, hM, hpow₁, hpow₂]
  dsimp [r, v]
  ring_nf
  have hpowAddNF : s ^ (-4 + k) * s ^ (2 : ℝ) = s ^ (-2 + k) := by
    simpa [sub_eq_add_neg, add_comm] using hpowAdd
  simp_rw [← hpowAddNF]
  let R : ℝ := ‖u‖ ^ (-β)
  let S : ℝ := s ^ (-4 + k)
  have hR : R = ‖u‖ ^ (-β) := rfl
  have hS : S = s ^ (-4 + k) := rfl
  simp_rw [← hR, ← hS]
  ring_nf
  have hpair : R * k ^ 2 * S * s ^ (2 : ℝ) * (1 / 2) +
      R * k ^ 2 * S * s ^ 2 * (-1 / 2) = 0 := by
    have hs2 : s ^ (2 : ℝ) = s ^ (2 : ℕ) := Real.rpow_natCast s 2
    calc
      _ = R * k ^ 2 * S * s ^ (2 : ℝ) * (1 / 2) +
          R * k ^ 2 * S * s ^ (2 : ℝ) * (-1 / 2) := by
            exact congrArg
              (fun x : ℝ => R * k ^ 2 * S * s ^ (2 : ℝ) * (1 / 2) +
                R * k ^ 2 * S * x * (-1 / 2)) hs2.symm
      _ = 0 := half_cancel _
  conv_rhs =>
    rw [add_assoc]
    arg 2
    rw [hpair]
  simp

private theorem planarWirtinger_integral_at_one_from_parent (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (A : ℝ)
    (hA : (A : ℂ) = DOZZ.planarGaussConstant k β)
    (hsecond : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      (2 + k - β) * (1 + k - β) * A) :
    (k / 2) * (k / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β := by
  let W : ℂ → ℂ := fun u => DOZZ.planarWirtingerKernel k β 1 u
  let M : ℂ → ℝ := fun u => DOZZ.planarMixedKernel k β 1 u
  let q : ℝ := k / 2
  let p : ℝ := q * (q - 1)
  let α : ℝ := 2 + k - β
  let X : ℝ := ∫ u : ℂ, (W u).re
  let m : ℝ := ∫ u : ℂ, M u
  have hWInt : Integrable W volume := by
    apply (integrable_planarWirtingerKernel_iff k β hk 1 (by norm_num)).2
    exact ⟨hβ, hβ₂⟩
  have hMData := planar_mixed_integral k β hk hβ hβ₂ 1 (by norm_num)
  have hMInt : Integrable M volume := by simpa [M] using hMData.1
  have hXInt : Integrable (fun u : ℂ => (W u).re) volume := hWInt.re
  have hdecompAE : (fun u : ℂ => planarRealSecondDifferenceLimit k β u) =ᵐ[volume]
      fun u => 2 * (p * (W u).re + q ^ 2 * M u) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
    simpa [p, q, W, M] using planarRealSecondDifferenceLimit_decompose k β u hu0 hu1
  have hdecomp : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      2 * (p * X + q ^ 2 * m) := by
    calc
      _ = ∫ u : ℂ, 2 * (p * (W u).re + q ^ 2 * M u) := integral_congr_ae hdecompAE
      _ = 2 * ((∫ u : ℂ, p * (W u).re) + (∫ u : ℂ, q ^ 2 * M u)) := by
        rw [integral_const_mul, integral_add (hXInt.const_mul p) (hMInt.const_mul (q ^ 2))]
      _ = 2 * (p * X + q ^ 2 * m) := by
        rw [integral_const_mul, integral_const_mul]
  have hreflection : ∀ u : ℂ, W (star u) = star (W u) := by
    intro u
    exact planarWirtingerKernel_reflection k β u
  have hcomp : (∫ u : ℂ, W (star u)) = ∫ u : ℂ, W u := by
    change (∫ u : ℂ, W (Complex.conjLIE u)) = _
    exact (LinearIsometryEquiv.measurePreserving Complex.conjLIE).integral_comp
      Complex.conjLIE.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding W
  have hstar : (∫ u : ℂ, W (star u)) = star (∫ u : ℂ, W u) := by
    calc
      _ = ∫ u : ℂ, star (W u) := integral_congr_ae (Filter.Eventually.of_forall hreflection)
      _ = _ := by simpa only [starRingEnd_apply] using (integral_conj (f := W))
  have hWself : star (∫ u : ℂ, W u) = ∫ u : ℂ, W u := hstar.symm.trans hcomp
  have hWreal : (∫ u : ℂ, W u) = (X : ℂ) := by
    calc
      _ = (((∫ u : ℂ, W u).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp hWself).symm
      _ = (X : ℂ) := by
        change Complex.ofReal ((∫ u : ℂ, W u).re) =
          Complex.ofReal (∫ u : ℂ, (W u).re)
        exact congrArg Complex.ofReal (integral_re hWInt).symm
  have hMvalue : ((q ^ 2 * m : ℝ) : ℂ) = ((α : ℂ) / 2) ^ 2 *
      DOZZ.planarGaussConstant k β := by
    simpa [M, m, q, α, norm_one, Real.one_rpow] using hMData.2
  have hsecond' : (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      α * (α - 1) * A := by
    calc
      _ = (2 + k - β) * (1 + k - β) * A := hsecond
      _ = α * (α - 1) * A := by dsimp [α]; ring
  have hbalance : Complex.ofReal (α * (α - 1) * A) =
      Complex.ofReal (2 * (p * X + q ^ 2 * m)) := by
    calc
      _ = Complex.ofReal (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) :=
        congrArg Complex.ofReal hsecond'.symm
      _ = _ := congrArg Complex.ofReal hdecomp
  have htarget : Complex.ofReal (p * X) =
      Complex.ofReal ((α / 2) * (α / 2 - 1)) * DOZZ.planarGaussConstant k β := by
    have hcoeff : ((α : ℂ) / 2) ^ 2 = Complex.ofReal ((α / 2) ^ 2) := by
      push_cast
      ring
    have hbalanceReal : α * (α - 1) * A = 2 * (p * X + q ^ 2 * m) :=
      Complex.ofReal_injective hbalance
    have hsolve : p * X = α * (α - 1) / 2 * A - q ^ 2 * m := by
      linear_combination (-1 / 2 : ℝ) * hbalanceReal
    calc
      _ = Complex.ofReal (α * (α - 1) / 2 * A - q ^ 2 * m) :=
        congrArg Complex.ofReal hsolve
      _ = Complex.ofReal (α * (α - 1) / 2 * A) - Complex.ofReal (q ^ 2 * m) :=
        Complex.ofReal_sub _ _
      _ = Complex.ofReal (α * (α - 1) / 2) * (A : ℂ) - Complex.ofReal (q ^ 2 * m) := by
        rw [Complex.ofReal_mul]
      _ = Complex.ofReal (α * (α - 1) / 2) * DOZZ.planarGaussConstant k β -
          ((α : ℂ) / 2) ^ 2 * DOZZ.planarGaussConstant k β := by rw [hA, hMvalue]
      _ = Complex.ofReal (α * (α - 1) / 2) * DOZZ.planarGaussConstant k β -
          Complex.ofReal ((α / 2) ^ 2) * DOZZ.planarGaussConstant k β := by rw [hcoeff]
      _ = Complex.ofReal (α * (α - 1) / 2 - (α / 2) ^ 2) *
          DOZZ.planarGaussConstant k β := by
        rw [Complex.ofReal_sub]
        ring
      _ = _ := by
        have hcoef : α * (α - 1) / 2 - (α / 2) ^ 2 =
            (α / 2) * (α / 2 - 1) := by ring
        rw [hcoef]
  rw [hWreal]
  simpa [p, q, α] using htarget

private theorem planarWirtinger_integral_at_one_value (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (hβne : β ≠ k + 1) :
    (k / 2) * (k / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β := by
  rcases lt_or_gt_of_ne hβne with hTaylor | hDifference
  · let A : ℝ := ∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u
    have hA : (A : ℂ) = DOZZ.planarGaussConstant k β := by
      simpa [A, norm_one, Real.one_rpow, integral_complex_ofReal] using
        ((planar_taylor_integral k β hk hβ hβ₂ hTaylor) 1).2
    have hsecond := planarTaylor_real_second_derivative_relation k β hk hβ hβ₂ hTaylor
    exact planarWirtinger_integral_at_one_from_parent k β hk hβ hβ₂ A hA
      (by simpa [A] using hsecond)
  · let A : ℝ := ∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u
    have hA : (A : ℂ) = DOZZ.planarGaussConstant k β := by
      simpa [A, norm_one, Real.one_rpow, integral_complex_ofReal] using
        ((planar_difference_integral k β hk hDifference hβ₂) 1).2
    have hsecond := planarDifference_real_second_derivative_relation k β hk
      (by linarith [hβ]) hβ₂ hDifference
    exact planarWirtinger_integral_at_one_from_parent k β hk hβ hβ₂ A hA
      (by simpa [A] using hsecond)

private theorem planarWirtinger_integral_tendsto_parameter (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    Tendsto (fun b : ℝ => ∫ u : ℂ, DOZZ.planarWirtingerKernel k b 1 u)
      (𝓝 β) (𝓝 (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := by
  let δ : ℝ := min ((β - k) / 2) ((2 - β) / 2)
  let βlo : ℝ := β - δ
  let βhi : ℝ := β + δ
  let B : ℂ → ℝ := fun u =>
    ‖u‖ ^ (-βlo) * ‖u - 1‖ ^ (k - 2) +
      ‖u‖ ^ (-βhi) * ‖u - 1‖ ^ (k - 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hklo : k < βlo := by
    dsimp [βlo, δ]
    have hmin : min ((β - k) / 2) ((2 - β) / 2) ≤ (β - k) / 2 := min_le_left _ _
    linarith
  have hhi₂ : βhi < 2 := by
    dsimp [βhi, δ]
    have hmin : min ((β - k) / 2) ((2 - β) / 2) ≤ (2 - β) / 2 := min_le_right _ _
    linarith
  have hβlo : βlo < β := by dsimp [βlo]; linarith
  have hβhi : β < βhi := by dsimp [βhi]; linarith
  have hparam : ∀ᶠ b : ℝ in 𝓝 β, βlo < b ∧ b < βhi := by
    filter_upwards [Ioo_mem_nhds hβlo hβhi] with b hb
    exact ⟨hb.1, hb.2⟩
  have hlowInt := positive_riesz_convolution_integrable k βlo hk hklo
    (by linarith [hβlo, hhi₂])
    (1 : ℂ) (by norm_num)
  have hhighInt := positive_riesz_convolution_integrable k βhi hk
    (by linarith [hβ, hβhi]) hhi₂
    (1 : ℂ) (by norm_num)
  have hBInt : Integrable B volume := by
    dsimp [B]
    exact hlowInt.add hhighInt
  have hmeas : ∀ᶠ b : ℝ in 𝓝 β,
      AEStronglyMeasurable (DOZZ.planarWirtingerKernel k b 1) volume := by
    filter_upwards [hparam] with b hb
    have hi : Integrable (DOZZ.planarWirtingerKernel k b 1) volume :=
      (integrable_planarWirtingerKernel_iff k b hk 1 (by norm_num)).2
        ⟨by linarith [hb.1], by linarith [hb.2]⟩
    exact hi.aestronglyMeasurable
  have hbound : ∀ᶠ b : ℝ in 𝓝 β, ∀ᵐ u ∂volume,
      ‖DOZZ.planarWirtingerKernel k b 1 u‖ ≤ B u := by
    filter_upwards [hparam] with b hb
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
    have hrpos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hnorm := norm_planarWirtingerKernel_eq k b 1 u hu0 hu1
    have hnorm' : ‖DOZZ.planarWirtingerKernel k b 1 u‖ =
        ‖u‖ ^ (-b) * ‖u - 1‖ ^ (k - 2) := by
      rw [hnorm, div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg u)]
      ring
    rw [hnorm']
    by_cases hrle : ‖u‖ ≤ 1
    · have hpow : ‖u‖ ^ (-b) ≤ ‖u‖ ^ (-βhi) :=
        Real.rpow_le_rpow_of_exponent_ge hrpos hrle (by linarith [hb.2])
      have hsnonneg : 0 ≤ ‖u - 1‖ ^ (k - 2) := Real.rpow_nonneg (norm_nonneg _) _
      calc
        ‖u‖ ^ (-b) * ‖u - 1‖ ^ (k - 2) ≤
            ‖u‖ ^ (-βhi) * ‖u - 1‖ ^ (k - 2) := mul_le_mul_of_nonneg_right hpow hsnonneg
        _ ≤ B u := by
          dsimp [B]
          exact le_add_of_nonneg_left (mul_nonneg
            (Real.rpow_nonneg (norm_nonneg u) _) hsnonneg)
    · have hrge : 1 ≤ ‖u‖ := le_of_not_ge hrle
      have hpow : ‖u‖ ^ (-b) ≤ ‖u‖ ^ (-βlo) :=
        Real.rpow_le_rpow_of_exponent_le hrge (by linarith [hb.1])
      have hsnonneg : 0 ≤ ‖u - 1‖ ^ (k - 2) := Real.rpow_nonneg (norm_nonneg _) _
      calc
        ‖u‖ ^ (-b) * ‖u - 1‖ ^ (k - 2) ≤
            ‖u‖ ^ (-βlo) * ‖u - 1‖ ^ (k - 2) := mul_le_mul_of_nonneg_right hpow hsnonneg
        _ ≤ B u := by
          dsimp [B]
          exact le_add_of_nonneg_right (mul_nonneg
            (Real.rpow_nonneg (norm_nonneg u) _) hsnonneg)
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun b : ℝ => DOZZ.planarWirtingerKernel k b 1 u) (𝓝 β)
      (𝓝 (DOZZ.planarWirtingerKernel k β 1 u)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume 1] with u hu0 hu1
    have hpow : Tendsto (fun b : ℝ => ‖u‖ ^ b) (𝓝 β) (𝓝 (‖u‖ ^ β)) :=
      (Real.continuousAt_const_rpow (norm_ne_zero_iff.mpr hu0)).tendsto
    have hpowC : Tendsto (fun b : ℝ => ((‖u‖ ^ b : ℝ) : ℂ))
        (𝓝 β) (𝓝 ((‖u‖ ^ β : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hpow
    have hdenom : Tendsto (fun b : ℝ => (1 - u) ^ 2 * ((‖u‖ ^ b : ℝ) : ℂ))
        (𝓝 β) (𝓝 ((1 - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ))) :=
      tendsto_const_nhds.mul hpowC
    have hdenom0 : (1 - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ) ≠ 0 := by
      apply mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hu1)))
      exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hu0) β).ne'
    let N : ℂ := (‖u - 1‖ ^ k : ℝ)
    have hkernel : Tendsto
        (fun b : ℝ => N / ((1 - u) ^ 2 * ((‖u‖ ^ b : ℝ) : ℂ)))
        (𝓝 β) (𝓝 (N / ((1 - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ)))) := by
      exact tendsto_const_nhds.div hdenom hdenom0
    simpa [N, DOZZ.planarWirtingerKernel] using hkernel
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence B
    hmeas hbound hBInt hlim

private theorem planarWirtingerTargetReal_continuousAt (k : ℝ) (hk : 0 < k)
    (hk1 : k < 1) :
    ContinuousAt (planarWirtingerTargetReal k) (k + 1) := by
  let qA : ℝ → ℝ := fun b => (2 + k - b) / 2
  let N : ℝ → ℝ := fun b =>
    Real.Gamma (1 - b / 2) * Real.Gamma (k / 2) * Real.Gamma ((b - k) / 2)
  let D : ℝ → ℝ := fun b =>
    Real.Gamma (b / 2) * Real.Gamma (1 - k / 2) * Real.Gamma (1 + (k - b) / 2)
  have hqA : ContinuousAt qA (k + 1) := by
    dsimp [qA]
    fun_prop
  have hqA0 : qA (k + 1) ≠ 0 := by
    have hval : qA (k + 1) = (1 : ℝ) / 2 := by dsimp [qA]; ring
    rw [hval]
    norm_num
  have harg1 : ContinuousAt (fun b : ℝ => 1 - b / 2) (k + 1) := by fun_prop
  have harg2 : ContinuousAt (fun b : ℝ => b / 2) (k + 1) := by fun_prop
  have harg3 : ContinuousAt (fun b : ℝ => (b - k) / 2) (k + 1) := by fun_prop
  have harg6 : ContinuousAt (fun b : ℝ => 1 + (k - b) / 2) (k + 1) := by fun_prop
  have hΓ1 : ContinuousAt (fun b : ℝ => Real.Gamma (1 - b / 2)) (k + 1) := by
    have hp : 0 < 1 - (k + 1) / 2 := by linarith
    have hcomp := (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg1 (by ring)
    change ContinuousAt (Real.Gamma ∘ fun b : ℝ => 1 - b / 2) (k + 1)
    exact hcomp
  have hΓ2 : ContinuousAt (fun b : ℝ => Real.Gamma (b / 2)) (k + 1) := by
    have hp : 0 < (k + 1) / 2 := by linarith
    have hcomp := (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg2 (by ring)
    change ContinuousAt (Real.Gamma ∘ fun b : ℝ => b / 2) (k + 1)
    exact hcomp
  have hΓ3 : ContinuousAt (fun b : ℝ => Real.Gamma ((b - k) / 2)) (k + 1) := by
    have hp : 0 < ((k + 1) - k) / 2 := by norm_num
    have hcomp := (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg3 (by ring)
    change ContinuousAt (Real.Gamma ∘ fun b : ℝ => (b - k) / 2) (k + 1)
    exact hcomp
  have hΓ6 : ContinuousAt (fun b : ℝ => Real.Gamma (1 + (k - b) / 2)) (k + 1) := by
    have hp : 0 < 1 + (k - (k + 1)) / 2 := by norm_num
    have hcomp := (continuousAt_realGamma_of_pos _ hp).comp_of_eq harg6 (by ring)
    change ContinuousAt (Real.Gamma ∘ fun b : ℝ => 1 + (k - b) / 2) (k + 1)
    exact hcomp
  have hN : ContinuousAt N (k + 1) := by
    dsimp [N]
    exact hΓ1.mul continuousAt_const |>.mul hΓ3
  have hD : ContinuousAt D (k + 1) := by
    dsimp [D]
    exact hΓ2.mul continuousAt_const |>.mul hΓ6
  have hDpos : 0 < D (k + 1) := by
    dsimp [D]
    have hp2 : 0 < (k + 1) / 2 := by linarith
    have hp5 : 0 < 1 - k / 2 := by linarith
    have hp6 : 0 < 1 + (k - (k + 1)) / 2 := by norm_num
    exact mul_pos (mul_pos (Real.Gamma_pos_of_pos hp2) (Real.Gamma_pos_of_pos hp5))
      (Real.Gamma_pos_of_pos hp6)
  have hbase : ContinuousAt (fun b : ℝ => Real.pi * (N b / D b)) (k + 1) :=
    continuousAt_const.mul (hN.div hD hDpos.ne')
  have hfactor : ContinuousAt (fun b : ℝ => (k / 2) ^ 2 / (qA b) ^ 2) (k + 1) :=
    continuousAt_const.div (hqA.pow 2) (pow_ne_zero 2 hqA0)
  have hcoeff : ContinuousAt (fun b : ℝ => qA b * (qA b - 1)) (k + 1) :=
    hqA.mul (hqA.sub continuousAt_const)
  have htarget : ContinuousAt (fun b : ℝ =>
      qA b * (qA b - 1) * ((k / 2) ^ 2 / (qA b) ^ 2 * (Real.pi * (N b / D b))))
      (k + 1) := hcoeff.mul (hfactor.mul hbase)
  have hfun : (fun b : ℝ => planarWirtingerTargetReal k b) =
      (fun b => qA b * (qA b - 1) *
        ((k / 2) ^ 2 / (qA b) ^ 2 * (Real.pi * (N b / D b)))) := by
    funext b
    simp only [planarWirtingerTargetReal, planarRieszCoefficientReal, qA, N, D]
    ring
  simpa only [hfun] using htarget

private theorem planarWirtingerTargetReal_eq (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β =
      (planarWirtingerTargetReal k β : ℂ) := by
  have hGauss : (planarRieszCoefficientReal k β : ℂ) =
      DOZZ.planarGaussConstant k β := by
    simpa [planarRieszCoefficientReal] using
      positive_riesz_coefficient_eq_planarGaussConstant k β hk hβ hβ₂
  let a : ℝ := (2 + k - β) / 2
  have hcast : ((2 + (k : ℂ) - (β : ℂ)) / 2) *
      ((2 + (k : ℂ) - (β : ℂ)) / 2 - 1) =
        Complex.ofReal (a * (a - 1)) := by
    dsimp [a]
    push_cast
    ring
  calc
    _ = Complex.ofReal (a * (a - 1)) * DOZZ.planarGaussConstant k β := by rw [hcast]
    _ = Complex.ofReal (a * (a - 1)) *
        Complex.ofReal (planarRieszCoefficientReal k β) := by rw [← hGauss]
    _ = Complex.ofReal (a * (a - 1) * planarRieszCoefficientReal k β) :=
      (Complex.ofReal_mul _ _).symm
    _ = Complex.ofReal (planarWirtingerTargetReal k β) := by
      apply congrArg Complex.ofReal
      dsimp [a, planarWirtingerTargetReal, planarRieszCoefficientReal]

private theorem planarWirtinger_integral_at_one_value_all (k β : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) :
    (k / 2) * (k / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) =
      ((2 + k - β) / 2) * ((2 + k - β) / 2 - 1) *
        DOZZ.planarGaussConstant k β := by
  by_cases hβne : β ≠ k + 1
  · exact planarWirtinger_integral_at_one_value k β hk hβ hβ₂ hβne
  · have hβeq : β = k + 1 := by
      by_contra h
      exact hβne h
    subst β
    have hk1 : k < 1 := by linarith
    let l : Filter ℝ := 𝓝[≠] (k + 1)
    let L : ℝ → ℂ := fun b =>
      ((k / 2) * (k / 2 - 1) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k b 1 u)
    let R : ℝ → ℂ := fun b => (planarWirtingerTargetReal k b : ℂ)
    have hDCT := planarWirtinger_integral_tendsto_parameter k (k + 1) hk
      (by linarith) (by linarith)
    have hleftFull : Tendsto L (𝓝 (k + 1))
        (𝓝 (L (k + 1))) := by
      have hconst : Tendsto (fun _ : ℝ =>
          (((k / 2) * (k / 2 - 1) : ℝ) : ℂ)) (𝓝 (k + 1))
          (𝓝 (((k / 2) * (k / 2 - 1) : ℝ) : ℂ)) := tendsto_const_nhds
      have h := hconst.mul hDCT
      simpa [L] using h
    have hleft : Tendsto L l (𝓝 (L (k + 1))) := hleftFull.mono_left nhdsWithin_le_nhds
    have hTcont := planarWirtingerTargetReal_continuousAt k hk hk1
    have hrightFull : Tendsto R (𝓝 (k + 1)) (𝓝 (R (k + 1))) := by
      exact Complex.continuous_ofReal.continuousAt.tendsto.comp hTcont.tendsto
    have hright : Tendsto R l (𝓝 (R (k + 1))) := hrightFull.mono_left nhdsWithin_le_nhds
    have hinterval : ∀ᶠ b : ℝ in l, k < b ∧ b < 2 := by
      have hlow : ∀ᶠ b : ℝ in l, k < b :=
        (eventually_gt_nhds (show k < k + 1 by linarith)).filter_mono nhdsWithin_le_nhds
      have hhigh : ∀ᶠ b : ℝ in l, b < 2 :=
        (eventually_lt_nhds (show k + 1 < 2 by linarith)).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlow, hhigh] with b hb₁ hb₂
      exact ⟨hb₁, hb₂⟩
    have heq : L =ᶠ[l] R := by
      filter_upwards [hinterval, self_mem_nhdsWithin] with b hb hbe
      have hvalue := planarWirtinger_integral_at_one_value k b hk hb.1 hb.2
        (by simpa using hbe)
      have htarget := planarWirtingerTargetReal_eq k b hk hb.1 hb.2
      simpa [L, R] using hvalue.trans htarget
    have hlim : L (k + 1) = R (k + 1) :=
      tendsto_nhds_unique (hleft.congr' heq) hright
    have hlim' : ((k : ℂ) / 2) * ((k : ℂ) / 2 - 1) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k (k + 1) 1 u) =
          (planarWirtingerTargetReal k (k + 1) : ℂ) := by
      have hh := hlim
      change ((k / 2) * (k / 2 - 1) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k (k + 1) 1 u) =
          (planarWirtingerTargetReal k (k + 1) : ℂ) at hh
      push_cast at hh
      exact hh
    have htarget := planarWirtingerTargetReal_eq k (k + 1) hk
      (by linarith) (by linarith)
    exact hlim'.trans htarget.symm

private theorem planarWirtingerKernel_rotated_scale (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (ξ z : ℂ) (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r)
    (hz : ξ * (r : ℂ) = z) (v : ℂ) :
    DOZZ.planarWirtingerKernel k β z (ξ * (r • v)) =
      (ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
        DOZZ.planarWirtingerKernel k β 1 v := by
  have hβpos : 0 < β := lt_trans hk hβ
  by_cases hv0 : v = 0
  · subst v
    simp [DOZZ.planarWirtingerKernel, Real.zero_rpow, ne_of_gt hβpos]
  · by_cases hv1 : v = 1
    · subst v
      simp [DOZZ.planarWirtingerKernel, hz, Real.zero_rpow, ne_of_gt hk]
    · have hξ0 : ξ ≠ 0 := by
        intro h
        simp [h] at hξ
      have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      have hnormV : ‖ξ * (r • v)‖ = r * ‖v‖ := by
        rw [norm_mul, hξ, one_mul, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      have hdiff : ξ * (r • v) - ξ * (r : ℂ) = ξ * (r : ℂ) * (v - 1) := by
        change ξ * ((r : ℂ) * v) - ξ * (r : ℂ) = ξ * (r : ℂ) * (v - 1)
        ring
      have hnormDiff : ‖ξ * (r • v) - z‖ = r * ‖v - 1‖ := by
        calc
          ‖ξ * (r • v) - z‖ = ‖ξ * (r • v) - ξ * (r : ℂ)‖ := by rw [hz]
          _ = ‖ξ * (r : ℂ) * (v - 1)‖ := congrArg norm hdiff
          _ = r * ‖v - 1‖ := by
            rw [norm_mul, norm_mul, hξ, one_mul, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos hr]
      have hden : (z - ξ * (r • v)) ^ 2 = ξ ^ 2 * (r : ℂ) ^ 2 * (1 - v) ^ 2 := by
        calc
          (z - ξ * (r • v)) ^ 2 = (ξ * (r : ℂ) - ξ * (r • v)) ^ 2 := by rw [hz]
          _ = (ξ * (r : ℂ) * (1 - v)) ^ 2 := by
            congr 2
            change ξ * (r : ℂ) - ξ * ((r : ℂ) * v) = ξ * (r : ℂ) * (1 - v)
            ring
          _ = ξ ^ 2 * (r : ℂ) ^ 2 * (1 - v) ^ 2 := by ring
      have hnumPow : (r * ‖v - 1‖) ^ k = r ^ k * ‖v - 1‖ ^ k :=
        Real.mul_rpow hr.le (norm_nonneg (v - 1))
      have hdenPow : (r * ‖v‖) ^ β = r ^ β * ‖v‖ ^ β :=
        Real.mul_rpow hr.le (norm_nonneg v)
      have hrpow : r ^ k = r ^ (k - β - 2) * (r ^ β * r ^ 2) := by
        calc
          r ^ k = r ^ ((k - β - 2) + (β + 2)) := by
            exact congrArg (fun x : ℝ => r ^ x) (by ring)
          _ = r ^ (k - β - 2) * r ^ (β + 2) := Real.rpow_add hr _ _
          _ = r ^ (k - β - 2) * (r ^ β * r ^ 2) := by
            rw [Real.rpow_add hr β 2]
            rw [← Real.rpow_natCast r 2]
            rfl
      rw [DOZZ.planarWirtingerKernel, DOZZ.planarWirtingerKernel,
        hnormDiff, hnormV, hden, hnumPow, hdenPow]
      have hnormvpos : 0 < ‖v‖ ^ β :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr hv0) β
      have hnormdiffpos : 0 < ‖v - 1‖ ^ k :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hv1)) k
      have hxi2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ0
      have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
      have hrβ : r ^ β ≠ 0 := (Real.rpow_pos_of_pos hr β).ne'
      have hcv : (1 - v) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hv1))
      field_simp [hxi2, hr2, hrβ, hnormvpos.ne', hcv, hnormdiffpos.ne']
      rw [hrpow]
      push_cast
      ring

private theorem planarWirtingerKernel_integral_scale (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (ξ z : ℂ) (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r)
    (hz : ξ * (r : ℂ) = z) :
    (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
      (ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) := by
  let g : ℂ → ℂ := fun u => DOZZ.planarWirtingerKernel k β z (ξ * u)
  have hrotation : (∫ u : ℂ, g u) =
      (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) := by
    change (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z (ξ * u)) = _
    let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
    simpa only [rotation_apply] using
      (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
        ((rotation c).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding)
        (fun u : ℂ => DOZZ.planarWirtingerKernel k β z u)
  have hscaling : (∫ u : ℂ, g (r • u)) =
      (((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) * (∫ u : ℂ, g u) := by
    have h := Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)
    simpa only [Complex.finrank_real_complex, Complex.real_smul] using h
  have hpoint : (fun u : ℂ => g (r • u)) = fun u =>
      (ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
        DOZZ.planarWirtingerKernel k β 1 u := by
    funext u
    exact planarWirtingerKernel_rotated_scale k β hk hβ ξ z hξ r hr hz u
  rw [hpoint, integral_const_mul] at hscaling
  rw [hrotation] at hscaling
  have hmul := congrArg (fun x : ℂ => (r ^ 2 : ℝ) * x) hscaling
  have hrpow : r ^ 2 * r ^ (k - β - 2) = r ^ (k - β) := by
    rw [← Real.rpow_natCast r 2]
    calc
      _ = r ^ (2 + (k - β - 2)) := (Real.rpow_add hr 2 (k - β - 2)).symm
      _ = _ := by congr 1; ring
  have hrpowC : ((r ^ 2 : ℝ) : ℂ) * (r ^ (k - β - 2) : ℝ) =
      (r ^ (k - β) : ℝ) := by
    calc
      _ = ((r ^ 2 * r ^ (k - β - 2) : ℝ) : ℂ) :=
        (Complex.ofReal_mul _ _).symm
      _ = _ := by rw [hrpow]
  have hleft : (r ^ 2 : ℝ) *
      ((ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) =
      (ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) := by
    calc
      _ = (ξ ^ 2)⁻¹ * ((r ^ 2 : ℝ) * (r ^ (k - β - 2) : ℝ)) *
          (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u) := by ring
      _ = _ := by rw [hrpowC]
  have hr2 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_ne_zero 2 hr.ne')
  have hright : ((r ^ 2 : ℝ) : ℂ) *
      ((((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u)) =
      (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) := by
    calc
      _ = (((r ^ 2 : ℝ) : ℂ) * (((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ)) *
          (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) := by
            exact (mul_assoc _ _ _).symm
      _ = (((r ^ 2 : ℝ) * (r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) := by
            rw [← Complex.ofReal_mul]
      _ = _ := by
        rw [mul_inv_cancel₀ (pow_ne_zero 2 hr.ne')]
        simp
  calc
    (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
        ((r ^ 2 : ℝ) : ℂ) * ((((r ^ 2 : ℝ)⁻¹ : ℝ) : ℂ) *
          (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u)) := by rw [hright]
    _ = ((r ^ 2 : ℝ) : ℂ) * ((ξ ^ 2)⁻¹ * (r ^ (k - β - 2) : ℝ) *
          (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := hmul.symm
    _ = _ := hleft

theorem planar_wirtinger_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, z ≠ 0 → Integrable (DOZZ.planarWirtingerKernel k β z) volume ∧
      (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
        ((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
          (‖z‖ ^ (2 + k - β) : ℝ) / z ^ 2 *
            DOZZ.planarGaussConstant k β := by
  intro z hz
  constructor
  · exact (integrable_planarWirtingerKernel_iff k β hk z hz).2 ⟨hβ, hβ₂⟩
  · let r : ℝ := ‖z‖
    let ξ : ℂ := z / (r : ℂ)
    have hr : 0 < r := by dsimp [r]; exact norm_pos_iff.mpr hz
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hξ : ‖ξ‖ = 1 := by
      dsimp [ξ]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [r]
      exact div_self (norm_ne_zero_iff.mpr hz)
    have hξ0 : ξ ≠ 0 := by
      intro h
      simp [h] at hξ
    have hξr : ξ * (r : ℂ) = z := by
      dsimp [ξ]
      field_simp [hrC]
    have hzsq : z ^ 2 = ξ ^ 2 * (r : ℂ) ^ 2 := by
      rw [← hξr]
      ring
    have hrpow : r ^ (2 + k - β) = r ^ 2 * r ^ (k - β) := by
      rw [← Real.rpow_natCast r 2]
      calc
        r ^ (2 + k - β) = r ^ (2 + (k - β)) := by congr 1; ring
        _ = r ^ (2 : ℝ) * r ^ (k - β) := Real.rpow_add hr 2 (k - β)
    have hrpowC : (r ^ (2 + k - β) : ℝ) =
        (r ^ 2 : ℝ) * r ^ (k - β) := by
      exact hrpow
    have hfactor : (ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) =
        (r ^ (2 + k - β) : ℝ) / z ^ 2 := by
      rw [hrpowC, hzsq]
      have hξ2 : ξ ^ 2 ≠ 0 := pow_ne_zero 2 hξ0
      have hr2 : (r : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hrC
      field_simp [hξ2, hr2]
      rw [← Complex.ofReal_pow]
      rw [← Complex.ofReal_mul]
    have hscale := planarWirtingerKernel_integral_scale k β hk hβ
      ξ z hξ r hr hξr
    have hbase := planarWirtinger_integral_at_one_value_all k β hk hβ hβ₂
    have hvalue : (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
        (∫ u : ℂ, DOZZ.planarWirtingerKernel k β z u) =
        ((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
          (r ^ (2 + k - β) : ℝ) / z ^ 2 *
            DOZZ.planarGaussConstant k β := by
      calc
        _ = (k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
            ((ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ) *
              (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := by rw [hscale]
        _ = ((ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ)) *
            ((k / 2 : ℝ) * (k / 2 - 1 : ℝ) *
              (∫ u : ℂ, DOZZ.planarWirtingerKernel k β 1 u)) := by ring
        _ = ((ξ ^ 2)⁻¹ * (r ^ (k - β) : ℝ)) *
            (((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
              DOZZ.planarGaussConstant k β) := by
                push_cast
                rw [hbase]
        _ = _ := by rw [hfactor]; ring
    simpa [r] using hvalue

end DOZZ.Proofs
