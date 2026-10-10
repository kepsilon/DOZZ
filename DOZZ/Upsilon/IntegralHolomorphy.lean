/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.IntegralBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# DOZZ Upsilon integral holomorphy

Differentiation under the defining integral on its strip of convergence.
-/

@[expose] public section

namespace DOZZ.Proofs

noncomputable section

open Set MeasureTheory Filter Topology

private lemma deriv_real_restrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    deriv (fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
  funext t
  exact (hF t).hasDerivAt.comp_ofReal.deriv

private def zDerivNumComplex (γ : ℝ) (w t : ℂ) : ℂ :=
  -2 * w * Complex.exp (-t) * complexDenom γ t +
    t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))

private def zDerivNum (γ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  zDerivNumComplex γ w (t : ℂ)

private def zDerivNumJoint (γ : ℝ) (p : ℂ × ℝ) : ℂ :=
  zDerivNum γ p.1 p.2

private lemma zDerivNumJoint_contDiff (γ : ℝ) :
    ContDiff ℝ 3 (zDerivNumJoint γ) := by
  have hF : ContDiff ℂ 3 (fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) := by
    fun_prop [zDerivNumComplex, complexDenom]
  have hF' : ContDiff ℝ 3 (fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) :=
    hF.restrict_scalars ℝ
  have hPair : ContDiff ℝ 3 (fun p : ℂ × ℝ => (p.1, (p.2 : ℂ))) := by
    exact contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
  change ContDiff ℝ 3 ((fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) ∘
    fun p : ℂ × ℝ => (p.1, (p.2 : ℂ)))
  exact hF'.comp hPair

private lemma zDerivNum_third_continuous (γ : ℝ) :
    Continuous (fun p : ℂ × ℝ =>
      iteratedDeriv 3 (zDerivNum γ p.1) p.2) := by
  have hJ := zDerivNumJoint_contDiff γ
  have hF : Continuous (fun p : ℂ × ℝ =>
      iteratedFDeriv ℝ 3 (zDerivNumJoint γ) p) :=
    hJ.continuous_iteratedFDeriv (by norm_num)
  have hEq : (fun p : ℂ × ℝ =>
      iteratedDeriv 3 (zDerivNum γ p.1) p.2) =
    (fun p : ℂ × ℝ =>
      iteratedFDeriv ℝ 3 (zDerivNumJoint γ) p
        (fun _ : Fin 3 => (0, (1 : ℝ)))) := by
    funext p
    let line : ℝ → ℂ × ℝ := fun t => (p.1, t)
    have hline : HasDerivAt line (0, (1 : ℝ)) p.2 := by
      simpa [line] using
        (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hlineD : deriv line = fun _ => (0, (1 : ℝ)) := by
      funext t
      exact ((hasDerivAt_const t p.1).prodMk (hasDerivAt_id t)).deriv
    have hline2 : iteratedDeriv 2 line p.2 = 0 := by
      rw [iteratedDeriv_succ]
      rw [show iteratedDeriv 1 line = deriv line by simp, hlineD]
      simp
    have hline3 : iteratedDeriv 3 line p.2 = 0 := by
      rw [iteratedDeriv_succ]
      rw [show iteratedDeriv 2 line = fun _ => 0 by
        funext t
        rw [iteratedDeriv_succ]
        rw [show iteratedDeriv 1 line = deriv line by simp, hlineD]
        simp]
      simp
    have hcomp := iteratedDeriv_vcomp_three
      (hg := hJ.contDiffAt)
      (hf := (by fun_prop : ContDiffAt ℝ 3 line p.2))
    rw [hline2, hline3] at hcomp
    have hcross₁ :
        iteratedFDeriv ℝ 2 (zDerivNumJoint γ) p ![0, (0, (1 : ℝ))] = 0 := by
      apply ContinuousMultilinearMap.map_coord_zero _ 0
      simp
    have hcross₂ :
        iteratedFDeriv ℝ 2 (zDerivNumJoint γ) p ![(0, (1 : ℝ)), 0] = 0 := by
      apply ContinuousMultilinearMap.map_coord_zero _ 1
      simp
    simp only [line, hlineD] at hcomp
    rw [hcross₁, hcross₂] at hcomp
    simpa [line, Function.comp_def, zDerivNumJoint] using hcomp
  rw [hEq]
  fun_prop

private lemma zDerivNumComplex_deriv_eq (γ : ℝ) (w : ℂ) :
    deriv (zDerivNumComplex γ w) = fun t =>
      -2 * w * Complex.exp (-t) *
          ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)) +
            (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) * Complex.cosh (t / (γ : ℂ))) +
        2 * w * Complex.exp (-t) * complexDenom γ t +
    Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) +
        t * w / 2 * (Complex.cosh (w * (t / 2)) ^ 2 + Complex.sinh (w * (t / 2)) ^ 2) := by
  funext t
  change deriv (fun t : ℂ =>
      -2 * w * Complex.exp (-t) *
          (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) +
        t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) t = _
  simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
  ring_nf

private lemma zDerivNumComplex_deriv_zero (γ : ℝ) (w : ℂ) :
    deriv (zDerivNumComplex γ w) 0 = 0 := by
  rw [zDerivNumComplex_deriv_eq]
  simp [complexDenom]

private lemma zDerivNumComplex_iteratedDeriv_two_zero {γ : ℝ} (hγ : 0 < γ) (w : ℂ) :
    iteratedDeriv 2 (zDerivNumComplex γ w) 0 = 0 := by
  rw [iteratedDeriv_succ]
  rw [show iteratedDeriv 1 (zDerivNumComplex γ w) = deriv (zDerivNumComplex γ w) by simp]
  rw [zDerivNumComplex_deriv_eq]
  simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hγ)
  field_simp [hγC]
  ring

private lemma zDerivNumContDiff (γ : ℝ) (w : ℂ) :
    ContDiff ℝ 3 (zDerivNum γ w) := by
  have hC : ContDiff ℂ 3 (zDerivNumComplex γ w) := by
    fun_prop [zDerivNumComplex, complexDenom]
  change ContDiff ℝ 3 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ))
  exact hC.restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff

private lemma zDerivNum_zero (γ : ℝ) (w : ℂ) : zDerivNum γ w 0 = 0 := by
  simp [zDerivNum, zDerivNumComplex, complexDenom]

private lemma zDerivNum_deriv_zero (γ : ℝ) (w : ℂ) : deriv (zDerivNum γ w) 0 = 0 := by
  have hF : Differentiable ℂ (zDerivNumComplex γ w) :=
    (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 (zDerivNumComplex γ w)).differentiable
      (by norm_num)
  change deriv (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) 0 = 0
  rw [deriv_real_restrict _ hF]
  exact zDerivNumComplex_deriv_zero γ w

private lemma zDerivNum_iteratedDeriv_two_zero {γ : ℝ} (hγ : 0 < γ) (w : ℂ) :
    iteratedDeriv 2 (zDerivNum γ w) 0 = 0 := by
  change iteratedDeriv 2 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) 0 = 0
  rw [iteratedDeriv_succ]
  have hF : Differentiable ℂ (zDerivNumComplex γ w) :=
    (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 (zDerivNumComplex γ w)).differentiable
      (by norm_num)
  have hfirst : iteratedDeriv 1 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) =
      fun t : ℝ => deriv (zDerivNumComplex γ w) (t : ℂ) := by
    simpa [iteratedDeriv_succ] using deriv_real_restrict _ hF
  rw [hfirst]
  have hC2 : ContDiff ℂ 2 (zDerivNumComplex γ w) := by
    exact (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 3
      (zDerivNumComplex γ w)).of_le (by norm_num)
  have hF' : Differentiable ℂ (deriv (zDerivNumComplex γ w)) := by
    simpa [iteratedDeriv_succ] using hC2.differentiable_iteratedDeriv' 1
  have hsecond := (hF' (0 : ℂ)).hasDerivAt.comp_ofReal.deriv
  calc
    deriv (fun t : ℝ => deriv (zDerivNumComplex γ w) (t : ℂ)) 0 =
        deriv (deriv (zDerivNumComplex γ w)) 0 := hsecond
    _ = iteratedDeriv 2 (zDerivNumComplex γ w) 0 := by
      rw [iteratedDeriv_succ]
      simp
    _ = 0 := zDerivNumComplex_iteratedDeriv_two_zero hγ w

private lemma zDerivNum_iteratedDerivWithin_one_zero (γ : ℝ) (w : ℂ) :
    iteratedDerivWithin 1 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 1 (zDerivNum γ w) 0 :=
    (zDerivNumContDiff γ w).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  simpa [iteratedDeriv_succ] using zDerivNum_deriv_zero γ w

private lemma zDerivNum_iteratedDerivWithin_two_zero {γ : ℝ} (hγ : 0 < γ)
    (w : ℂ) : iteratedDerivWithin 2 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 2 (zDerivNum γ w) 0 :=
    (zDerivNumContDiff γ w).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  exact zDerivNum_iteratedDeriv_two_zero hγ w

private lemma zDerivNum_taylorWithinEval_zero {γ : ℝ} (hγ : 0 < γ) (w : ℂ)
    (t : ℝ) : taylorWithinEval (zDerivNum γ w) 2 (Icc 0 1) 0 t = 0 := by
  rw [taylor_within_apply]
  have h0 : iteratedDerivWithin 0 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
    simpa using zDerivNum_zero γ w
  have h1 := zDerivNum_iteratedDerivWithin_one_zero γ w
  have h2 := zDerivNum_iteratedDerivWithin_two_zero hγ w
  simp [Finset.sum_range_succ, h0, h1, h2]

private lemma exists_zDerivNum_taylor_bound {γ : ℝ} (hγ : 0 < γ)
    (w₀ : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ t ∈ Icc 0 1,
      ‖zDerivNum γ w t‖ ≤ C * t ^ 3 := by
  let K : Set (ℂ × ℝ) := Metric.closedBall w₀ r ×ˢ Icc 0 1
  let derivativeNorm : ℂ × ℝ → ℝ := fun p =>
    ‖iteratedDeriv 3 (zDerivNum γ p.1) p.2‖
  have hK : IsCompact K := by
    change IsCompact (Metric.closedBall w₀ r ×ˢ Icc (0 : ℝ) 1)
    exact IsCompact.prod (isCompact_closedBall w₀ r) isCompact_Icc
  have hcont : ContinuousOn derivativeNorm K :=
    (zDerivNum_third_continuous γ).norm.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.bddAbove_image hcont
  let C : ℝ := max C₀ 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro w hw t ht
  have hderiv : ∀ y ∈ Icc (0 : ℝ) 1,
      ‖iteratedDerivWithin 3 (zDerivNum γ w) (Icc 0 1) y‖ ≤ C := by
    intro y hy
    have hEq := iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1))
      ((zDerivNumContDiff γ w).contDiffAt) hy
    rw [hEq]
    apply le_trans _ (le_max_left C₀ 0)
    have hp : (w, y) ∈ K := ⟨hw, hy⟩
    have himage : derivativeNorm (w, y) ∈ derivativeNorm '' K :=
      ⟨(w, y), hp, rfl⟩
    exact hC₀ himage
  have hTaylor := taylor_mean_remainder_bound
    (f := zDerivNum γ w) (a := 0) (b := 1) (C := C) (x := t) (n := 2)
    (by norm_num) (zDerivNumContDiff γ w).contDiffOn
    ht hderiv
  rw [zDerivNum_taylorWithinEval_zero hγ w t] at hTaylor
  norm_num at hTaylor
  have ht0 : 0 ≤ t := ht.1
  have hnonneg : 0 ≤ C * t ^ 3 := mul_nonneg (le_max_right _ _)
    (pow_nonneg ht0 _)
  linarith only [hTaylor, hnonneg]

private def upsilonLogIntegrandDeriv (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  zDerivNum γ ((Q γ / 2 : ℂ) - z) t /
    ((realDenom γ t : ℂ) * (t : ℂ))

private lemma deriv_upsilonLogIntegrand {γ : ℝ} {t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) (z : ℂ) :
    deriv (fun z : ℂ => upsilonLogIntegrand γ z t) z =
      upsilonLogIntegrandDeriv γ z t := by
  have hD : (realDenom γ t : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hγ)
  have hS₁ : Complex.sinh ((t : ℂ) * (γ : ℂ) / 4) ≠ 0 := by
    rw [show (t : ℂ) * (γ : ℂ) / 4 = ((t * γ / 4 : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
  have hS₂ : Complex.sinh ((t : ℂ) / (γ : ℂ)) ≠ 0 := by
    rw [show (t : ℂ) / (γ : ℂ) = ((t / γ : ℝ) : ℂ) by push_cast; rfl]
    rw [← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
  simp (disch := fun_prop) [upsilonLogIntegrand, upsilonLogIntegrandDeriv,
    zDerivNum, zDerivNumComplex, realDenom, complexDenom,
    deriv_csinh, deriv_cexp]
  field_simp [hD, htC, hγC, hS₁, hS₂]
  ring_nf

private lemma upsilonLogIntegrandDeriv_norm_le_of_taylor {γ : ℝ}
    (hγ : 0 < γ) (z : ℂ) (C : ℝ) (hC : 0 ≤ C)
    {t : ℝ} (ht : 0 < t) (_ht1 : t ≤ 1)
    (hTaylor : ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3) :
    ‖upsilonLogIntegrandDeriv γ z t‖ ≤ 4 * C := by
  have hdenPos := realDenom_pos hγ ht
  have hdenQuad := realDenom_ge_quadratic hγ ht
  have hdenT : 0 < realDenom γ t * t := mul_pos hdenPos ht
  have hdenTLower : t ^ 3 / 4 ≤ realDenom γ t * t := by
    calc
      t ^ 3 / 4 = (t ^ 2 / 4) * t := by ring
      _ ≤ realDenom γ t * t := mul_le_mul_of_nonneg_right hdenQuad ht.le
  have hnormDen :
      ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  rw [upsilonLogIntegrandDeriv, norm_div, hnormDen]
  rw [div_le_iff₀ hdenT]
  have h4C : 0 ≤ 4 * C := mul_nonneg (by norm_num) hC
  have hprod := mul_le_mul_of_nonneg_left hdenTLower h4C
  have hprod' : C * t ^ 3 ≤ 4 * C * (realDenom γ t * t) := by
    linarith only [hprod]
  exact le_trans hTaylor hprod'

private lemma upsilonLogIntegrandDeriv_norm_le_tail {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) {t : ℝ} (ht : 1 ≤ t) :
    ‖upsilonLogIntegrandDeriv γ z t‖ ≤
      2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
  let w : ℂ := (Q γ / 2 : ℂ) - z
  let δ : ℝ := Q γ / 2 - |w.re|
  have hQpos : 0 < Q γ := by unfold Q; positivity
  have hstrip : |w.re| < Q γ / 2 := by
    apply (abs_lt).2
    constructor <;> dsimp [w] <;> simp <;> linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hdenPos := realDenom_pos hγ (by linarith : 0 < t)
  have hdenLower := realDenom_ge_tail_exp hγ ht
  have hK : 0 < tailConst γ := tailConst_pos hγ
  have hdenom :
      ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hdenPos, abs_of_pos (by linarith : 0 < t)]
  have hcomplexDenom : complexDenom γ (t : ℂ) = (realDenom γ t : ℂ) := by
    simp [complexDenom, realDenom]
  have hcomplexDenomNorm : ‖complexDenom γ (t : ℂ)‖ = realDenom γ t := by
    rw [hcomplexDenom, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
  have hlinear :
      ‖-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
          ((realDenom γ t : ℂ) * (t : ℂ))‖ ≤
        2 * ‖w‖ * Real.exp (-t) := by
    have hexp : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
      simp [Complex.norm_exp]
    calc
      _ = (2 * ‖w‖ * Real.exp (-t) * realDenom γ t) /
          (realDenom γ t * t) := by
            rw [norm_div, hdenom]
            simp [hcomplexDenomNorm, hexp]
      _ ≤ 2 * ‖w‖ * Real.exp (-t) := by
        have htpos : 0 < t := by linarith
        have hcoef : 0 ≤ 2 * ‖w‖ * Real.exp (-t) := by positivity
        have hDt : realDenom γ t ≤ realDenom γ t * t := by
          simpa using mul_le_mul_of_nonneg_left ht hdenPos.le
        rw [div_le_iff₀ (mul_pos hdenPos htpos)]
        exact mul_le_mul_of_nonneg_left hDt hcoef
  have hnonzero : (realDenom γ t : ℂ) * (t : ℂ) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hdenPos.ne')
      (Complex.ofReal_ne_zero.mpr (by linarith : t ≠ 0))
  have hnonlinear :
      ‖(Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) /
          (realDenom γ t : ℂ)‖ ≤
        (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
    have hSinh : ‖Complex.sinh (w * (t / 2))‖ ≤ Real.exp (|w.re| * (t / 2)) := by
      calc
        _ ≤ Real.exp |(w * (t / 2)).re| := complex_sinh_norm_le_exp_abs_re _
        _ = Real.exp (|w.re| * (t / 2)) := by
          have hre : (w * (t / 2)).re = w.re * (t / 2) := by simp
          rw [hre, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
    have hCosh : ‖Complex.cosh (w * (t / 2))‖ ≤ Real.exp (|w.re| * (t / 2)) := by
      calc
        _ ≤ Real.exp |(w * (t / 2)).re| := complex_cosh_norm_le_exp_abs_re _
        _ = Real.exp (|w.re| * (t / 2)) := by
          have hre : (w * (t / 2)).re = w.re * (t / 2) := by simp
          rw [hre, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
    have hprod :
        ‖Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))‖ ≤
          Real.exp (|w.re| * t) := by
      calc
        _ = ‖Complex.sinh (w * (t / 2))‖ * ‖Complex.cosh (w * (t / 2))‖ := norm_mul _ _
        _ ≤ Real.exp (|w.re| * (t / 2)) * Real.exp (|w.re| * (t / 2)) :=
          mul_le_mul hSinh hCosh (norm_nonneg _) (Real.exp_pos _).le
        _ = Real.exp (|w.re| * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
    have hden :
        (tailConst γ)⁻¹ * Real.exp (-δ * t) * realDenom γ t ≥
          Real.exp (|w.re| * t) := by
      have hfactor :
          (tailConst γ)⁻¹ * Real.exp (-δ * t) *
              (tailConst γ * Real.exp (Q γ / 2 * t)) = Real.exp (|w.re| * t) := by
        calc
          _ = ((tailConst γ)⁻¹ * tailConst γ) *
              (Real.exp (-δ * t) * Real.exp (Q γ / 2 * t)) := by ring
          _ = Real.exp (|w.re| * t) := by
            rw [inv_mul_cancel₀ hK.ne', ← Real.exp_add]
            rw [show -δ * t + Q γ / 2 * t = |w.re| * t by dsimp [δ]; ring]
            simp
      calc
        _ ≥ (tailConst γ)⁻¹ * Real.exp (-δ * t) *
            (tailConst γ * Real.exp (Q γ / 2 * t)) :=
              mul_le_mul_of_nonneg_left hdenLower (by positivity)
        _ = _ := hfactor
    have hdiv :
        Real.exp (|w.re| * t) / realDenom γ t ≤
          (tailConst γ)⁻¹ * Real.exp (-δ * t) :=
      (div_le_iff₀ hdenPos).2 hden
    calc
      _ = ‖Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))‖ /
          realDenom γ t := rfl
      _ ≤ Real.exp (|w.re| * t) / realDenom γ t :=
        div_le_div_of_nonneg_right hprod hdenPos.le
      _ ≤ _ := hdiv
  have hsum := norm_add_le
    (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
      ((realDenom γ t : ℂ) * (t : ℂ)))
    (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) /
      (realDenom γ t : ℂ))
  have hEq : upsilonLogIntegrandDeriv γ z t =
      (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
          ((realDenom γ t : ℂ) * (t : ℂ))) +
        (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) /
          (realDenom γ t : ℂ)) := by
    rw [upsilonLogIntegrandDeriv, zDerivNum, zDerivNumComplex]
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hDC : (realDenom γ t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hdenPos.ne'
    field_simp [htC, hDC]
    have hqw : (Q γ : ℂ) - 2 * z = 2 * w := by
      dsimp [w]
      ring
    rw [hqw]
    have harg : (2 * w) * (t : ℂ) / 2 ^ 2 = (t : ℂ) * w / 2 := by ring
    rw [harg]
    ring
  rw [hEq]
  calc
    _ ≤ 2 * ‖w‖ * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
          exact hsum.trans (add_le_add hlinear hnonlinear)
    _ = _ := by simp [w, δ]

private lemma upsilonLogIntegrandDeriv_aestronglyMeasurable (γ : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrandDeriv γ z t) volume := by
  have hnum : Measurable (fun t : ℝ => zDerivNum γ ((Q γ / 2 : ℂ) - z) t) := by
    fun_prop [zDerivNum, zDerivNumComplex, complexDenom]
  have hden : Measurable (fun t : ℝ =>
      (realDenom γ t : ℂ) * (t : ℂ)) := by
    fun_prop [realDenom]
  exact (hnum.div hden).aestronglyMeasurable

private lemma upsilonLog_hasDerivAt {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (z₀ : ℂ) (hz₀ : 0 < z₀.re) (hzQ : z₀.re < Q γ) :
    HasDerivAt (fun z : ℂ => upsilonLog γ z)
      (∫ t in Ioi (0 : ℝ), upsilonLogIntegrandDeriv γ z₀ t) z₀ := by
  let margin : ℝ := min z₀.re (Q γ - z₀.re)
  let r : ℝ := margin / 2
  let q : ℂ := (Q γ / 2 : ℂ)
  let w₀ : ℂ := q - z₀
  let W : ℝ := ‖w₀‖ + r
  let B : ℝ := (tailConst γ)⁻¹
  have hmargin : 0 < margin := by
    dsimp [margin]
    exact lt_min hz₀ (sub_pos.mpr hzQ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hQpos : 0 < Q γ := by unfold Q; positivity
  have hqre : q.re = Q γ / 2 := by simp [q]
  have hWnonneg : 0 ≤ W := by dsimp [W]; positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_of_lt (inv_pos.mpr (tailConst_pos hγ))
  obtain ⟨C, hC, hTaylor⟩ := exists_zDerivNum_taylor_bound hγ w₀ r
  let A : ℝ := 4 * C * Real.exp 1 + 2 * W
  let bound : ℝ → ℝ := fun t => A * Real.exp (-t) + B * Real.exp (-r * t)
  have hA_nonneg : 0 ≤ A := by dsimp [A, W]; positivity
  have hA_lower : 2 * W ≤ A := by
    dsimp [A]
    linarith only [mul_nonneg hC (Real.exp_pos 1).le]
  have hs : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hz_near (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      |z.re - z₀.re| < r := by
    have hdist : dist z z₀ < r := Metric.mem_ball.mp hz
    have hre := (Complex.abs_re_le_norm (z - z₀)).trans_lt (by
      simpa [dist_eq_norm] using hdist)
    simpa [Complex.sub_re] using hre
  have hz_real_bounds (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      r < z.re ∧ z.re < Q γ - r := by
    have hc := hz_near z hz
    have hc' := abs_lt.mp hc
    have hmleft : margin ≤ z₀.re := min_le_left _ _
    have hmright : margin ≤ Q γ - z₀.re := min_le_right _ _
    constructor
    · dsimp [r] at hc' ⊢
      dsimp [margin] at hmleft
      linarith
    · dsimp [r] at hc' ⊢
      dsimp [margin] at hmright
      linarith
  have hw_re_margin (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      |Q γ / 2 - z.re| ≤ Q γ / 2 - r := by
    obtain ⟨hzlow, hzhigh⟩ := hz_real_bounds z hz
    apply abs_le.mpr
    constructor <;> linarith
  have hw_norm_bound (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      ‖(Q γ / 2 : ℂ) - z‖ ≤ W := by
    have hdist : dist z z₀ < r := Metric.mem_ball.mp hz
    have hdiff : dist ((Q γ / 2 : ℂ) - z) w₀ = dist z z₀ := by
      rw [dist_eq_norm, dist_eq_norm]
      have heq : ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z := by dsimp [w₀]; ring
      rw [heq]
      simp [norm_sub_rev]
    dsimp [W, w₀]
    calc
      ‖(Q γ / 2 : ℂ) - z‖ = ‖w₀ + (z₀ - z)‖ := by
        congr 1
        dsimp [w₀]
        ring
      _ ≤ ‖w₀‖ + ‖z₀ - z‖ := norm_add_le _ _
      _ = ‖w₀‖ + dist z z₀ := by rw [dist_eq_norm]; simp [norm_sub_rev]
      _ ≤ ‖w₀‖ + r := by linarith [hdiff]
  have hTaylor_local {z : ℂ} (hz : z ∈ Metric.ball z₀ r)
      {t : ℝ} (ht : t ∈ Icc 0 1) :
      ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3 := by
    apply hTaylor
    · have hdist : dist ((Q γ / 2 : ℂ) - z) w₀ ≤ r := by
        rw [dist_eq_norm]
        have heq : ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z := by dsimp [w₀]; ring
        rw [heq]
        have hdz : dist z z₀ < r := Metric.mem_ball.mp hz
        simpa [dist_eq_norm, norm_sub_rev] using hdz.le
      exact Metric.mem_closedBall.mpr hdist
    · exact ht
  have hparam_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r,
        ‖upsilonLogIntegrandDeriv γ z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    by_cases ht1 : t ≤ 1
    · have hTaylor' := hTaylor_local hz ⟨le_of_lt ht, ht1⟩
      have hsmall := upsilonLogIntegrandDeriv_norm_le_of_taylor hγ z C hC ht ht1 hTaylor'
      have hexp : 1 ≤ Real.exp (1 - t) := by
        exact Real.one_le_exp_iff.mpr (by linarith)
      have hexpId : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add]
        congr 1
      have hcoeff : 4 * C ≤ A * Real.exp (-t) := by
        dsimp [A]
        have h := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4 * C)
        rw [hexpId] at h
        linarith only [h, mul_nonneg hWnonneg (Real.exp_pos (-t)).le]
      calc
        _ ≤ 4 * C := hsmall
        _ ≤ A * Real.exp (-t) := hcoeff
        _ ≤ bound t := by
          dsimp [bound]
          exact le_add_of_nonneg_right (mul_nonneg hB_nonneg (Real.exp_pos _).le)
    · have ht' : 1 ≤ t := le_of_not_ge ht1
      obtain ⟨hzlow, hzhigh⟩ := hz_real_bounds z hz
      have hzQ' : z.re < Q γ := lt_of_lt_of_le hzhigh (by linarith [hr])
      have htail := upsilonLogIntegrandDeriv_norm_le_tail hγ z (lt_trans hr hzlow) hzQ' ht'
      have hδ : r ≤ Q γ / 2 - |Q γ / 2 - z.re| := by
        have habs := hw_re_margin z hz
        linarith
      have hfirst :
          2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) ≤ A * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by
          calc
            2 * ‖(Q γ / 2 : ℂ) - z‖ ≤ 2 * W := by
              exact mul_le_mul_of_nonneg_left (hw_norm_bound z hz) (by norm_num)
            _ ≤ A := hA_lower) (Real.exp_pos _).le
      have hsecond :
          B * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) ≤
            B * Real.exp (-r * t) := by
        apply mul_le_mul_of_nonneg_left _ hB_nonneg
        apply Real.exp_le_exp.mpr
        have ht0 : 0 ≤ t := by linarith
        have hmul := mul_le_mul_of_nonneg_right hδ ht0
        linarith only [hmul]
      have htail' := add_le_add hfirst hsecond
      simpa [bound, B] using htail.trans htail'
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrand γ z t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with z
    exact (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict
  have hF_int : Integrable (fun t : ℝ => upsilonLogIntegrand γ z₀ t)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (upsilonLogIntegrand_integrableOn hγ hγ2 z₀ hz₀ hzQ)
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => upsilonLogIntegrandDeriv γ z₀ t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (upsilonLogIntegrandDeriv_aestronglyMeasurable γ z₀).restrict
  have hBound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    have h₁ : IntegrableOn (fun t : ℝ => A * Real.exp (-t)) (Ioi (0 : ℝ)) := by
      change Integrable (fun t : ℝ => A * Real.exp (-t))
        (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_comm] using
        (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul A
    have h₂ : IntegrableOn (fun t : ℝ => B * Real.exp (-r * t)) (Ioi (0 : ℝ)) := by
      change Integrable (fun t : ℝ => B * Real.exp (-r * t))
        (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_comm] using
        (exp_neg_integrableOn_Ioi 0 (b := r) hr).const_mul B
    change IntegrableOn (fun t : ℝ => A * Real.exp (-t) + B * Real.exp (-r * t))
      (Ioi (0 : ℝ))
    exact h₁.add h₂
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r,
        HasDerivAt (fun z : ℂ => upsilonLogIntegrand γ z t)
          (upsilonLogIntegrandDeriv γ z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hfun : DifferentiableAt ℂ (fun z : ℂ => upsilonLogIntegrand γ z t) z := by
      fun_prop [upsilonLogIntegrand]
    simpa [deriv_upsilonLogIntegrand hγ ht z] using hfun.hasDerivAt
  obtain ⟨_, hhas⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z₀ r) hs hF_meas hF_int hF'_meas hparam_bound hBound_int hdiff
  simpa [upsilonLog] using hhas

/-- The logarithm given by the convergent integral is holomorphic on its defining strip. -/
theorem upsilonLog_differentiableOn {γ : ℝ}
    (hγ : 0 < γ) (_hγ2 : γ < 2) :
    DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ} := by
  intro z hz
  exact (upsilonLog_hasDerivAt hγ _hγ2 z hz.1 hz.2).differentiableAt.differentiableWithinAt

end

end DOZZ.Proofs

end
