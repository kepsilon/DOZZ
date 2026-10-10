/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# DOZZ Upsilon integral convergence

This module contains the integrand bounds behind the convergence and strip-regularity results
for `upsilonLog`.
-/

@[expose] public section

namespace DOZZ.Proofs

noncomputable section

open Set MeasureTheory Filter Topology

def complexDenom (γ : ℝ) (t : ℂ) : ℂ :=
  Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))

def realDenom (γ : ℝ) (t : ℝ) : ℝ :=
  Real.sinh (t * γ / 4) * Real.sinh (t / γ)

private def complexNumerator (γ : ℝ) (z : ℂ) (t : ℂ) : ℂ :=
  ((Q γ : ℂ) / 2 - z) ^ 2 * Complex.exp (-t) * complexDenom γ t -
    Complex.sinh (((Q γ : ℂ) / 2 - z) * (t / 2)) ^ 2

private def complexNumeratorDerivative (γ : ℝ) (z : ℂ) (t : ℂ) : ℂ :=
  let w := (Q γ : ℂ) / 2 - z
  w ^ 2 * Complex.exp (-t) *
      ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)) +
        (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) * Complex.cosh (t / (γ : ℂ)) -
        complexDenom γ t) -
    w * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))

private def canceledNumerator (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  complexNumerator γ z (t : ℂ)

private lemma canceledNumerator_eq_source (γ : ℝ) (z : ℂ) (t : ℝ) :
    canceledNumerator γ z t =
      (Q γ / 2 - z) ^ 2 * Real.exp (-t) *
          (Real.sinh (t * γ / 4) * Real.sinh (t / γ) : ℂ) -
        Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 := by
  simp only [canceledNumerator, complexNumerator, complexDenom,
    Complex.ofReal_sinh, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat]

private lemma complexNumerator_contDiff (γ : ℝ) (z : ℂ) :
    ContDiff ℂ 3 (complexNumerator γ z) := by
  change ContDiff ℂ 3 (fun t : ℂ =>
    ((Q γ : ℂ) / 2 - z) ^ 2 * Complex.exp (-t) *
        (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
      Complex.sinh (((Q γ : ℂ) / 2 - z) * (t / 2)) ^ 2)
  fun_prop

private lemma complexNumerator_deriv_zero (γ : ℝ) (z : ℂ) :
    deriv (complexNumerator γ z) 0 = 0 := by
  change deriv (fun t : ℂ =>
    ((Q γ : ℂ) / 2 - z) ^ 2 * Complex.exp (-t) *
        (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
      Complex.sinh (((Q γ : ℂ) / 2 - z) * (t / 2)) ^ 2) 0 = 0
  simp (disch := fun_prop) only [deriv_fun_sub, deriv_fun_mul, deriv_fun_pow, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, deriv_div_const, deriv_const', zero_div, sub_self, mul_zero,
    neg_zero, Complex.exp_zero, mul_one, deriv_cexp, deriv_neg'', mul_neg, zero_add, zero_mul,
    Complex.sinh_zero, deriv_csinh, Complex.cosh_zero, deriv_id'', one_mul, add_zero, one_div]

private lemma complexNumerator_deriv_eq (γ : ℝ) (z : ℂ) :
    deriv (complexNumerator γ z) = complexNumeratorDerivative γ z := by
  funext t
  change deriv (fun t : ℂ =>
    ((Q γ : ℂ) / 2 - z) ^ 2 * Complex.exp (-t) *
        (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) -
      Complex.sinh (((Q γ : ℂ) / 2 - z) * (t / 2)) ^ 2) t =
    complexNumeratorDerivative γ z t
  simp (disch := fun_prop) only [deriv_fun_sub, deriv_fun_mul, deriv_fun_pow, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, deriv_div_const, deriv_const', zero_div, sub_self, mul_zero,
    zero_mul, deriv_cexp, deriv_neg'', mul_neg, mul_one, zero_add, neg_mul, deriv_csinh,
    deriv_id'', one_mul, add_zero, one_div, complexNumeratorDerivative, complexDenom]
  ring_nf

private lemma complexNumerator_iteratedDeriv_two_zero (γ : ℝ) (z : ℂ)
    (hγ : 0 < γ) :
    iteratedDeriv 2 (complexNumerator γ z) 0 = 0 := by
  rw [iteratedDeriv_succ]
  rw [show iteratedDeriv 1 (complexNumerator γ z) =
      deriv (complexNumerator γ z) by simp]
  rw [complexNumerator_deriv_eq]
  change deriv (fun t : ℂ =>
    ((Q γ : ℂ) / 2 - z) ^ 2 * Complex.exp (-t) *
        ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)) +
          (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) * Complex.cosh (t / (γ : ℂ)) -
          (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)))) -
      ((Q γ : ℂ) / 2 - z) *
        Complex.sinh (((Q γ : ℂ) / 2 - z) * (t / 2)) *
        Complex.cosh (((Q γ : ℂ) / 2 - z) * (t / 2))) 0 = 0
  simp (disch := fun_prop) only [deriv_fun_sub, deriv_fun_mul, deriv_fun_pow, Nat.cast_ofNat,
    Nat.add_one_sub_one, pow_one, deriv_div_const, deriv_const', zero_div, sub_self, mul_zero,
    neg_zero, Complex.exp_zero, mul_one, deriv_cexp, deriv_neg'', mul_neg, zero_add, zero_mul,
    Complex.cosh_zero, Complex.sinh_zero, add_zero, deriv_fun_add, deriv_ccosh, deriv_id'',
    one_mul, deriv_csinh, one_div, sub_zero]
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hγ)
  field_simp [hγC]
  ring

private lemma canceledNumerator_contDiff (γ : ℝ) (z : ℂ) :
    ContDiff ℝ 3 (canceledNumerator γ z) := by
  change ContDiff ℝ 3 (fun t : ℝ => complexNumerator γ z (t : ℂ))
  exact ((complexNumerator_contDiff γ z).restrict_scalars ℝ).comp
    Complex.ofRealCLM.contDiff

private lemma canceledNumerator_contDiffOn (γ : ℝ) (z : ℂ) :
    ContDiffOn ℝ 3 (canceledNumerator γ z) (Icc 0 1) := by
  exact (canceledNumerator_contDiff γ z).contDiffOn.mono (Set.subset_univ _)

private lemma canceledNumerator_zero (γ : ℝ) (z : ℂ) :
    canceledNumerator γ z 0 = 0 := by
  simp only [canceledNumerator, complexNumerator, Complex.ofReal_zero, neg_zero,
    Complex.exp_zero, mul_one, complexDenom, zero_mul, zero_div, Complex.sinh_zero, mul_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_self]

private lemma canceledNumerator_deriv_zero (γ : ℝ) (z : ℂ) :
    deriv (canceledNumerator γ z) 0 = 0 := by
  change deriv (fun t : ℝ => complexNumerator γ z (t : ℂ)) 0 = 0
  have hF : HasDerivAt (complexNumerator γ z) 0 0 := by
    have hd : HasDerivAt (complexNumerator γ z)
        (deriv (complexNumerator γ z) 0) 0 :=
      ((complexNumerator_contDiff γ z).differentiable (by norm_num) 0).hasDerivAt
    rwa [complexNumerator_deriv_zero] at hd
  simpa using hF.comp_ofReal.deriv

private lemma deriv_real_restrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    deriv (fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
  funext t
  exact (hF t).hasDerivAt.comp_ofReal.deriv

private lemma canceledNumerator_iteratedDeriv_two_zero (γ : ℝ) (z : ℂ)
    (hγ : 0 < γ) :
    iteratedDeriv 2 (canceledNumerator γ z) 0 = 0 := by
  change iteratedDeriv 2 (fun t : ℝ => complexNumerator γ z (t : ℂ)) 0 = 0
  rw [iteratedDeriv_succ]
  have hF : Differentiable ℂ (complexNumerator γ z) :=
    (complexNumerator_contDiff γ z).differentiable (by norm_num)
  have hfirst : iteratedDeriv 1 (fun t : ℝ => complexNumerator γ z (t : ℂ)) =
      fun t : ℝ => deriv (complexNumerator γ z) (t : ℂ) := by
    simpa [iteratedDeriv_succ] using deriv_real_restrict _ hF
  rw [hfirst]
  have hF' : Differentiable ℂ (deriv (complexNumerator γ z)) := by
    have hC2 : ContDiff ℂ (1 + 1) (complexNumerator γ z) :=
      (complexNumerator_contDiff γ z).of_le (by norm_num)
    simpa [iteratedDeriv_succ] using hC2.differentiable_iteratedDeriv' 1
  have hsecond := (hF' (0 : ℂ)).hasDerivAt.comp_ofReal.deriv
  calc
    deriv (fun t : ℝ => deriv (complexNumerator γ z) (t : ℂ)) 0 =
        deriv (deriv (complexNumerator γ z)) 0 := hsecond
    _ = iteratedDeriv 2 (complexNumerator γ z) 0 := by
      rw [iteratedDeriv_succ]
      simp
    _ = 0 := complexNumerator_iteratedDeriv_two_zero γ z hγ

private lemma canceledNumerator_iteratedDerivWithin_one_zero (γ : ℝ) (z : ℂ) :
    iteratedDerivWithin 1 (canceledNumerator γ z) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 1 (canceledNumerator γ z) 0 :=
    (canceledNumerator_contDiff γ z).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  simpa [iteratedDeriv_succ] using canceledNumerator_deriv_zero γ z

private lemma canceledNumerator_iteratedDerivWithin_two_zero (γ : ℝ) (z : ℂ)
    (hγ : 0 < γ) :
    iteratedDerivWithin 2 (canceledNumerator γ z) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 2 (canceledNumerator γ z) 0 :=
    (canceledNumerator_contDiff γ z).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  exact canceledNumerator_iteratedDeriv_two_zero γ z hγ

private lemma canceledNumerator_taylorWithinEval_zero (γ : ℝ) (z : ℂ)
    (hγ : 0 < γ) (t : ℝ) :
    taylorWithinEval (canceledNumerator γ z) 2 (Icc 0 1) 0 t = 0 := by
  rw [taylor_within_apply]
  have h0 : iteratedDerivWithin 0 (canceledNumerator γ z) (Icc 0 1) 0 = 0 := by
    simpa using canceledNumerator_zero γ z
  have h1 := canceledNumerator_iteratedDerivWithin_one_zero γ z
  have h2 := canceledNumerator_iteratedDerivWithin_two_zero γ z hγ
  simp [Finset.sum_range_succ, h0, h1, h2]

private lemma exists_canceledNumerator_taylor_bound (γ : ℝ) (z : ℂ)
    (hγ : 0 < γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 1,
      ‖canceledNumerator γ z t‖ ≤ C * t ^ 3 := by
  have hcont : ContDiffOn ℝ (2 + 1) (canceledNumerator γ z) (Icc 0 1) := by
    exact (canceledNumerator_contDiffOn γ z).of_le (by norm_num)
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound
    (f := canceledNumerator γ z) (a := 0) (b := 1) (n := 2)
    (by norm_num) hcont
  refine ⟨C, ?_, ?_⟩
  · have h := hC 1 (by norm_num)
    rw [canceledNumerator_taylorWithinEval_zero γ z hγ 1] at h
    have h' : ‖canceledNumerator γ z 1‖ ≤ C := by simpa using h
    exact (norm_nonneg _).trans h'
  · intro t ht
    have h := hC t ht
    rw [canceledNumerator_taylorWithinEval_zero γ z hγ t] at h
    simpa using h

lemma realDenom_ge_quadratic {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) :
    t ^ 2 / 4 ≤ realDenom γ t := by
  have hγ' : γ ≠ 0 := ne_of_gt hγ
  have hs₁ : t * γ / 4 ≤ Real.sinh (t * γ / 4) :=
    (Real.self_le_sinh_iff).2 (by positivity)
  have hs₂ : t / γ ≤ Real.sinh (t / γ) :=
    (Real.self_le_sinh_iff).2 (by positivity)
  calc
    t ^ 2 / 4 = (t * γ / 4) * (t / γ) := by field_simp [hγ']
    _ ≤ Real.sinh (t * γ / 4) * Real.sinh (t / γ) :=
      mul_le_mul hs₁ hs₂ (by positivity) (by positivity)

lemma realDenom_pos {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) :
    0 < realDenom γ t := by
  unfold realDenom
  exact mul_pos (Real.sinh_pos_iff.2 (by positivity))
    (Real.sinh_pos_iff.2 (div_pos ht hγ))

private lemma upsilonLogIntegrand_eq_canceled_div {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) {t : ℝ} (ht : 0 < t) :
    upsilonLogIntegrand γ z t =
      canceledNumerator γ z t / ((realDenom γ t : ℂ) * (t : ℂ)) := by
  rw [upsilonLogIntegrand, canceledNumerator_eq_source]
  have hD : (realDenom γ t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'
  have hS₁ : (Real.sinh (t * γ / 4) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
  have hS₂ : (Real.sinh (t / γ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hRD : (realDenom γ t : ℂ) =
      (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ) := by
    simp [realDenom]
  rw [hRD]
  field_simp [hD, hS₁, hS₂, htC]

private lemma upsilonLogIntegrand_norm_le_of_taylor {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hG : ∀ t ∈ Icc 0 1, ‖canceledNumerator γ z t‖ ≤ C * t ^ 3)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ‖upsilonLogIntegrand γ z t‖ ≤ 4 * C := by
  have hDen : 0 < realDenom γ t := realDenom_pos hγ ht
  have hDLower := realDenom_ge_quadratic hγ ht
  have hDt : t ^ 3 / 4 ≤ realDenom γ t * t := by
    calc
      t ^ 3 / 4 = (t ^ 2 / 4) * t := by ring
      _ ≤ realDenom γ t * t := mul_le_mul_of_nonneg_right hDLower (le_of_lt ht)
  have hDtPos : 0 < realDenom γ t * t := mul_pos hDen ht
  have hnormDen : ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos hDen, abs_of_pos ht]
  have hG' : ‖canceledNumerator γ z t‖ ≤ C * t ^ 3 := hG t ⟨le_of_lt ht, ht1⟩
  rw [upsilonLogIntegrand_eq_canceled_div hγ z ht, norm_div, hnormDen]
  calc
    ‖canceledNumerator γ z t‖ / (realDenom γ t * t) ≤
        (C * t ^ 3) / (realDenom γ t * t) :=
          div_le_div_of_nonneg_right hG' (le_of_lt hDtPos)
    _ ≤ 4 * C := (div_le_iff₀ hDtPos).2 <| by
      calc
        C * t ^ 3 = 4 * C * (t ^ 3 / 4) := by ring
        _ ≤ 4 * C * (realDenom γ t * t) :=
          mul_le_mul_of_nonneg_left hDt (by positivity)

private lemma upsilonLogIntegrand_integrableOn_Ioc {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) : IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ z t) (Ioc 0 1) := by
  obtain ⟨C, hC, hG⟩ := exists_canceledNumerator_taylor_bound γ z hγ
  have hmeas : AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrand γ z t) volume := by
    change AEStronglyMeasurable (fun t : ℝ =>
      ((Q γ / 2 - z) ^ 2 * Real.exp (-t) -
        Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
          (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t) volume
    have hA : Measurable (fun t : ℝ => (Q γ / 2 - z) ^ 2 * Real.exp (-t)) := by
      fun_prop
    have hB : Measurable (fun t : ℝ =>
        Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2) := by
      fun_prop
    have hD : Measurable (fun t : ℝ =>
        (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ)) := by
      fun_prop
    have ht : Measurable (fun t : ℝ => (t : ℂ)) := by
      fun_prop
    exact ((hA.sub (hB.div hD)).div ht).aestronglyMeasurable
  apply Measure.integrableOn_of_bounded (s := Ioc 0 1) (μ := volume) (by simp) hmeas
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact upsilonLogIntegrand_norm_le_of_taylor hγ z C hC hG ht.1 ht.2

def tailConst (γ : ℝ) : ℝ :=
  ((1 - Real.exp (-2 * (γ / 4))) / 2) *
    ((1 - Real.exp (-2 * (1 / γ))) / 2)

lemma tailConst_pos {γ : ℝ} (hγ : 0 < γ) : 0 < tailConst γ := by
  have hγ4 : 0 < γ / 4 := by positivity
  have hγinv : 0 < 1 / γ := by positivity
  have h₁ : -2 * (γ / 4) < 0 := by linarith only [hγ4]
  have h₂ : -2 * (1 / γ) < 0 := by linarith only [hγinv]
  have h₁' : 0 < 1 - Real.exp (-2 * (γ / 4)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr h₁)
  have h₂' : 0 < 1 - Real.exp (-2 * (1 / γ)) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr h₂)
  unfold tailConst
  exact mul_pos (div_pos h₁' (by norm_num)) (div_pos h₂' (by norm_num))

private lemma real_sinh_ge_exp {a x : ℝ} (hax : a ≤ x) :
    ((1 - Real.exp (-2 * a)) / 2) * Real.exp x ≤ Real.sinh x := by
  have hexp : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmono : Real.exp (-2 * x) ≤ Real.exp (-2 * a) :=
    Real.exp_le_exp.mpr (by linarith only [hax])
  have hfactor : 1 - Real.exp (-2 * a) ≤ 1 - Real.exp (-2 * x) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hfactor (le_of_lt (Real.exp_pos x))
  calc
    ((1 - Real.exp (-2 * a)) / 2) * Real.exp x ≤
        ((1 - Real.exp (-2 * x)) / 2) * Real.exp x := by
          linarith only [hmul]
    _ = Real.sinh x := by
      rw [Real.sinh_eq]
      calc
        ((1 - Real.exp (-2 * x)) / 2) * Real.exp x =
            (Real.exp x - Real.exp x * Real.exp (-2 * x)) / 2 := by ring
        _ = (Real.exp x - Real.exp (-x)) / 2 := by rw [hexp]

lemma realDenom_ge_tail_exp {γ t : ℝ} (hγ : 0 < γ) (ht : 1 ≤ t) :
    tailConst γ * Real.exp (Q γ / 2 * t) ≤ realDenom γ t := by
  have hs₁ : ((1 - Real.exp (-2 * (γ / 4))) / 2) * Real.exp (t * γ / 4) ≤
      Real.sinh (t * γ / 4) :=
    real_sinh_ge_exp (by linarith only [mul_le_mul_of_nonneg_right ht hγ.le])
  have hs₂ : ((1 - Real.exp (-2 * (1 / γ))) / 2) * Real.exp (t / γ) ≤
      Real.sinh (t / γ) :=
    real_sinh_ge_exp (div_le_div_of_nonneg_right ht (by positivity))
  have hq : Q γ / 2 * t = t * γ / 4 + t / γ := by
    unfold Q
    field_simp [ne_of_gt hγ]
    ring
  have hc₂ : 0 < (1 - Real.exp (-2 * (1 / γ))) / 2 := by
    apply div_pos
    · apply sub_pos.mpr
      have hγinv : 0 < 1 / γ := by positivity
      exact Real.exp_lt_one_iff.mpr (by linarith only [hγinv])
    · norm_num
  have hsecond : 0 ≤ ((1 - Real.exp (-2 * (1 / γ))) / 2) * Real.exp (t / γ) :=
    le_of_lt (mul_pos hc₂ (Real.exp_pos _))
  have hfirst : 0 ≤ Real.sinh (t * γ / 4) :=
    (Real.sinh_pos_iff.mpr (by positivity)).le
  calc
    tailConst γ * Real.exp (Q γ / 2 * t) =
        (((1 - Real.exp (-2 * (γ / 4))) / 2) * Real.exp (t * γ / 4)) *
          (((1 - Real.exp (-2 * (1 / γ))) / 2) * Real.exp (t / γ)) := by
            unfold tailConst
            have he : Real.exp (Q γ / 2 * t) =
                Real.exp (t * γ / 4) * Real.exp (t / γ) := by
              rw [← Real.exp_add]
              rw [hq]
            rw [he]
            ring
    _ ≤ Real.sinh (t * γ / 4) * Real.sinh (t / γ) :=
      mul_le_mul hs₁ hs₂ hsecond hfirst
    _ = realDenom γ t := by rfl

lemma complex_sinh_norm_le_exp_abs_re (w : ℂ) :
    ‖Complex.sinh w‖ ≤ Real.exp |w.re| := by
  rw [Complex.sinh]
  calc
    ‖(Complex.exp w - Complex.exp (-w)) / 2‖ =
        ‖Complex.exp w - Complex.exp (-w)‖ / 2 := by simp
    _ ≤ (‖Complex.exp w‖ + ‖Complex.exp (-w)‖) / 2 := by
      exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = (Real.exp w.re + Real.exp (-w.re)) / 2 := by
      simp [Complex.norm_exp]
    _ ≤ Real.exp |w.re| := by
      have h₁ : Real.exp w.re ≤ Real.exp |w.re| :=
        Real.exp_le_exp.mpr (le_abs_self _)
      have h₂ : Real.exp (-w.re) ≤ Real.exp |w.re| :=
        Real.exp_le_exp.mpr (neg_le_abs _)
      linarith

lemma complex_cosh_norm_le_exp_abs_re (w : ℂ) :
    ‖Complex.cosh w‖ ≤ Real.exp |w.re| := by
  rw [Complex.cosh]
  calc
    ‖(Complex.exp w + Complex.exp (-w)) / 2‖ =
        ‖Complex.exp w + Complex.exp (-w)‖ / 2 := by simp
    _ ≤ (‖Complex.exp w‖ + ‖Complex.exp (-w)‖) / 2 := by
      exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ = (Real.exp w.re + Real.exp (-w.re)) / 2 := by
      simp [Complex.norm_exp]
    _ ≤ Real.exp |w.re| := by
      have h₁ : Real.exp w.re ≤ Real.exp |w.re| :=
        Real.exp_le_exp.mpr (le_abs_self _)
      have h₂ : Real.exp (-w.re) ≤ Real.exp |w.re| :=
        Real.exp_le_exp.mpr (neg_le_abs _)
      linarith

lemma upsilonLogIntegrand_norm_le_tail {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) {t : ℝ} (ht : 1 ≤ t) :
    ‖upsilonLogIntegrand γ z t‖ ≤
    ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
  let w : ℂ := (Q γ / 2 : ℂ) - z
  let δ : ℝ := Q γ / 2 - |w.re|
  have hQpos : 0 < Q γ := by
    unfold Q
    positivity
  have hstrip : |w.re| < Q γ / 2 := by
    apply (abs_lt).2
    constructor <;> dsimp [w] <;> simp <;> linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hdenPos := realDenom_pos hγ (by linarith : 0 < t)
  have hdenLower := realDenom_ge_tail_exp hγ ht
  have hK : 0 < tailConst γ := tailConst_pos hγ
  have hKinv : 0 ≤ (tailConst γ)⁻¹ := le_of_lt (inv_pos.mpr hK)
  have hdeltaExp :
      Real.exp (|w.re| * t) / realDenom γ t ≤
        (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
    apply (div_le_iff₀ hdenPos).2
    have hfactor : 0 ≤ (tailConst γ)⁻¹ * Real.exp (-δ * t) := by positivity
    have hprod := mul_le_mul_of_nonneg_left hdenLower hfactor
    have hEq :
        (tailConst γ)⁻¹ * Real.exp (-δ * t) *
            (tailConst γ * Real.exp (Q γ / 2 * t)) =
          Real.exp (|w.re| * t) := by
      calc
        (tailConst γ)⁻¹ * Real.exp (-δ * t) *
            (tailConst γ * Real.exp (Q γ / 2 * t)) =
            ((tailConst γ)⁻¹ * tailConst γ) *
              (Real.exp (-δ * t) * Real.exp (Q γ / 2 * t)) := by ring
        _ = Real.exp (|w.re| * t) := by
          rw [inv_mul_cancel₀ hK.ne', ← Real.exp_add]
          rw [show -δ * t + Q γ / 2 * t = |w.re| * t by
            dsimp [δ]
            ring_nf]
          ring
    calc
      Real.exp (|w.re| * t) =
          (tailConst γ)⁻¹ * Real.exp (-δ * t) *
            (tailConst γ * Real.exp (Q γ / 2 * t)) := hEq.symm
      _ ≤ (tailConst γ)⁻¹ * Real.exp (-δ * t) * realDenom γ t := hprod
  have hSinhNorm :
      ‖Complex.sinh (w * (t / 2))‖ ^ 2 ≤ Real.exp (|w.re| * t) := by
    have hre : (w * (t / 2)).re = w.re * (t / 2) := by simp
    have habs : |(w * (t / 2)).re| = |w.re| * (t / 2) := by
      rw [hre, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
    have hnorm := complex_sinh_norm_le_exp_abs_re (w * (t / 2))
    have hpow : (Real.exp |(w * (t / 2)).re|) ^ 2 = Real.exp (|w.re| * t) := by
      rw [pow_two, ← Real.exp_add]
      rw [habs]
      congr 1
      ring
    calc
      ‖Complex.sinh (w * (t / 2))‖ ^ 2 ≤
          (Real.exp |(w * (t / 2)).re|) ^ 2 := by
            exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = Real.exp (|w.re| * t) := hpow
  have hB :
      ‖Complex.sinh (w * (t / 2)) ^ 2 / (realDenom γ t : ℂ)‖ ≤
        (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
    calc
      ‖Complex.sinh (w * (t / 2))‖ ^ 2 / realDenom γ t ≤
          Real.exp (|w.re| * t) / realDenom γ t :=
        div_le_div_of_nonneg_right hSinhNorm (le_of_lt hdenPos)
      _ ≤ (tailConst γ)⁻¹ * Real.exp (-δ * t) := hdeltaExp
  have hA : ‖w ^ 2 * Complex.exp (-(t : ℂ))‖ = ‖w‖ ^ 2 * Real.exp (-t) := by
    simp [Complex.norm_exp]
  have htC : ‖(t : ℂ)‖ = t := by
    simp [abs_of_pos (by linarith : 0 < t)]
  have hbound :
      ‖(w ^ 2 * Complex.exp (-(t : ℂ)) -
          Complex.sinh (w * (t / 2)) ^ 2 / (realDenom γ t : ℂ)) / (t : ℂ)‖ ≤
        ‖w‖ ^ 2 * Real.exp (-t) + (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
    rw [norm_div, htC]
    calc
      ‖w ^ 2 * Complex.exp (-(t : ℂ)) -
          Complex.sinh (w * (t / 2)) ^ 2 / (realDenom γ t : ℂ)‖ / t ≤
          (‖w ^ 2 * Complex.exp (-(t : ℂ))‖ +
            ‖Complex.sinh (w * (t / 2)) ^ 2 / (realDenom γ t : ℂ)‖) / t := by
              exact div_le_div_of_nonneg_right (norm_sub_le _ _) (by positivity)
      _ ≤ ‖w‖ ^ 2 * Real.exp (-t) + (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
            rw [hA]
            have hsum :
                ‖w‖ ^ 2 * Real.exp (-t) +
                  ‖Complex.sinh (w * (t / 2)) ^ 2 / (realDenom γ t : ℂ)‖ ≤
                ‖w‖ ^ 2 * Real.exp (-t) + (tailConst γ)⁻¹ * Real.exp (-δ * t) :=
              by
                simpa [add_comm] using
                  add_le_add_right hB (‖w‖ ^ 2 * Real.exp (-t))
            calc
              _ ≤ _ := div_le_self
                (add_nonneg (by positivity) (by positivity)) ht
              _ ≤ _ := hsum
  simpa [upsilonLogIntegrand, w, δ, realDenom, Complex.sub_re,
    Complex.ofReal_re, Complex.ofReal_sinh, Complex.ofReal_mul,
    abs_of_pos (by linarith : 0 < t)] using hbound

lemma upsilonLogIntegrand_aestronglyMeasurable (γ : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrand γ z t) volume := by
  change AEStronglyMeasurable (fun t : ℝ =>
    ((Q γ / 2 - z) ^ 2 * Real.exp (-t) -
      Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t) volume
  have hA : Measurable (fun t : ℝ => (Q γ / 2 - z) ^ 2 * Real.exp (-t)) := by
    fun_prop
  have hB : Measurable (fun t : ℝ =>
      Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2) := by
    fun_prop
  have hD : Measurable (fun t : ℝ =>
      (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ)) := by
    fun_prop
  have ht : Measurable (fun t : ℝ => (t : ℂ)) := by
    fun_prop
  exact ((hA.sub (hB.div hD)).div ht).aestronglyMeasurable

private lemma upsilonLogIntegrand_integrableOn_Ioi_one {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) :
    IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ z t) (Ioi 1) := by
  let w : ℂ := (Q γ / 2 : ℂ) - z
  let δ : ℝ := Q γ / 2 - |w.re|
  let A : ℝ := ‖(Q γ / 2 : ℂ) - z‖ ^ 2
  let B : ℝ := (tailConst γ)⁻¹
  have hQpos : 0 < Q γ := by unfold Q; positivity
  have hstrip : |w.re| < Q γ / 2 := by
    apply (abs_lt).2
    constructor <;> dsimp [w] <;> simp <;> linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hB : 0 ≤ B := by
    dsimp [B]
    exact le_of_lt (inv_pos.mpr (tailConst_pos hγ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hmajor1 : IntegrableOn (fun t : ℝ => A * Real.exp (-t)) (Ioi 1) := by
    change Integrable (fun t : ℝ => A * Real.exp (-t)) (volume.restrict (Ioi 1))
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi 1 (b := 1) (by norm_num)).const_mul A
  have hmajor2 : IntegrableOn (fun t : ℝ => B * Real.exp (-δ * t)) (Ioi 1) := by
    change Integrable (fun t : ℝ => B * Real.exp (-δ * t)) (volume.restrict (Ioi 1))
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi 1 (b := δ) hδ).const_mul B
  have hmajor : IntegrableOn
      (fun t : ℝ => A * Real.exp (-t) + B * Real.exp (-δ * t)) (Ioi 1) :=
    hmajor1.add hmajor2
  apply Integrable.mono' hmajor
    (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htail := upsilonLogIntegrand_norm_le_tail hγ z hz0 hzQ ht.le
  simpa [w, δ, A, B, tailConst, mul_comm] using htail

theorem upsilonLogIntegrand_integrableOn {γ : ℝ} (hγ : 0 < γ)
    (_hγ2 : γ < 2) (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) :
    IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ z t) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext t
    simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro ht
      by_cases hle : t ≤ 1
      · exact Or.inl ⟨ht, hle⟩
      · exact Or.inr (lt_of_not_ge hle)
    · rintro (⟨ht, _⟩ | ht)
      · exact ht
      · linarith
  rw [hsplit, integrableOn_union]
  exact ⟨upsilonLogIntegrand_integrableOn_Ioc hγ z,
    upsilonLogIntegrand_integrableOn_Ioi_one hγ z hz0 hzQ⟩


end

end DOZZ.Proofs

end
