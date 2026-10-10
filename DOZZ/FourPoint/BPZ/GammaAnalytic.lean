/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.LFun
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! # Analyticity of the Gamma-function expressions in the BPZ equation

* `bpz_analyticAt_complex_Gamma`, `bpz_analyticAt_real_Gamma`: `Γ` is analytic away from the
  poles `0, -1, -2, …`. In the complex case `Γ` is the pointwise inverse of the entire function
  `1 / Γ`, which does not vanish off the poles. The real case composes with `ofReal` and `re`.
* `bpz_analyticAt_gaussCoefficientRatio`: if `a`, `b`, `c` are real analytic at `x₀` and the ten
  Gamma arguments of `gaussCoefficientRatio` are positive at `x₀`, then
  `x ↦ gaussCoefficientRatio (a x) (b x) (c x)` is real analytic at `x₀`.
* `bpz_analyticAt_re_planarGaussConstant`: if `k`, `β` are real analytic at `x₀` and the three
  arguments of `lFun` in `planarGaussConstant` avoid the integers at `x₀`, then the real part of
  `x ↦ planarGaussConstant (k x) (β x)` is real analytic at `x₀`. Every `lFun` factor is finite
  and nonzero there, so the quotient is analytic. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The complex Gamma function is analytic away from the poles `-m`, `m : ℕ`. -/
theorem bpz_analyticAt_complex_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.Gamma s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) s :=
    Complex.differentiable_one_div_Gamma.analyticAt s
  have h2 : (Complex.Gamma s)⁻¹ ≠ 0 := inv_ne_zero (Complex.Gamma_ne_zero hs)
  simpa only [inv_inv] using h1.fun_inv h2

/-- The real Gamma function is real analytic away from the poles `-m`, `m : ℕ`. -/
theorem bpz_analyticAt_real_Gamma {x : ℝ} (hx : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    AnalyticAt ℝ Real.Gamma x := by
  have hc : ∀ m : ℕ, (x : ℂ) ≠ -(m : ℂ) := fun m h => hx m (by exact_mod_cast h)
  have h1 : AnalyticAt ℝ Complex.Gamma (Complex.ofRealCLM x) :=
    (bpz_analyticAt_complex_Gamma hc).restrictScalars
  have h2 : AnalyticAt ℝ (fun y : ℝ => (Complex.Gamma (y : ℂ)).re) x :=
    (Complex.reCLM.analyticAt _).comp (h1.comp (Complex.ofRealCLM.analyticAt x))
  have e : Real.Gamma = fun y : ℝ => (Complex.Gamma (y : ℂ)).re := by
    funext y
    simp only [Complex.Gamma_ofReal, Complex.ofReal_re]
  rw [e]
  exact h2

/-- `Real.Gamma ∘ f` is real analytic at a point where `f` is analytic with positive value. -/
theorem bpzGA_analyticAt_real_Gamma_comp {f : ℝ → ℝ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀)
    (h : 0 < f x₀) : AnalyticAt ℝ (fun x => Real.Gamma (f x)) x₀ :=
  (bpz_analyticAt_real_Gamma fun m =>
    (lt_of_le_of_lt (neg_nonpos.2 (Nat.cast_nonneg m)) h).ne').fun_comp hf

/-- The Gauss coefficient ratio is real analytic in the parameters where all ten Gamma arguments
are positive. -/
theorem bpz_analyticAt_gaussCoefficientRatio {a b c : ℝ → ℝ} {x₀ : ℝ}
    (ha : AnalyticAt ℝ a x₀) (hb : AnalyticAt ℝ b x₀) (hc : AnalyticAt ℝ c x₀)
    (h1 : 0 < c x₀) (h2 : 0 < 1 - a x₀) (h3 : 0 < 1 - b x₀) (h4 : 0 < a x₀ - c x₀ + 1)
    (h5 : 0 < b x₀ - c x₀ + 1) (h6 : 0 < 2 - c x₀) (h7 : 0 < c x₀ - a x₀)
    (h8 : 0 < c x₀ - b x₀) (h9 : 0 < a x₀) (h10 : 0 < b x₀) :
    AnalyticAt ℝ (fun x => gaussCoefficientRatio (a x) (b x) (c x)) x₀ := by
  have k1 := bpzGA_analyticAt_real_Gamma_comp hc h1
  have k2 := bpzGA_analyticAt_real_Gamma_comp (analyticAt_const.fun_sub ha) h2
  have k3 := bpzGA_analyticAt_real_Gamma_comp (analyticAt_const.fun_sub hb) h3
  have k4 := bpzGA_analyticAt_real_Gamma_comp
    ((ha.fun_sub hc).fun_add (analyticAt_const (v := (1 : ℝ)))) h4
  have k5 := bpzGA_analyticAt_real_Gamma_comp
    ((hb.fun_sub hc).fun_add (analyticAt_const (v := (1 : ℝ)))) h5
  have k6 := bpzGA_analyticAt_real_Gamma_comp (analyticAt_const.fun_sub hc) h6
  have k7 := bpzGA_analyticAt_real_Gamma_comp (hc.fun_sub ha) h7
  have k8 := bpzGA_analyticAt_real_Gamma_comp (hc.fun_sub hb) h8
  have k9 := bpzGA_analyticAt_real_Gamma_comp ha h9
  have k10 := bpzGA_analyticAt_real_Gamma_comp hb h10
  have hden : Real.Gamma (2 - c x₀) ^ 2 * Real.Gamma (c x₀ - a x₀) * Real.Gamma (c x₀ - b x₀) *
      Real.Gamma (a x₀) * Real.Gamma (b x₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (pow_ne_zero 2 (Real.Gamma_pos_of_pos h6).ne') (Real.Gamma_pos_of_pos h7).ne')
      (Real.Gamma_pos_of_pos h8).ne') (Real.Gamma_pos_of_pos h9).ne')
      (Real.Gamma_pos_of_pos h10).ne'
  unfold gaussCoefficientRatio
  exact (((((k1.fun_pow 2).fun_mul k2).fun_mul k3).fun_mul k4).fun_mul k5).fun_neg.fun_div
    (((((k6.fun_pow 2).fun_mul k7).fun_mul k8).fun_mul k9).fun_mul k10) hden

/-- A real number that is not an integer is not a pole `-m` of `Γ`. -/
theorem bpzGA_ne_neg_nat {y : ℝ} (h : ∀ n : ℤ, y ≠ n) (m : ℕ) : (y : ℂ) ≠ -(m : ℂ) :=
  fun hm => h (-(m : ℤ)) (by exact_mod_cast hm)

/-- For a real number `y` that is not an integer, `1 - y` is not a pole `-m` of `Γ`. -/
theorem bpzGA_one_sub_ne_neg_nat {y : ℝ} (h : ∀ n : ℤ, y ≠ n) (m : ℕ) :
    1 - (y : ℂ) ≠ -(m : ℂ) := fun hm =>
  h (1 + (m : ℤ)) (by
    have : (y : ℂ) = 1 + (m : ℂ) := by linear_combination -hm
    exact_mod_cast this)

/-- `lFun` is nonzero at a real point that is not an integer. -/
theorem bpzGA_lFun_ne_zero {y : ℝ} (h : ∀ n : ℤ, y ≠ n) : lFun (y : ℂ) ≠ 0 :=
  div_ne_zero (Complex.Gamma_ne_zero (bpzGA_ne_neg_nat h))
    (Complex.Gamma_ne_zero (bpzGA_one_sub_ne_neg_nat h))

/-- `Complex.Gamma ∘ g` is real analytic where `g : ℝ → ℂ` is real analytic and avoids the
poles of `Γ`. -/
theorem bpzGA_analyticAt_Gamma_comp {g : ℝ → ℂ} {x₀ : ℝ} (hg : AnalyticAt ℝ g x₀)
    (h : ∀ m : ℕ, g x₀ ≠ -(m : ℂ)) : AnalyticAt ℝ (fun x => Complex.Gamma (g x)) x₀ :=
  (bpz_analyticAt_complex_Gamma h).restrictScalars.fun_comp hg

/-- `x ↦ lFun (f x)` is real analytic where `f` is real analytic and avoids the integers. -/
theorem bpzGA_analyticAt_lFun {f : ℝ → ℝ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀)
    (h : ∀ n : ℤ, f x₀ ≠ n) : AnalyticAt ℝ (fun x => lFun (f x : ℂ)) x₀ := by
  have hg : AnalyticAt ℝ (fun x : ℝ => (f x : ℂ)) x₀ := (Complex.ofRealCLM.analyticAt _).comp hf
  have e1 : AnalyticAt ℝ (fun x => Complex.Gamma (f x : ℂ)) x₀ :=
    bpzGA_analyticAt_Gamma_comp hg (bpzGA_ne_neg_nat h)
  have e2 : AnalyticAt ℝ (fun x => Complex.Gamma (1 - (f x : ℂ))) x₀ :=
    bpzGA_analyticAt_Gamma_comp (analyticAt_const.fun_sub hg) (bpzGA_one_sub_ne_neg_nat h)
  exact e1.fun_div e2 (Complex.Gamma_ne_zero (bpzGA_one_sub_ne_neg_nat h))

/-- The real part of the planar Gauss constant is real analytic in the parameters where the three
arguments of `lFun` avoid the integers. -/
theorem bpz_analyticAt_re_planarGaussConstant {k β : ℝ → ℝ} {x₀ : ℝ}
    (hk : AnalyticAt ℝ k x₀) (hβ : AnalyticAt ℝ β x₀)
    (h1 : ∀ n : ℤ, β x₀ / 2 ≠ n) (h2 : ∀ n : ℤ, -k x₀ / 2 ≠ n)
    (h3 : ∀ n : ℤ, 2 - β x₀ / 2 + k x₀ / 2 ≠ n) :
    AnalyticAt ℝ (fun x => (planarGaussConstant (k x) (β x)).re) x₀ := by
  have a1 : AnalyticAt ℝ (fun x => lFun ((β x / 2 : ℝ) : ℂ)) x₀ :=
    bpzGA_analyticAt_lFun (by fun_prop (disch := norm_num)) h1
  have a2 : AnalyticAt ℝ (fun x => lFun ((-k x / 2 : ℝ) : ℂ)) x₀ :=
    bpzGA_analyticAt_lFun (by fun_prop (disch := norm_num)) h2
  have a3 : AnalyticAt ℝ (fun x => lFun ((2 - β x / 2 + k x / 2 : ℝ) : ℂ)) x₀ :=
    bpzGA_analyticAt_lFun (by fun_prop (disch := norm_num)) h3
  have hne : lFun ((β x₀ / 2 : ℝ) : ℂ) * lFun ((-k x₀ / 2 : ℝ) : ℂ) *
      lFun ((2 - β x₀ / 2 + k x₀ / 2 : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (bpzGA_lFun_ne_zero h1) (bpzGA_lFun_ne_zero h2))
      (bpzGA_lFun_ne_zero h3)
  have hP : AnalyticAt ℝ (fun x => planarGaussConstant (k x) (β x)) x₀ :=
    analyticAt_const.fun_div ((a1.fun_mul a2).fun_mul a3) hne
  exact (Complex.reCLM.analyticAt _).comp hP

end DOZZ.Proofs
