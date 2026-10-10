/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Segment
public import DOZZ.Statements.Defs.ShiftCoeffA

/-!
# Analyticity of the γ/2 shift coefficient

The total γ/2 shift coefficient `𝒜(z, b, c) = shiftCoeffA γ (γ/2) z b c` is a quotient of seven
`l`-factors. It is analytic along an analytic charge curve wherever `Γ` is analytic at the four
numerator arguments other than the constant `-γ²/4` and at `1 - y` for the three denominator
arguments `y` (`ShiftCoeffGood`). At real charges these are positivity conditions.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- Analyticity conditions for the γ/2 shift coefficient `𝒜(z, b, c)`: `Γ` is analytic at the
non-constant numerator arguments and at one minus each denominator argument. -/
def ShiftCoeffGood (γ : ℝ) (z b c : ℂ) : Prop :=
  AnalyticAt ℂ Complex.Gamma ((γ : ℂ) / 2 * z) ∧
    AnalyticAt ℂ Complex.Gamma ((γ : ℂ) / 2 * z - ((γ : ℂ) / 2) ^ 2) ∧
    AnalyticAt ℂ Complex.Gamma ((γ : ℂ) / 2 / 2 * ((z + b + c) - 2 * z - (γ : ℂ) / 2)) ∧
    AnalyticAt ℂ Complex.Gamma (1 - (γ : ℂ) / 2 / 2 * ((z + b + c) - (γ : ℂ) / 2 - 2 * Q γ)) ∧
    AnalyticAt ℂ Complex.Gamma (1 - (γ : ℂ) / 2 / 2 * ((z + b + c) - 2 * c - (γ : ℂ) / 2)) ∧
    AnalyticAt ℂ Complex.Gamma (1 - (γ : ℂ) / 2 / 2 * ((z + b + c) - 2 * b - (γ : ℂ) / 2))


/-- **The γ/2 shift coefficient is analytic along analytic charge curves** where
`ShiftCoeffGood` holds. -/
theorem analyticAt_shiftCoeffA_comp {γ : ℝ} {f₁ f₂ f₃ : ℂ → ℂ} {t : ℂ}
    (h₁ : AnalyticAt ℂ f₁ t) (h₂ : AnalyticAt ℂ f₂ t) (h₃ : AnalyticAt ℂ f₃ t)
    (hg : ShiftCoeffGood γ (f₁ t) (f₂ t) (f₃ t)) :
    AnalyticAt ℂ (fun s => shiftCoeffA γ ((γ : ℂ) / 2) (f₁ s) (f₂ s) (f₃ s)) t := by
  obtain ⟨g₁, g₂, g₃, g₄, g₅, g₆⟩ := hg
  have hfun : (fun s => shiftCoeffA γ ((γ : ℂ) / 2) (f₁ s) (f₂ s) (f₃ s)) = fun s =>
      lFun (-((γ : ℂ) / 2) ^ 2) * lFun ((γ : ℂ) / 2 * f₁ s) *
        lFun ((γ : ℂ) / 2 * f₁ s - ((γ : ℂ) / 2) ^ 2) *
        lFun ((γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - 2 * f₁ s - (γ : ℂ) / 2)) *
        (lFun ((γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - (γ : ℂ) / 2 - 2 * Q γ)))⁻¹ *
        (lFun ((γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - 2 * f₃ s - (γ : ℂ) / 2)))⁻¹ *
        (lFun ((γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - 2 * f₂ s - (γ : ℂ) / 2)))⁻¹ := by
    funext s
    unfold shiftCoeffA
    rw [div_eq_mul_inv, mul_inv, mul_inv]
    ring
  rw [hfun]
  have a₁ : AnalyticAt ℂ (fun s => lFun ((γ : ℂ) / 2 * f₁ s)) t :=
    analyticAt_lFun_comp (f := fun s => (γ : ℂ) / 2 * f₁ s) (analyticAt_const.mul h₁) g₁
  have a₂ : AnalyticAt ℂ (fun s => lFun ((γ : ℂ) / 2 * f₁ s - ((γ : ℂ) / 2) ^ 2)) t :=
    analyticAt_lFun_comp (f := fun s => (γ : ℂ) / 2 * f₁ s - ((γ : ℂ) / 2) ^ 2)
      ((analyticAt_const.mul h₁).sub analyticAt_const) g₂
  have a₃ : AnalyticAt ℂ (fun s => lFun ((γ : ℂ) / 2 / 2 *
      ((f₁ s + f₂ s + f₃ s) - 2 * f₁ s - (γ : ℂ) / 2))) t :=
    analyticAt_lFun_comp
      (f := fun s => (γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - 2 * f₁ s - (γ : ℂ) / 2))
      (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub (analyticAt_const.mul h₁)).sub
        analyticAt_const)) g₃
  have a₄ : AnalyticAt ℂ (fun s => (lFun ((γ : ℂ) / 2 / 2 *
      ((f₁ s + f₂ s + f₃ s) - (γ : ℂ) / 2 - 2 * Q γ)))⁻¹) t :=
    analyticAt_inv_lFun_comp
      (f := fun s => (γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - (γ : ℂ) / 2 - 2 * Q γ))
      (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub analyticAt_const).sub
        analyticAt_const)) g₄
  have a₅ : AnalyticAt ℂ (fun s => (lFun ((γ : ℂ) / 2 / 2 *
      ((f₁ s + f₂ s + f₃ s) - 2 * f₃ s - (γ : ℂ) / 2)))⁻¹) t :=
    analyticAt_inv_lFun_comp
      (f := fun s => (γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - 2 * f₃ s - (γ : ℂ) / 2))
      (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub (analyticAt_const.mul h₃)).sub
        analyticAt_const)) g₅
  have a₆ : AnalyticAt ℂ (fun s => (lFun ((γ : ℂ) / 2 / 2 *
      ((f₁ s + f₂ s + f₃ s) - 2 * f₂ s - (γ : ℂ) / 2)))⁻¹) t :=
    analyticAt_inv_lFun_comp
      (f := fun s => (γ : ℂ) / 2 / 2 * ((f₁ s + f₂ s + f₃ s) - 2 * f₂ s - (γ : ℂ) / 2))
      (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub (analyticAt_const.mul h₂)).sub
        analyticAt_const)) g₆
  exact (((((analyticAt_const.mul a₁).mul a₂).mul a₃).mul a₄).mul a₅).mul a₆

/-- **The γ/2 shift coefficient is meromorphic along analytic charge curves.** -/
theorem meromorphicAt_shiftCoeffA_comp {γ : ℝ} {f₁ f₂ f₃ : ℂ → ℂ} {t : ℂ}
    (h₁ : AnalyticAt ℂ f₁ t) (h₂ : AnalyticAt ℂ f₂ t) (h₃ : AnalyticAt ℂ f₃ t) :
    MeromorphicAt (fun s => shiftCoeffA γ ((γ : ℂ) / 2) (f₁ s) (f₂ s) (f₃ s)) t := by
  unfold shiftCoeffA
  refine (((((meromorphicAt_lFun_comp' analyticAt_const).fun_mul
    (meromorphicAt_lFun_comp' (analyticAt_const.mul h₁))).fun_mul
    (meromorphicAt_lFun_comp' ((analyticAt_const.mul h₁).sub analyticAt_const))).fun_mul
    (meromorphicAt_lFun_comp' (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub
      (analyticAt_const.mul h₁)).sub analyticAt_const)))).fun_div
    (((meromorphicAt_lFun_comp' (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub
      analyticAt_const).sub analyticAt_const))).fun_mul
    (meromorphicAt_lFun_comp' (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub
      (analyticAt_const.mul h₃)).sub analyticAt_const)))).fun_mul
    (meromorphicAt_lFun_comp' (analyticAt_const.mul ((((h₁.add h₂).add h₃).sub
      (analyticAt_const.mul h₂)).sub analyticAt_const)))))

/-- **`ShiftCoeffGood` at real charges from positivity** of the six real arguments. -/
theorem shiftCoeffGood_ofReal {γ z b c : ℝ} (h₁ : 0 < γ / 2 * z)
    (h₂ : 0 < γ / 2 * z - (γ / 2) ^ 2)
    (h₃ : 0 < γ / 2 / 2 * ((z + b + c) - 2 * z - γ / 2))
    (h₄ : 0 < 1 - γ / 2 / 2 * ((z + b + c) - γ / 2 - 2 * Q γ))
    (h₅ : 0 < 1 - γ / 2 / 2 * ((z + b + c) - 2 * c - γ / 2))
    (h₆ : 0 < 1 - γ / 2 / 2 * ((z + b + c) - 2 * b - γ / 2)) :
    ShiftCoeffGood γ (z : ℂ) (b : ℂ) (c : ℂ) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert analyticAt_Gamma_ofReal_pos h₁ using 1
    push_cast
    ring
  · convert analyticAt_Gamma_ofReal_pos h₂ using 1
    push_cast
    ring
  · convert analyticAt_Gamma_ofReal_pos h₃ using 1
    push_cast
    ring
  · convert analyticAt_Gamma_ofReal_pos h₄ using 1
    push_cast
    ring
  · convert analyticAt_Gamma_ofReal_pos h₅ using 1
    push_cast
    ring
  · convert analyticAt_Gamma_ofReal_pos h₆ using 1
    push_cast
    ring

/-- **`ShiftCoeffGood` at a real point `(x - γ/2, b, c)` from linear inequalities.** -/
theorem shiftCoeffGood_of_lt {γ x b c : ℝ} (hγ : 0 < γ) (h₂ : γ < x) (h₃ : x < b + c)
    (h₄ : x - γ + b + c - 2 * Q γ < 4 / γ) (h₅ : x - γ + b - c < 4 / γ)
    (h₆ : x - γ + c - b < 4 / γ) :
    ShiftCoeffGood γ ((x : ℂ) - γ / 2) (b : ℂ) (c : ℂ) := by
  have hz : (x : ℂ) - γ / 2 = ((x - γ / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  have hq : (0 : ℝ) < γ / 4 := by positivity
  have hone : γ / 4 * (4 / γ) = 1 := by field_simp
  refine shiftCoeffGood_ofReal ?_ ?_ ?_ ?_ ?_ ?_
  · have : 0 < x - γ / 2 := by linarith
    positivity
  · have e : γ / 2 * (x - γ / 2) - (γ / 2) ^ 2 = γ / 2 * (x - γ) := by ring
    rw [e]
    have : 0 < x - γ := by linarith
    positivity
  · have e : γ / 2 / 2 * ((x - γ / 2 + b + c) - 2 * (x - γ / 2) - γ / 2) = γ / 4 * (b + c - x) := by
      ring
    rw [e]
    have : 0 < b + c - x := by linarith
    positivity
  · have e : γ / 2 / 2 * ((x - γ / 2 + b + c) - γ / 2 - 2 * Q γ) =
        γ / 4 * (x - γ + b + c - 2 * Q γ) := by ring
    have h := mul_lt_mul_of_pos_left h₄ hq
    rw [e]
    linarith
  · have e : γ / 2 / 2 * ((x - γ / 2 + b + c) - 2 * c - γ / 2) = γ / 4 * (x - γ + b - c) := by
      ring
    have h := mul_lt_mul_of_pos_left h₅ hq
    rw [e]
    linarith
  · have e : γ / 2 / 2 * ((x - γ / 2 + b + c) - 2 * b - γ / 2) = γ / 4 * (x - γ + c - b) := by
      ring
    have h := mul_lt_mul_of_pos_left h₆ hq
    rw [e]
    linarith

/-- `ShiftCoeffGood` persists along continuous curves. -/
theorem eventually_shiftCoeffGood {γ : ℝ} {f₁ f₂ f₃ : ℝ → ℂ} {t₀ : ℝ}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h₃ : Continuous f₃)
    (h : ShiftCoeffGood γ (f₁ t₀) (f₂ t₀) (f₃ t₀)) :
    ∀ᶠ t in 𝓝 t₀, ShiftCoeffGood γ (f₁ t) (f₂ t) (f₃ t) := by
  obtain ⟨k₁, k₂, k₃, k₄, k₅, k₆⟩ := h
  filter_upwards [eventually_analyticAt_comp (φ := fun t => (γ : ℂ) / 2 * f₁ t)
      (by fun_prop) k₁,
    eventually_analyticAt_comp (φ := fun t => (γ : ℂ) / 2 * f₁ t - ((γ : ℂ) / 2) ^ 2)
      (by fun_prop) k₂,
    eventually_analyticAt_comp
      (φ := fun t => (γ : ℂ) / 2 / 2 * ((f₁ t + f₂ t + f₃ t) - 2 * f₁ t - (γ : ℂ) / 2))
      (by fun_prop) k₃,
    eventually_analyticAt_comp
      (φ := fun t => 1 - (γ : ℂ) / 2 / 2 * ((f₁ t + f₂ t + f₃ t) - (γ : ℂ) / 2 - 2 * Q γ))
      (by fun_prop) k₄,
    eventually_analyticAt_comp
      (φ := fun t => 1 - (γ : ℂ) / 2 / 2 * ((f₁ t + f₂ t + f₃ t) - 2 * f₃ t - (γ : ℂ) / 2))
      (by fun_prop) k₅,
    eventually_analyticAt_comp
      (φ := fun t => 1 - (γ : ℂ) / 2 / 2 * ((f₁ t + f₂ t + f₃ t) - 2 * f₂ t - (γ : ℂ) / 2))
      (by fun_prop) k₆] with t a₁ a₂ a₃ a₄ a₅ a₆
  exact ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩

end DOZZ.Proofs

end
