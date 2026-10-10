/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Segment
public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.ShiftEquations.Rbar.Multiplier

/-!
# The coefficient of the second dual crossing seed, in complex form

`dualCrossingL γ ε α α' = l(c - 1) l(c - a - b + 1) / (l(c - a) l(c - b))` with the Gauss parameters
of the dual (`χ = 2/γ`) degenerate insertion. Its complex form `dualLC` uses the affine arguments
`c - 1 = 2(ε - Q)/γ`, `c - a - b + 1 = 2 + 4/γ² - 2α/γ`, `c - a = 1 + 2/γ² + (ε - α - α')/γ` and
`c - b = -2/γ² + (ε - α + α')/γ`; it agrees with the real coefficient at real charges, is
meromorphic along analytic curves, and analytic where `Γ` is analytic at `c - 1`, `c - a - b + 1`,
`1 - (c - a)` and `1 - (c - b)`.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- `c - 1` for the dual crossing coefficient. -/
noncomputable def dualArg₁ (γ : ℝ) (ε : ℂ) : ℂ := 2 * (ε - Q γ) / γ

/-- `c - a - b + 1` for the dual crossing coefficient. -/
noncomputable def dualArg₂ (γ : ℝ) (α : ℂ) : ℂ := 2 + 4 / (γ : ℂ) ^ 2 - 2 * α / γ

/-- `c - a` for the dual crossing coefficient. -/
noncomputable def dualArg₃ (γ : ℝ) (ε α α' : ℂ) : ℂ := 1 + 2 / (γ : ℂ) ^ 2 + (ε - α - α') / γ

/-- `c - b` for the dual crossing coefficient. -/
noncomputable def dualArg₄ (γ : ℝ) (ε α α' : ℂ) : ℂ := -2 / (γ : ℂ) ^ 2 + (ε - α + α') / γ

/-- The complex coefficient of the second dual crossing seed. -/
noncomputable def dualLC (γ : ℝ) (ε α α' : ℂ) : ℂ :=
  lFun (dualArg₁ γ ε) * lFun (dualArg₂ γ α) /
    (lFun (dualArg₃ γ ε α α') * lFun (dualArg₄ γ ε α α'))

/-- **The complex coefficient at real charges is `dualCrossingL`.** -/
theorem dualLC_ofReal {γ : ℝ} (hγ : γ ≠ 0) (ε α α' : ℝ) :
    dualLC γ ε α α' = (dualCrossingL γ ε α α' : ℂ) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  have h₁ : dualArg₁ γ ε = ((gaussParameterC γ (2 / γ) ε - 1 : ℝ) : ℂ) := by
    unfold dualArg₁ gaussParameterC
    push_cast
    field_simp
    ring
  have h₂ : dualArg₂ γ α = ((gaussParameterC γ (2 / γ) ε - gaussParameterA γ (2 / γ) α ε α' -
      gaussParameterB γ (2 / γ) α ε α' + 1 : ℝ) : ℂ) := by
    unfold dualArg₂ gaussParameterC gaussParameterA gaussParameterB
    push_cast
    field_simp
    ring
  have h₃ : dualArg₃ γ ε α α' =
      ((gaussParameterC γ (2 / γ) ε - gaussParameterA γ (2 / γ) α ε α' : ℝ) : ℂ) := by
    unfold dualArg₃ gaussParameterC gaussParameterA Q
    push_cast
    field_simp
    ring
  have h₄ : dualArg₄ γ ε α α' =
      ((gaussParameterC γ (2 / γ) ε - gaussParameterB γ (2 / γ) α ε α' : ℝ) : ℂ) := by
    unfold dualArg₄ gaussParameterC gaussParameterB Q
    push_cast
    field_simp
    ring
  unfold dualLC dualCrossingL
  rw [h₁, h₂, h₃, h₄, lFun_ofReal, lFun_ofReal, lFun_ofReal, lFun_ofReal]
  simp only [Complex.ofReal_re]
  push_cast
  ring

theorem analyticAt_dualArg₁_comp {γ : ℝ} {f : ℂ → ℂ} {t : ℂ} (h : AnalyticAt ℂ f t) :
    AnalyticAt ℂ (fun s => dualArg₁ γ (f s)) t := by
  unfold dualArg₁
  exact (analyticAt_const.mul (h.sub analyticAt_const)).div_const

theorem analyticAt_dualArg₂_comp {γ : ℝ} {f : ℂ → ℂ} {t : ℂ} (h : AnalyticAt ℂ f t) :
    AnalyticAt ℂ (fun s => dualArg₂ γ (f s)) t := by
  unfold dualArg₂
  exact analyticAt_const.sub (analyticAt_const.mul h).div_const

theorem analyticAt_dualArg₃_comp {γ : ℝ} {f₁ f₂ f₃ : ℂ → ℂ} {t : ℂ} (h₁ : AnalyticAt ℂ f₁ t)
    (h₂ : AnalyticAt ℂ f₂ t) (h₃ : AnalyticAt ℂ f₃ t) :
    AnalyticAt ℂ (fun s => dualArg₃ γ (f₁ s) (f₂ s) (f₃ s)) t := by
  unfold dualArg₃
  exact analyticAt_const.add ((h₁.sub h₂).sub h₃).div_const

theorem analyticAt_dualArg₄_comp {γ : ℝ} {f₁ f₂ f₃ : ℂ → ℂ} {t : ℂ} (h₁ : AnalyticAt ℂ f₁ t)
    (h₂ : AnalyticAt ℂ f₂ t) (h₃ : AnalyticAt ℂ f₃ t) :
    AnalyticAt ℂ (fun s => dualArg₄ γ (f₁ s) (f₂ s) (f₃ s)) t := by
  unfold dualArg₄
  exact analyticAt_const.add ((h₁.sub h₂).add h₃).div_const

/-- **The complex coefficient is meromorphic along analytic curves.** -/
theorem meromorphicAt_dualLC_comp {γ : ℝ} {f₁ f₂ f₃ : ℂ → ℂ} {t : ℂ}
    (h₁ : AnalyticAt ℂ f₁ t) (h₂ : AnalyticAt ℂ f₂ t) (h₃ : AnalyticAt ℂ f₃ t) :
    MeromorphicAt (fun s => dualLC γ (f₁ s) (f₂ s) (f₃ s)) t := by
  unfold dualLC
  exact ((meromorphicAt_lFun_comp' (analyticAt_dualArg₁_comp h₁)).fun_mul
    (meromorphicAt_lFun_comp' (analyticAt_dualArg₂_comp h₂))).fun_div
    ((meromorphicAt_lFun_comp' (analyticAt_dualArg₃_comp h₁ h₂ h₃)).fun_mul
      (meromorphicAt_lFun_comp' (analyticAt_dualArg₄_comp h₁ h₂ h₃)))

/-- **The complex coefficient is analytic along analytic curves** where `Γ` is analytic at the two
numerator arguments and at one minus the two denominator arguments. -/
theorem analyticAt_dualLC_comp {γ : ℝ} {f₁ f₂ f₃ : ℂ → ℂ} {t : ℂ}
    (h₁ : AnalyticAt ℂ f₁ t) (h₂ : AnalyticAt ℂ f₂ t) (h₃ : AnalyticAt ℂ f₃ t)
    (g₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ (f₁ t)))
    (g₂ : AnalyticAt ℂ Complex.Gamma (dualArg₂ γ (f₂ t)))
    (g₃ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₃ γ (f₁ t) (f₂ t) (f₃ t)))
    (g₄ : AnalyticAt ℂ Complex.Gamma (1 - dualArg₄ γ (f₁ t) (f₂ t) (f₃ t))) :
    AnalyticAt ℂ (fun s => dualLC γ (f₁ s) (f₂ s) (f₃ s)) t := by
  have hfun : (fun s => dualLC γ (f₁ s) (f₂ s) (f₃ s)) = fun s =>
      lFun (dualArg₁ γ (f₁ s)) * lFun (dualArg₂ γ (f₂ s)) *
        (lFun (dualArg₃ γ (f₁ s) (f₂ s) (f₃ s)))⁻¹ *
        (lFun (dualArg₄ γ (f₁ s) (f₂ s) (f₃ s)))⁻¹ := by
    funext s
    unfold dualLC
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [hfun]
  exact (((analyticAt_lFun_comp (f := fun s => dualArg₁ γ (f₁ s))
    (analyticAt_dualArg₁_comp h₁) g₁).mul
    (analyticAt_lFun_comp (f := fun s => dualArg₂ γ (f₂ s)) (analyticAt_dualArg₂_comp h₂) g₂)).mul
    (analyticAt_inv_lFun_comp (f := fun s => dualArg₃ γ (f₁ s) (f₂ s) (f₃ s))
      (analyticAt_dualArg₃_comp h₁ h₂ h₃) g₃)).mul
    (analyticAt_inv_lFun_comp (f := fun s => dualArg₄ γ (f₁ s) (f₂ s) (f₃ s))
      (analyticAt_dualArg₄_comp h₁ h₂ h₃) g₄)


theorem dualArg₂_ofReal (γ α : ℝ) :
    dualArg₂ γ (α : ℂ) = ((2 + 4 / γ ^ 2 - 2 * α / γ : ℝ) : ℂ) := by
  unfold dualArg₂
  push_cast
  ring

theorem one_sub_dualArg₃_ofReal (γ ε α α' : ℝ) :
    1 - dualArg₃ γ (ε : ℂ) (α : ℂ) (α' : ℂ) = ((-2 / γ ^ 2 - (ε - α - α') / γ : ℝ) : ℂ) := by
  unfold dualArg₃
  push_cast
  ring

theorem one_sub_dualArg₄_ofReal (γ ε α α' : ℝ) :
    1 - dualArg₄ γ (ε : ℂ) (α : ℂ) (α' : ℂ) = ((1 + 2 / γ ^ 2 - (ε - α + α') / γ : ℝ) : ℂ) := by
  unfold dualArg₄
  push_cast
  ring

end DOZZ.Proofs

end
