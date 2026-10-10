/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Rbar.Multiplier

/-!
# The analytic γ/2-crossing multiplier off the diagonal

For charges `(α', ε, α)` the Gauss parameters of the γ/2 crossing are
`A = (γ/4)(α' + ε + α - Q - γ) - 1/2`, `B = (γ/4)(α' + ε - α - Q) + 1/2`, `C = 1 - (γ/2)(Q - α')`,
with `A + B - C = γε/2 - γ²/4 - 1` and, on the crossing region `x = (α + α' + ε - γ/2 - 2Q)/γ > 0`,
`A = (γ²/4) x`. As on the diagonal, the unit multiplier `gammaHalfUnitCrossingMultiplier` is the
restriction of `T(α', ε, α) = -(4π/γ²) Γ(A+1) Γ(1-A)⁻¹ l(B) l(C)⁻¹ (l(-γ²/4) l(γε/2))⁻¹`,
holomorphic wherever `Re(A+1)`, `Re B`, `Re(1-C)` and `Re(1-γε/2)` are positive. Where `B` vanishes
the regularized multiplier `(4/γ) B T`, with `(4/γ) B l(B) = (4/γ) Γ(B+1)/Γ(1-B)`, stays
holomorphic.
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- The Gauss parameter `A` of the γ/2 crossing at charges `(a', e, a)`. -/
noncomputable def crossA3 (γ : ℝ) (a' e a : ℂ) : ℂ :=
  (γ / 4 : ℂ) * (a' + e + a - Q γ - γ) - 1 / 2

/-- The Gauss parameter `B` of the γ/2 crossing. -/
noncomputable def crossB3 (γ : ℝ) (a' e a : ℂ) : ℂ :=
  (γ / 4 : ℂ) * (a' + e - a - Q γ) + 1 / 2

/-- The Gauss parameter `C` of the γ/2 crossing. -/
noncomputable def crossC3 (γ : ℝ) (a' : ℂ) : ℂ := 1 - (γ / 2 : ℂ) * (Q γ - a')

/-- The analytic γ/2-crossing multiplier. -/
noncomputable def crossingMultiplier3 (γ : ℝ) (a' e a : ℂ) : ℂ :=
  -(4 * Real.pi / γ ^ 2 : ℂ) * Complex.Gamma (crossA3 γ a' e a + 1) *
    (Complex.Gamma (1 - crossA3 γ a' e a))⁻¹ * lFun (crossB3 γ a' e a) *
    (lFun (crossC3 γ a'))⁻¹ * (lFun (-(γ : ℂ) ^ 2 / 4) * lFun ((γ : ℂ) * e / 2))⁻¹

/-- The regularized multiplier `(4/γ) B T`, holomorphic across `B = 0`. -/
noncomputable def crossingMultiplier3Reg (γ : ℝ) (a' e a : ℂ) : ℂ :=
  -(4 * Real.pi / γ ^ 2 : ℂ) * Complex.Gamma (crossA3 γ a' e a + 1) *
    (Complex.Gamma (1 - crossA3 γ a' e a))⁻¹ *
    (4 / γ * (Complex.Gamma (crossB3 γ a' e a + 1) *
      (Complex.Gamma (1 - crossB3 γ a' e a))⁻¹)) *
    (lFun (crossC3 γ a'))⁻¹ * (lFun (-(γ : ℂ) ^ 2 / 4) * lFun ((γ : ℂ) * e / 2))⁻¹

/-- The real closed form of the analytic multiplier. -/
noncomputable def crossingMultiplier3Real (γ α' ε α : ℝ) : ℝ :=
  -(4 * Real.pi / γ ^ 2) *
    Real.Gamma (γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) + 1) *
    (Real.Gamma (1 - γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ)))⁻¹ *
    lR (γ / 4 * (α' + ε - α - Q γ) + 1 / 2) * (lR (1 - γ / 2 * (Q γ - α')))⁻¹ *
    (lR (-(γ ^ 2) / 4) * lR (γ * ε / 2))⁻¹

/-- The Gauss parameters of the γ/2 crossing. -/
theorem gaussParameters_three {γ α' ε α : ℝ} (hγ : 0 < γ) :
    gaussParameterA γ (γ / 2) α' ε α = γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) ∧
      gaussParameterB γ (γ / 2) α' ε α = γ / 4 * (α' + ε - α - Q γ) + 1 / 2 ∧
      gaussParameterC γ (γ / 2) α' = 1 - γ / 2 * (Q γ - α') ∧
      gaussParameterA γ (γ / 2) α' ε α + gaussParameterB γ (γ / 2) α' ε α -
          gaussParameterC γ (γ / 2) α' = γ * ε / 2 - γ ^ 2 / 4 - 1 := by
  unfold gaussParameterA gaussParameterB gaussParameterC Q
  refine ⟨by field_simp; ring, by ring, by ring, by field_simp; ring⟩

/-- **The unit crossing multiplier on the crossing region, in closed form.** -/
theorem gammaHalfUnitCrossingMultiplier_real {γ μ α' ε α : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hε₁ : γ / 2 < ε) (hε₂ : ε < 2 / γ) (hx : 0 < (α + α' + ε - γ / 2 - 2 * Q γ) / γ) :
    gammaHalfUnitCrossingMultiplier γ μ α' ε α = crossingMultiplier3Real γ α' ε α := by
  obtain ⟨hA, hB, hC, hy⟩ := gaussParameters_three (α' := α') (ε := ε) (α := α) hγ
  obtain ⟨hyb, -, -, -⟩ := cross_bounds hγ hε₁ hε₂
  set x := (α + α' + ε - γ / 2 - 2 * Q γ) / γ with hxdef
  have hnum : (α + α' + ε + γ / 2 - 2 * Q γ) / γ = x + 1 := by
    rw [hxdef]
    field_simp
    ring
  have hratio : Real.Gamma (x + 1) / Real.Gamma x = x := by
    rw [Real.Gamma_add_one hx.ne', mul_div_assoc, div_self (Real.Gamma_pos_of_pos hx).ne',
      mul_one]
  have hApos : 0 < γ ^ 2 / 4 * x := by positivity
  have hlA : x * lR (γ ^ 2 / 4 * x) =
      4 / γ ^ 2 * (Real.Gamma (γ ^ 2 / 4 * x + 1) / Real.Gamma (1 - γ ^ 2 / 4 * x)) := by
    unfold lR
    rw [Real.Gamma_add_one hApos.ne']
    field_simp
  have hlast : 2 + γ ^ 2 / 4 - γ * ε / 2 = 1 - (γ * ε / 2 - γ ^ 2 / 4 - 1) := by ring
  unfold gammaHalfUnitCrossingMultiplier gammaHalfCrossingMultiplier crossingMultiplier3Real
  rw [hnum, ← hxdef, hratio, hy, hA, hB, hC, hlast]
  simp only [lFun_ofReal_re_eq_lR]
  exact multiplier_algebra hμ.ne' (lR_mul_lR_one_sub hyb.1 hyb.2) hlA

theorem crossA3_ofReal {γ : ℝ} (hγ : 0 < γ) (α' ε α : ℝ) :
    crossA3 γ α' ε α = ((γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) := by
  unfold crossA3
  have hγ0 : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  rw [Q]
  push_cast
  field_simp
  ring

theorem crossB3_ofReal (γ α' ε α : ℝ) :
    crossB3 γ α' ε α = ((γ / 4 * (α' + ε - α - Q γ) + 1 / 2 : ℝ) : ℂ) := by
  unfold crossB3
  push_cast
  ring

theorem crossC3_ofReal (γ α' : ℝ) : crossC3 γ α' = ((1 - γ / 2 * (Q γ - α') : ℝ) : ℂ) := by
  unfold crossC3
  push_cast
  ring

/-- **The analytic multiplier at real charges is the real closed form.** -/
theorem crossingMultiplier3_ofReal {γ : ℝ} (hγ : 0 < γ) (α' ε α : ℝ) :
    crossingMultiplier3 γ α' ε α = (crossingMultiplier3Real γ α' ε α : ℂ) := by
  unfold crossingMultiplier3 crossingMultiplier3Real
  rw [crossA3_ofReal hγ, crossB3_ofReal, crossC3_ofReal,
    show (-(γ : ℂ) ^ 2 / 4) = ((-(γ ^ 2) / 4 : ℝ) : ℂ) by push_cast; ring,
    show ((γ : ℂ) * ε / 2) = ((γ * ε / 2 : ℝ) : ℂ) by push_cast; ring,
    lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR,
    show ((γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) + 1 =
      ((γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) + 1 : ℝ) : ℂ) by push_cast; ring,
    show (1 : ℂ) - ((γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) =
      ((1 - γ ^ 2 / 4 * ((α + α' + ε - γ / 2 - 2 * Q γ) / γ) : ℝ) : ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  ring

/-- **On the crossing region the unit multiplier is the analytic one.** -/
theorem gammaHalfUnitCrossingMultiplier_eq_three {γ μ α' ε α : ℝ} (hγ : 0 < γ) (hμ : 0 < μ)
    (hε₁ : γ / 2 < ε) (hε₂ : ε < 2 / γ) (hx : 0 < (α + α' + ε - γ / 2 - 2 * Q γ) / γ) :
    (gammaHalfUnitCrossingMultiplier γ μ α' ε α : ℂ) = crossingMultiplier3 γ α' ε α := by
  rw [crossingMultiplier3_ofReal hγ, gammaHalfUnitCrossingMultiplier_real hγ hμ hε₁ hε₂ hx]

/-- `l(w) = Γ(w) Γ(1-w)⁻¹`. -/
theorem lFun_eq_mul_inv (w : ℂ) : lFun w = Complex.Gamma w * (Complex.Gamma (1 - w))⁻¹ := by
  unfold lFun
  rw [div_eq_mul_inv]

/-- The analytic multiplier as a product of Gamma factors. -/
theorem crossingMultiplier3_eq (γ : ℝ) (a' e a : ℂ) :
    crossingMultiplier3 γ a' e a =
      -(4 * Real.pi / γ ^ 2 : ℂ) * Complex.Gamma (crossA3 γ a' e a + 1) *
        (Complex.Gamma (1 - crossA3 γ a' e a))⁻¹ *
        (Complex.Gamma (crossB3 γ a' e a) * (Complex.Gamma (1 - crossB3 γ a' e a))⁻¹) *
        (Complex.Gamma (1 - crossC3 γ a') * (Complex.Gamma (crossC3 γ a'))⁻¹) *
        ((lFun (-(γ : ℂ) ^ 2 / 4))⁻¹ *
          (Complex.Gamma (1 - (γ : ℂ) * e / 2) * (Complex.Gamma ((γ : ℂ) * e / 2))⁻¹)) := by
  unfold crossingMultiplier3
  rw [lFun_eq_mul_inv (crossB3 γ a' e a), lFun_inv, mul_inv, lFun_inv ((γ : ℂ) * e / 2)]

/-- The regularized multiplier as a product of Gamma factors. -/
theorem crossingMultiplier3Reg_eq (γ : ℝ) (a' e a : ℂ) :
    crossingMultiplier3Reg γ a' e a =
      -(4 * Real.pi / γ ^ 2 : ℂ) * Complex.Gamma (crossA3 γ a' e a + 1) *
        (Complex.Gamma (1 - crossA3 γ a' e a))⁻¹ *
        (4 / γ * (Complex.Gamma (crossB3 γ a' e a + 1) *
          (Complex.Gamma (1 - crossB3 γ a' e a))⁻¹)) *
        (Complex.Gamma (1 - crossC3 γ a') * (Complex.Gamma (crossC3 γ a'))⁻¹) *
        ((lFun (-(γ : ℂ) ^ 2 / 4))⁻¹ *
          (Complex.Gamma (1 - (γ : ℂ) * e / 2) * (Complex.Gamma ((γ : ℂ) * e / 2))⁻¹)) := by
  unfold crossingMultiplier3Reg
  rw [lFun_inv, mul_inv, lFun_inv ((γ : ℂ) * e / 2)]

/-- Off `B = 0` the regularized multiplier is `(4/γ) B T`. -/
theorem crossingMultiplier3Reg_eq_mul {γ : ℝ} {a' e a : ℂ} (hB : crossB3 γ a' e a ≠ 0) :
    crossingMultiplier3Reg γ a' e a = 4 / γ * crossB3 γ a' e a * crossingMultiplier3 γ a' e a := by
  rw [crossingMultiplier3Reg_eq, crossingMultiplier3_eq, Complex.Gamma_add_one _ hB]
  ring

/-- Holomorphy of `Γ ∘ φ` at a point where `Re φ > 0`. -/
theorem differentiableAt_Gamma_comp {φ : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℂ φ z)
    (hre : 0 < (φ z).re) : DifferentiableAt ℂ (fun w => Complex.Gamma (φ w)) z :=
  (Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hre)).comp z hφ

/-- Holomorphy of `1/Γ ∘ φ`. -/
theorem differentiableAt_inv_Gamma_comp {φ : ℂ → ℂ} {z : ℂ} (hφ : DifferentiableAt ℂ φ z) :
    DifferentiableAt ℂ (fun w => (Complex.Gamma (φ w))⁻¹) z :=
  (Complex.differentiable_one_div_Gamma _).comp z hφ

/-- **The analytic multiplier is holomorphic along holomorphic charge curves** where
`Re(A+1)`, `Re B`, `Re(1-C)` and `Re(1-γε/2)` are positive. -/
theorem differentiableAt_crossingMultiplier3 {γ : ℝ} {φ₁ φ₂ φ₃ : ℂ → ℂ} {z : ℂ}
    (h₁ : DifferentiableAt ℂ φ₁ z) (h₂ : DifferentiableAt ℂ φ₂ z) (h₃ : DifferentiableAt ℂ φ₃ z)
    (hA : 0 < (crossA3 γ (φ₁ z) (φ₂ z) (φ₃ z) + 1).re)
    (hB : 0 < (crossB3 γ (φ₁ z) (φ₂ z) (φ₃ z)).re)
    (hC : 0 < (1 - crossC3 γ (φ₁ z)).re)
    (hE : 0 < (1 - (γ : ℂ) * φ₂ z / 2).re) :
    DifferentiableAt ℂ (fun w => crossingMultiplier3 γ (φ₁ w) (φ₂ w) (φ₃ w)) z := by
  simp_rw [crossingMultiplier3_eq]
  have hAd : DifferentiableAt ℂ (fun w => crossA3 γ (φ₁ w) (φ₂ w) (φ₃ w)) z := by
    unfold crossA3
    fun_prop
  have hBd : DifferentiableAt ℂ (fun w => crossB3 γ (φ₁ w) (φ₂ w) (φ₃ w)) z := by
    unfold crossB3
    fun_prop
  have hCd : DifferentiableAt ℂ (fun w => crossC3 γ (φ₁ w)) z := by
    unfold crossC3
    fun_prop
  have hEd : DifferentiableAt ℂ (fun w => (γ : ℂ) * φ₂ w / 2) z := by fun_prop
  exact ((((((differentiableAt_const _).mul
    (differentiableAt_Gamma_comp (hAd.add_const 1) hA)).mul
    (differentiableAt_inv_Gamma_comp ((differentiableAt_const 1).sub hAd))).mul
    ((differentiableAt_Gamma_comp hBd hB).mul
      (differentiableAt_inv_Gamma_comp ((differentiableAt_const 1).sub hBd)))).mul
    ((differentiableAt_Gamma_comp ((differentiableAt_const 1).sub hCd) hC).mul
      (differentiableAt_inv_Gamma_comp hCd))).mul
    ((differentiableAt_const _).mul
      ((differentiableAt_Gamma_comp ((differentiableAt_const 1).sub hEd) hE).mul
        (differentiableAt_inv_Gamma_comp hEd))))

/-- **The regularized multiplier is holomorphic along holomorphic charge curves** where
`Re(A+1)`, `Re(B+1)`, `Re(1-C)` and `Re(1-γε/2)` are positive. -/
theorem differentiableAt_crossingMultiplier3Reg {γ : ℝ} {φ₁ φ₂ φ₃ : ℂ → ℂ} {z : ℂ}
    (h₁ : DifferentiableAt ℂ φ₁ z) (h₂ : DifferentiableAt ℂ φ₂ z) (h₃ : DifferentiableAt ℂ φ₃ z)
    (hA : 0 < (crossA3 γ (φ₁ z) (φ₂ z) (φ₃ z) + 1).re)
    (hB : 0 < (crossB3 γ (φ₁ z) (φ₂ z) (φ₃ z) + 1).re)
    (hC : 0 < (1 - crossC3 γ (φ₁ z)).re)
    (hE : 0 < (1 - (γ : ℂ) * φ₂ z / 2).re) :
    DifferentiableAt ℂ (fun w => crossingMultiplier3Reg γ (φ₁ w) (φ₂ w) (φ₃ w)) z := by
  simp_rw [crossingMultiplier3Reg_eq]
  have hAd : DifferentiableAt ℂ (fun w => crossA3 γ (φ₁ w) (φ₂ w) (φ₃ w)) z := by
    unfold crossA3
    fun_prop
  have hBd : DifferentiableAt ℂ (fun w => crossB3 γ (φ₁ w) (φ₂ w) (φ₃ w)) z := by
    unfold crossB3
    fun_prop
  have hCd : DifferentiableAt ℂ (fun w => crossC3 γ (φ₁ w)) z := by
    unfold crossC3
    fun_prop
  have hEd : DifferentiableAt ℂ (fun w => (γ : ℂ) * φ₂ w / 2) z := by fun_prop
  exact ((((((differentiableAt_const _).mul
    (differentiableAt_Gamma_comp (hAd.add_const 1) hA)).mul
    (differentiableAt_inv_Gamma_comp ((differentiableAt_const 1).sub hAd))).mul
    ((differentiableAt_const _).mul ((differentiableAt_Gamma_comp (hBd.add_const 1) hB).mul
      (differentiableAt_inv_Gamma_comp ((differentiableAt_const 1).sub hBd))))).mul
    ((differentiableAt_Gamma_comp ((differentiableAt_const 1).sub hCd) hC).mul
      (differentiableAt_inv_Gamma_comp hCd))).mul
    ((differentiableAt_const _).mul
      ((differentiableAt_Gamma_comp ((differentiableAt_const 1).sub hEd) hE).mul
        (differentiableAt_inv_Gamma_comp hEd))))

end DOZZ.Proofs

end
