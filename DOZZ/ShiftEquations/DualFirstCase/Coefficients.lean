/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.Statements.Defs.DualMu
public import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.ShiftEquations.Rbar.Multiplier
import Mathlib.Tactic
/-! # The dual crossing product and the centered shift coefficient -/
@[expose] public section
open Complex Filter Topology Set
namespace DOZZ.Proofs
/-- Analytic parameters for the dual crossing with its first charge variable. -/
noncomputable def dualFirstCase_A (γ : ℝ) (a₂ a₃ z : ℂ) : ℂ :=
  (2 / γ : ℂ) / 2 * (z + a₂ + a₃ - 2 / γ - 2 * Q γ)
noncomputable def dualFirstCase_B (γ : ℝ) (a₂ a₃ z : ℂ) : ℂ :=
  (2 / γ : ℂ) / 2 * (z + a₂ - a₃ - 2 / γ)
noncomputable def dualFirstCase_C (γ : ℝ) (z : ℂ) : ℂ := (2 / γ : ℂ) * z - (2 / γ : ℂ) ^ 2
/-- Product of the two distinct dual crossing multipliers. -/
noncomputable def dualFirstCase_crossingProduct (γ : ℝ) (a₂ a₃ z : ℂ) : ℂ :=
  let A := dualFirstCase_A γ a₂ a₃ z
  let B := dualFirstCase_B γ a₂ a₃ z
  let c := dualFirstCase_C γ z
  let d := dualFirstCase_C γ a₂
  (lFun A * lFun B / (lFun c * lFun (d - 1))) *
    (lFun (d - 1) * lFun (2 - c) / (lFun (d - A) * lFun (d - B)))
/-- The l-function reciprocal identity is valid with the totalized convention of `lFun`. -/
theorem dualFirstCase_lFun_one_sub (z : ℂ) : lFun (1 - z) = (lFun z)⁻¹ := by
  unfold lFun
  rw [sub_sub_cancel, inv_div]
/-- Complexification of the literal real Gauss parameters. -/
theorem dualFirstCase_parameters (γ x a₂ a₃ : ℝ) (hγ : γ ≠ 0) :
    dualFirstCase_A γ a₂ a₃ x = (gaussParameterA γ (2 / γ) x a₂ a₃ : ℂ) ∧
    dualFirstCase_B γ a₂ a₃ x = (gaussParameterB γ (2 / γ) x a₂ a₃ : ℂ) ∧
    dualFirstCase_C γ x = (gaussParameterC γ (2 / γ) x : ℂ) ∧
    dualFirstCase_C γ a₂ - 1 =
      (gaussParameterA γ (2 / γ) x a₂ a₃ + gaussParameterB γ (2 / γ) x a₂ a₃ - gaussParameterC γ (2 / γ) x : ℂ) := by
  have hg : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ
  unfold dualFirstCase_A dualFirstCase_B dualFirstCase_C gaussParameterA gaussParameterB gaussParameterC Q
  push_cast
  constructor
  · field_simp; ring
  constructor
  · field_simp; ring
  constructor <;> field_simp <;> ring
/-- The product is exactly the product of the two coefficients `dualCrossingMultiplier` and
`dualCrossingL` of the dual crossing seeds on the real slice. -/
theorem dualFirstCase_crossingProduct_ofReal (γ x a₂ a₃ : ℝ) (hγ : γ ≠ 0) :
    dualFirstCase_crossingProduct γ a₂ a₃ x =
      ((dualCrossingMultiplier γ a₃ x a₂ * dualCrossingL γ a₂ x a₃ : ℝ) : ℂ) := by
  obtain ⟨hA, hB, hc, _hd⟩ := dualFirstCase_parameters γ x a₂ a₃ hγ
  have hdC := (dualFirstCase_parameters γ a₂ x a₃ hγ).2.2.1
  have hab : gaussParameterA γ (2 / γ) x a₂ a₃ + gaussParameterB γ (2 / γ) x a₂ a₃ =
      gaussParameterC γ (2 / γ) x + gaussParameterC γ (2 / γ) a₂ - 1 := by
    unfold gaussParameterA gaussParameterB gaussParameterC Q
    field_simp; ring
  unfold dualFirstCase_crossingProduct dualCrossingMultiplier dualCrossingL
  dsimp only
  rw [hA, hB, hc, hdC]
  rw [show (gaussParameterC γ (2 / γ) a₂ : ℂ) - 1 =
    ((gaussParameterC γ (2 / γ) a₂ - 1 : ℝ) : ℂ) by push_cast; rfl]
  have habc : (gaussParameterA γ (2 / γ) x a₂ a₃ : ℂ) + gaussParameterB γ (2 / γ) x a₂ a₃ =
      (gaussParameterC γ (2 / γ) x : ℂ) + gaussParameterC γ (2 / γ) a₂ - 1 := by exact_mod_cast hab
  rw [show (2 : ℂ) - (gaussParameterC γ (2 / γ) x : ℂ) =
      ((gaussParameterC γ (2 / γ) a₂ - gaussParameterA γ (2 / γ) x a₂ a₃ -
        gaussParameterB γ (2 / γ) x a₂ a₃ + 1 : ℝ) : ℂ) by push_cast; linear_combination habc]
  simp only [← Complex.ofReal_sub, lFun_ofReal, Complex.ofReal_re]
  push_cast
  rw [show gaussParameterA γ (2 / γ) x a₂ a₃ + gaussParameterB γ (2 / γ) x a₂ a₃ -
    gaussParameterC γ (2 / γ) x = gaussParameterC γ (2 / γ) a₂ - 1 by linarith only [hab]]
/-- The crossing product is meromorphic on the whole plane. -/
theorem dualFirstCase_crossingProduct_meromorphic (γ : ℝ) (a₂ a₃ : ℂ) :
    MeromorphicOn (dualFirstCase_crossingProduct γ a₂ a₃) univ := by
  intro z _
  have hA : AnalyticAt ℂ (dualFirstCase_A γ a₂ a₃) z := by unfold dualFirstCase_A; fun_prop
  have hB : AnalyticAt ℂ (dualFirstCase_B γ a₂ a₃) z := by unfold dualFirstCase_B; fun_prop
  have hc : AnalyticAt ℂ (dualFirstCase_C γ) z := by unfold dualFirstCase_C; fun_prop
  exact ((meromorphicAt_lFun_comp hA).fun_mul (meromorphicAt_lFun_comp hB)).fun_div
    ((meromorphicAt_lFun_comp hc).fun_mul analyticAt_const.meromorphicAt) |>.fun_mul
    ((analyticAt_const.meromorphicAt.fun_mul (meromorphicAt_lFun_comp (analyticAt_const.sub hc))).fun_div
      ((meromorphicAt_lFun_comp (analyticAt_const.sub hA)).fun_mul
        (meromorphicAt_lFun_comp (analyticAt_const.sub hB))))
end DOZZ.Proofs
