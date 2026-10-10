/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.Brownian.Reflection.RtheorAnalytic
/-! # Meromorphic DOZZ expressions along analytic charge lines -/
@[expose] public section
open Complex Set
namespace DOZZ.Proofs
/-- The normalized formula is meromorphic along every entire analytic charge curve. -/
theorem roots_formula_line_meromorphic {γ μ : ℝ} {U : ℂ → ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hU : IsUpsilon γ U)
    (A : Fin 3 → ℂ → ℂ) (hA : ∀ i, Differentiable ℂ (A i)) :
    MeromorphicOn (fun z : ℂ =>
      ((μ : ℂ) ^ ((A 0 z + A 1 z + A 2 z - 2 * Q γ) / γ) /
        Complex.Gamma ((A 0 z + A 1 z + A 2 z - 2 * Q γ) / γ)) *
          dozzFormula γ μ U (A 0 z) (A 1 z) (A 2 z)) univ := by
  intro z _
  have ha : ∀ i, AnalyticAt ℂ (A i) z := fun i => (hA i).analyticAt z
  have hS : AnalyticAt ℂ (fun w => (A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ) z :=
    (((ha 0).add (ha 1)).add (ha 2)).sub analyticAt_const |>.div_const
  have hμslit : (μ : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hμ
  have hnorm : MeromorphicAt (fun w => (μ : ℂ) ^ ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ) /
      Complex.Gamma ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / γ)) z :=
    (analyticAt_const.cpow hS hμslit).meromorphicAt.fun_div
      ((meromorphicAt_complexGamma _).comp_analyticAt hS)
  have hb : (((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ)) : ℂ) ∈ slitPlane :=
    Complex.ofReal_mem_slitPlane.mpr (dozzFormula_base_pos hγ hγ2 hμ)
  have hUa : ∀ f : ℂ → ℂ, AnalyticAt ℂ f z → AnalyticAt ℂ (fun w => U (f w)) z :=
    fun f hf => (hU.1.analyticAt (f z)).comp hf
  have hpow : AnalyticAt ℂ (fun w =>
      (((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ)) : ℂ) ^
        ((2 * Q γ - (A 0 w + A 1 w + A 2 w)) / γ)) z :=
    analyticAt_const.cpow ((analyticAt_const.sub (((ha 0).add (ha 1)).add (ha 2))).div_const) hb
  have hnum : AnalyticAt ℂ (fun w => deriv U 0 * U (A 0 w) * U (A 1 w) * U (A 2 w)) z :=
    ((analyticAt_const.mul (hUa _ (ha 0))).mul (hUa _ (ha 1))).mul (hUa _ (ha 2))
  have hhalf : AnalyticAt ℂ (fun w => (A 0 w + A 1 w + A 2 w) / 2) z :=
    (((ha 0).add (ha 1)).add (ha 2)).div_const
  have hden : AnalyticAt ℂ (fun w =>
      U ((A 0 w + A 1 w + A 2 w - 2 * Q γ) / 2) *
        U ((A 0 w + A 1 w + A 2 w) / 2 - A 0 w) *
        U ((A 0 w + A 1 w + A 2 w) / 2 - A 1 w) *
        U ((A 0 w + A 1 w + A 2 w) / 2 - A 2 w)) z :=
    (((hUa _ ((((ha 0).add (ha 1)).add (ha 2)).sub analyticAt_const |>.div_const)).mul
      (hUa _ (hhalf.sub (ha 0)))).mul (hUa _ (hhalf.sub (ha 1)))).mul (hUa _ (hhalf.sub (ha 2)))
  exact hnorm.fun_mul ((hpow.mul hnum).meromorphicAt.fun_div hden.meromorphicAt)
end DOZZ.Proofs
