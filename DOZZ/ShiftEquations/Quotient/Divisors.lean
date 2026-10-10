/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DozzFormula
public import DOZZ.Statements.Defs.ShiftCoeffA
public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Statements.Defs.IsUpsilon
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Topology.DiscreteSubset
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Total DOZZ coefficients: meromorphy and codiscrete nonvanishing

The shift coefficient `shiftCoeffA` is a quotient of seven values of `lFun` at affine arguments; the
DOZZ formula is a zero-free power times a quotient of values of an entire Upsilon at affine
arguments. Both are meromorphic on the plane and, with Mathlib's totalized division and Gamma,
vanish only on a codiscrete exceptional set.
-/

public section

open Filter Set Topology

namespace DOZZ.Proofs

/-- `lFun` composed with an analytic function is meromorphic. -/
theorem meromorphicAt_lFun_comp {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) :
    MeromorphicAt (fun w => lFun (f w)) z := by
  have h1 : MeromorphicAt (fun w => Complex.Gamma (f w)) z :=
    (meromorphicAt_complexGamma (f z)).comp_analyticAt (g := f) hf
  have h2 : MeromorphicAt (fun w => Complex.Gamma (1 - f w)) z :=
    (meromorphicAt_complexGamma (1 - f z)).comp_analyticAt (g := fun w => 1 - f w)
      (analyticAt_const.sub hf)
  unfold lFun
  exact h1.fun_div h2

/-- The total shift coefficient is meromorphic in its first charge on the whole plane. -/
theorem meromorphicOn_shiftCoeffA (γ : ℝ) (χ α₂ α₃ : ℂ) :
    MeromorphicOn (fun z => shiftCoeffA γ χ z α₂ α₃) univ := by
  intro z _
  unfold shiftCoeffA
  have hc : ∀ w : ℂ → ℂ, AnalyticAt ℂ w z → MeromorphicAt (fun x => lFun (w x)) z :=
    fun w hw => meromorphicAt_lFun_comp hw
  refine (((((hc _ analyticAt_const).fun_mul (hc _ (by fun_prop))).fun_mul
    (hc _ (by fun_prop))).fun_mul (hc _ (by fun_prop))).fun_div
    (((hc _ (by fun_prop)).fun_mul (hc _ (by fun_prop))).fun_mul (hc _ (by fun_prop))))

/-- The total shift coefficient vanishes only on a codiscrete exceptional set, when its constant
factor `l(-χ²)` is nonzero. -/
theorem eventually_shiftCoeffA_ne_zero (γ : ℝ) {χ : ℂ} (α₂ α₃ : ℂ) (hχ : χ ≠ 0)
    (h0 : lFun (-χ ^ 2) ≠ 0) :
    ∀ᶠ z in codiscrete ℂ, shiftCoeffA γ χ z α₂ α₃ ≠ 0 := by
  have hχ2 : χ / 2 ≠ 0 := div_ne_zero hχ two_ne_zero
  have e1 := eventually_affine_lFun_ne_zero (c := χ) (d := 0) hχ
  have e2 := eventually_affine_lFun_ne_zero (c := χ) (d := -χ ^ 2) hχ
  have e3 := eventually_affine_lFun_ne_zero (c := -(χ / 2)) (d := χ / 2 * (α₂ + α₃ - χ))
    (neg_ne_zero.mpr hχ2)
  have e4 := eventually_affine_lFun_ne_zero (c := χ / 2)
    (d := χ / 2 * (α₂ + α₃ - χ - 2 * Q γ)) hχ2
  have e5 := eventually_affine_lFun_ne_zero (c := χ / 2) (d := χ / 2 * (α₂ - α₃ - χ)) hχ2
  have e6 := eventually_affine_lFun_ne_zero (c := χ / 2) (d := χ / 2 * (α₃ - α₂ - χ)) hχ2
  filter_upwards [e1, e2, e3, e4, e5, e6] with z h1 h2 h3 h4 h5 h6
  have key : ∀ x y : ℂ, x = y → lFun y ≠ 0 → lFun x ≠ 0 := fun x y e h => e ▸ h
  unfold shiftCoeffA
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 (key _ _ (by ring) h1))
    (key _ _ (by ring) h2)) (key _ _ (by ring) h3))
    (mul_ne_zero (mul_ne_zero (key _ _ (by ring) h4) (key _ _ (by ring) h5))
      (key _ _ (by ring) h6))

/-- An Upsilon is zero-free on the strip `0 < Re z < Q`, where it is an exponential. -/
theorem IsUpsilon.ne_zero_of_re {γ : ℝ} {U : ℂ → ℂ} (hU : IsUpsilon γ U) {z : ℂ}
    (h0 : 0 < z.re) (h1 : z.re < Q γ) : U z ≠ 0 := by
  rw [hU.2 z h0 h1]
  exact Complex.exp_ne_zero _

/-- The positive real base of the DOZZ power factor. -/
theorem dozzFormula_base_pos {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) :
    0 < dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) :=
  mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos (by positivity) _)

/-- The DOZZ formula, as a function of its first charge, is meromorphic on the plane. -/
theorem meromorphicOn_dozzFormula {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    MeromorphicOn (fun z => dozzFormula γ μ U z α₂ α₃) univ := by
  intro z _
  have hb : (((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ)) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 (dozzFormula_base_pos hγ hγ2 hμ)
  have hUa : ∀ w : ℂ → ℂ, AnalyticAt ℂ w z → AnalyticAt ℂ (fun x => U (w x)) z :=
    fun w hw => (hU.1.analyticAt (w z)).comp hw
  have hpow : AnalyticAt ℂ (fun x : ℂ =>
      (((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ)) : ℂ) ^
        ((2 * Q γ - (x + α₂ + α₃)) / γ)) z :=
    analyticAt_const.cpow (by fun_prop) hb
  have hnum : AnalyticAt ℂ (fun x : ℂ => deriv U 0 * U x * U α₂ * U α₃) z :=
    ((analyticAt_const.mul (hUa _ analyticAt_id)).mul analyticAt_const).mul analyticAt_const
  have hden : AnalyticAt ℂ (fun x : ℂ =>
      U ((x + α₂ + α₃ - 2 * Q γ) / 2) * U ((x + α₂ + α₃) / 2 - x) *
        U ((x + α₂ + α₃) / 2 - α₂) * U ((x + α₂ + α₃) / 2 - α₃)) z :=
    (((hUa _ (by fun_prop)).mul (hUa _ (by fun_prop))).mul (hUa _ (by fun_prop))).mul
      (hUa _ (by fun_prop))
  unfold dozzFormula
  exact (hpow.mul hnum).meromorphicAt.fun_div hden.meromorphicAt

/-- The DOZZ formula vanishes only on a codiscrete exceptional set, for fixed charges at which
Upsilon does not vanish. -/
theorem eventually_dozzFormula_ne_zero {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hU : IsUpsilon γ U) {α₂ α₃ : ℂ} (h₂ : U α₂ ≠ 0) (h₃ : U α₃ ≠ 0) :
    ∀ᶠ z in codiscrete ℂ, dozzFormula γ μ U z α₂ α₃ ≠ 0 := by
  have hQ : γ / 2 < Q γ := by
    unfold Q
    have : 0 < 2 / γ := by positivity
    linarith
  have hd : deriv U 0 ≠ 0 := by
    rw [IsUpsilon.deriv_zero hγ hγ2 hU]
    exact IsUpsilon.ne_zero_of_re hU (by simp; positivity) (by simpa using hQ)
  have hb : (((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (dozzFormula_base_pos hγ hγ2 hμ).ne'
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have e0 := eventually_upsilon_affine_ne_zero hγ hU (c := 1) (d := 0) one_ne_zero
  have e1 := eventually_upsilon_affine_ne_zero hγ hU (c := 1 / 2)
    (d := (α₂ + α₃ - 2 * Q γ) / 2) hhalf
  have e2 := eventually_upsilon_affine_ne_zero hγ hU (c := -(1 / 2)) (d := (α₂ + α₃) / 2)
    (neg_ne_zero.mpr hhalf)
  have e3 := eventually_upsilon_affine_ne_zero hγ hU (c := 1 / 2) (d := (α₃ - α₂) / 2) hhalf
  have e4 := eventually_upsilon_affine_ne_zero hγ hU (c := 1 / 2) (d := (α₂ - α₃) / 2) hhalf
  filter_upwards [e0, e1, e2, e3, e4] with z h0 h1 h2 h3 h4
  have hp : (((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ)) : ℂ) ^
      ((2 * Q γ - (z + α₂ + α₃)) / γ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
  have key : ∀ x y : ℂ, x = y → U y ≠ 0 → U x ≠ 0 := fun x y e h => e ▸ h
  unfold dozzFormula
  exact div_ne_zero (mul_ne_zero hp (mul_ne_zero (mul_ne_zero (mul_ne_zero hd
    (key _ _ (by ring) h0)) h₂) h₃))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (key _ _ (by ring) h1) (key _ _ (by ring) h2))
      (key _ _ (by ring) h3)) (key _ _ (by ring) h4))

end DOZZ.Proofs

end
