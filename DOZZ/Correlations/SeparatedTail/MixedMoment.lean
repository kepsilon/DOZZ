/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The Hölder step of the separated joint-tail estimate retains every correlation of the
harmonic and restoration envelope. Only the two Dirichlet cutoff masses are independent. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The finite-cutoff mixed moment bound of the separated joint-tail estimate. `E` includes the
Wick variance correction, the harmonic suprema and the correlated restoration scalar. -/
theorem separatedTail_mixed_moment_le_of_independent_domination
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W2 W3 D2 D3 E : Ω → ℝ≥0∞)
    (hD2 : AEMeasurable D2 P) (hD3 : AEMeasurable D3 P)
    (hE : AEMeasurable E P) (hD : IndepFun D2 D3 P)
    (a2 a3 p q : ℝ) (_ha2 : 0 ≤ a2) (_ha3 : 0 ≤ a3)
    (hpq : p.HolderConjugate q)
    (hdom : ∀ᵐ ω ∂P, W2 ω ^ a2 * W3 ω ^ a3 ≤ E ω *
      (D2 ω ^ a2 * D3 ω ^ a3)) :
    (∫⁻ ω, W2 ω ^ a2 * W3 ω ^ a3 ∂P) ≤
      (∫⁻ ω, E ω ^ p ∂P) ^ (1 / p) *
        ((∫⁻ ω, D2 ω ^ (a2 * q) ∂P) *
          (∫⁻ ω, D3 ω ^ (a3 * q) ∂P)) ^ (1 / q) := by
  have hpow : IndepFun (fun ω => D2 ω ^ (a2*q))
      (fun ω => D3 ω ^ (a3*q)) P :=
    hD.comp (ENNReal.continuous_rpow_const.measurable)
      (ENNReal.continuous_rpow_const.measurable)
  have hfactor := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hD2.pow_const (a2*q)) (hD3.pow_const (a3*q)) hpow
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hE
    ((hD2.pow_const a2).mul (hD3.pow_const a3))
  calc
    _ ≤ ∫⁻ ω, E ω * (D2 ω ^ a2 * D3 ω ^ a3) ∂P := lintegral_mono_ae hdom
    _ ≤ _ := by
      simpa only [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.pos.le,
        ← ENNReal.rpow_mul, hfactor] using hh

/-- Uniform finite bounds on the three moments give one finite mixed-moment constant. -/
theorem separatedTail_mixed_moment_le_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (W2 W3 D2 D3 E : Ω → ℝ≥0∞)
    (hD2 : AEMeasurable D2 P) (hD3 : AEMeasurable D3 P)
    (hE : AEMeasurable E P) (hD : IndepFun D2 D3 P)
    (a2 a3 p q : ℝ) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hpq : p.HolderConjugate q)
    (hdom : ∀ᵐ ω ∂P, W2 ω ^ a2 * W3 ω ^ a3 ≤ E ω *
      (D2 ω ^ a2 * D3 ω ^ a3))
    (BE B2 B3 : ℝ≥0∞)
    (hBE : (∫⁻ ω, E ω ^ p ∂P) ≤ BE)
    (hB2 : (∫⁻ ω, D2 ω ^ (a2 * q) ∂P) ≤ B2)
    (hB3 : (∫⁻ ω, D3 ω ^ (a3 * q) ∂P) ≤ B3) :
    (∫⁻ ω, W2 ω ^ a2 * W3 ω ^ a3 ∂P) ≤
      BE ^ (1 / p) * (B2 * B3) ^ (1 / q) :=
  (separatedTail_mixed_moment_le_of_independent_domination P W2 W3 D2 D3 E hD2 hD3 hE hD
    a2 a3 p q ha2 ha3 hpq hdom).trans (mul_le_mul'
      (ENNReal.rpow_le_rpow hBE (div_nonneg zero_le_one hpq.pos.le))
      (ENNReal.rpow_le_rpow (mul_le_mul' hB2 hB3) (div_nonneg zero_le_one hpq.symm.pos.le)))

/-- The uniform constant in the preceding estimate is finite. -/
theorem separatedTail_mixed_moment_constant_lt_top
    (BE B2 B3 : ℝ≥0∞) (hBE : BE < ⊤) (hB2 : B2 < ⊤) (hB3 : B3 < ⊤)
    (p q : ℝ) (hpq : p.HolderConjugate q) :
    BE ^ (1 / p) * (B2 * B3) ^ (1 / q) < ⊤ :=
  ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hpq.pos.le) hBE.ne)
    (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hpq.symm.pos.le) (ENNReal.mul_lt_top hB2 hB3).ne)

end DOZZ.Proofs
