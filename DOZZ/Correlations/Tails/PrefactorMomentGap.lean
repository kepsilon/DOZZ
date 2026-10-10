/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.Tactic.Ring

/-! An independent Gaussian pin preserves the exponential last-cut moment rate. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem independent_prefactor_moment_gap
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (Q : Measure Ξ) [SFinite P] [SFinite Q]
    (J Jc : Ω → ℝ≥0∞) (S : Ξ → ℝ≥0∞)
    (hJ : AEMeasurable J P) (hJc : AEMeasurable Jc P) (hS : AEMeasurable S Q)
    (p L D γ c : ℝ) (hp : 0 ≤ p) (hD : 0 ≤ D)
    (hSm : (∫⁻ ω, S ω^p ∂Q).toReal ≤ L)
    (hgap : (∫⁻ ω, J ω^p ∂P).toReal-(∫⁻ ω, Jc ω^p ∂P).toReal ≤ D*Real.exp (-γ*c)) :
    (∫⁻ q : Ω × Ξ, (S q.2*J q.1)^p ∂P.prod Q).toReal -
      (∫⁻ q : Ω × Ξ, (S q.2*Jc q.1)^p ∂P.prod Q).toReal ≤ L*D*Real.exp (-γ*c) := by
  have hprod (A : Ω → ℝ≥0∞) (hA : AEMeasurable A P) :
      (∫⁻ q : Ω × Ξ, (S q.2*A q.1)^p ∂P.prod Q).toReal =
        (∫⁻ ω, S ω^p ∂Q).toReal*(∫⁻ ω, A ω^p ∂P).toReal := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp,mul_comm (S _ ^ p)]
    rw [lintegral_prod_mul (hA.pow_const p) (hS.pow_const p),ENNReal.toReal_mul,mul_comm]
  rw [hprod J hJ,hprod Jc hJc,← mul_sub]
  calc
    _ ≤ (∫⁻ ω, S ω^p ∂Q).toReal*(D*Real.exp (-γ*c)) :=
      mul_le_mul_of_nonneg_left hgap ENNReal.toReal_nonneg
    _ ≤ L*(D*Real.exp (-γ*c)) :=
      mul_le_mul_of_nonneg_right hSm (mul_nonneg hD (Real.exp_nonneg _))
    _ = _ := (mul_assoc _ _ _).symm


end DOZZ.Proofs
