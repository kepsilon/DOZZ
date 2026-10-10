/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsTailSandwich

/-! Quantitative scalar tail estimate before choosing the logarithmic cut level. -/

@[expose] public section
open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

theorem truncated_williams_tail_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ × Ω → ℝ) (J Jc : Ω → ℝ)
    (hJ : Measurable J) (hJc : Measurable Jc)
    (hJ0 : ∀ ω, 0 ≤ J ω) (hJc0 : ∀ ω, 0 ≤ Jc ω)
    (ν γ x c r D : ℝ) (hν : 0 < ν) (hγ : 0 < γ) (hx : 0 < x) (hD : 0 ≤ D)
    (hpr : 2*ν/γ ≤ r)
    (hJp : Integrable (fun ω => J ω^(2*ν/γ)) P)
    (hJcp : Integrable (fun ω => Jc ω^(2*ν/γ)) P)
    (hJr : Integrable (fun ω => J ω^r) P)
    (hJcr : Integrable (fun ω => Jc ω^r) P)
    (hupper : ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P, A q ≤ J q.2)
    (hlower : ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P, c ≤ q.1 → Jc q.2 ≤ A q)
    (hgap : (∫ ω, J ω^(2*ν/γ) ∂P)-(∫ ω, Jc ω^(2*ν/γ) ∂P) ≤ D*Real.exp (-γ*c)) :
    |(((brownianMaximumReferenceLaw ν).prod P) {q | x < A q*Real.exp (γ*q.1)}).toReal -
        x^(-(2*ν/γ))*(∫ ω, J ω^(2*ν/γ) ∂P)| ≤
      x^(-(2*ν/γ))*(D*Real.exp (-γ*c)) +
        x^(-r)*((∫ ω, J ω^r ∂P)+(∫ ω, Jc ω^r ∂P)) +
          (x*Real.exp (-γ*c))^(-r)*(∫ ω, Jc ω^r ∂P) := by
  let μ := brownianMaximumReferenceLaw ν
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  have hp : 0 < 2*ν/γ := by positivity
  have hr : 0 < r := hp.trans_le hpr
  have hs := truncated_williams_tail_sandwich μ P A J Jc hJc0 γ c x hγ hupper hlower
  have hu := williams_pareto_tail_error P J hJ hJ0 ν γ x r hν hγ hx hpr hJp hJr
  have hl := williams_pareto_tail_error P Jc hJc hJc0 ν γ x r hν hγ hx hpr hJcp hJcr
  have he := power_tail_le_moment P Jc hJc0 r (x*Real.exp (-γ*c)) hr
    (mul_pos hx (Real.exp_pos _)) hJcr
  have hd := mul_le_mul_of_nonneg_left hgap (Real.rpow_nonneg hx.le (-(2*ν/γ)))
  have hJi : 0 ≤ ∫ ω, J ω^r ∂P := integral_nonneg (fun ω => Real.rpow_nonneg (hJ0 ω) r)
  have hJci : 0 ≤ ∫ ω, Jc ω^r ∂P := integral_nonneg (fun ω => Real.rpow_nonneg (hJc0 ω) r)
  have hXr : 0 ≤ x^(-r) := Real.rpow_nonneg hx.le _
  have hXc : 0 ≤ (x*Real.exp (-γ*c))^(-r) := Real.rpow_nonneg (by positivity) _
  have hXd : 0 ≤ x^(-(2*ν/γ))*(D*Real.exp (-γ*c)) := by positivity
  have h1 := (abs_le.mp hu).2
  have h2 := (abs_le.mp hl).1
  apply abs_le.mpr
  constructor
  · have hlower' := hs.2
    change (((μ.prod P) {q | x < Jc q.2*Real.exp (γ*q.1)}).toReal)-
      (P {ω | x*Real.exp (-γ*c) < Jc ω}).toReal ≤
      ((μ.prod P) {q | x < A q*Real.exp (γ*q.1)}).toReal at hlower'
    nlinarith only [hlower',h2,he,hd,hXr,hJi]
  · have hupper' := hs.1
    change ((μ.prod P) {q | x < A q*Real.exp (γ*q.1)}).toReal ≤
      ((μ.prod P) {q | x < J q.2*Real.exp (γ*q.1)}).toReal at hupper'
    nlinarith only [hupper',h1,hXd,hXr,hJci,hXc]


end DOZZ.Proofs
