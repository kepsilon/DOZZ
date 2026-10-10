/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LogarithmicCutRate

/-! The scalar Williams model tail, with its moment and last-cut inputs explicit. -/

@[expose] public section
open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

theorem williams_model_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ × Ω → ℝ) (J : Ω → ℝ) (Jc : ℝ → Ω → ℝ)
    (hJ : Measurable J) (hJ0 : ∀ ω, 0 ≤ J ω)
    (ν γ η a r D K : ℝ) (hν : 0 < ν) (hγ : 0 < γ)
    (hη : 0 < η) (ha : η < a) (hr : 0 < r)
    (hpr : 2*ν/γ+η < (1-a)*r) (hD : 0 ≤ D) (hK : 0 ≤ K)
    (hJp : Integrable (fun ω => J ω^(2*ν/γ)) P)
    (hJr : Integrable (fun ω => J ω^r) P)
    (hJrK : (∫ ω, J ω^r ∂P) ≤ K)
    (hJcm : ∀ c : ℝ, 0 ≤ c → Measurable (Jc c))
    (hJc0 : ∀ c : ℝ, 0 ≤ c → ∀ ω, 0 ≤ Jc c ω)
    (hJcp : ∀ c : ℝ, 0 ≤ c → Integrable (fun ω => Jc c ω^(2*ν/γ)) P)
    (hJcr : ∀ c : ℝ, 0 ≤ c → Integrable (fun ω => Jc c ω^r) P)
    (hJcrK : ∀ c : ℝ, 0 ≤ c → (∫ ω, Jc c ω^r ∂P) ≤ K)
    (hupper : ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P, A q ≤ J q.2)
    (hlower : ∀ c : ℝ, 0 ≤ c →
      ∀ᵐ q ∂(brownianMaximumReferenceLaw ν).prod P, c ≤ q.1 → Jc c q.2 ≤ A q)
    (hgap : ∀ c : ℝ, 0 ≤ c → (∫ ω, J ω^(2*ν/γ) ∂P)-
      (∫ ω, Jc c ω^(2*ν/γ) ∂P) ≤ D*Real.exp (-γ*c)) :
    ∀ x : ℝ, 1 ≤ x →
      |(((brownianMaximumReferenceLaw ν).prod P) {q | x < A q*Real.exp (γ*q.1)}).toReal-
        x^(-(2*ν/γ))*(∫ ω, J ω^(2*ν/γ) ∂P)| ≤ (D+3*K)*x^(-(2*ν/γ)-η) := by
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have ha0 : 0 < a := hη.trans ha
  let c := a*Real.log x/γ
  have hc : 0 ≤ c := div_nonneg (mul_nonneg ha0.le (Real.log_nonneg hx)) hγ.le
  have hpr' : 2*ν/γ ≤ r := by nlinarith only [hpr,ha0,hr,hη]
  have ht := truncated_williams_tail_error P A J (Jc c) hJ (hJcm c hc)
    hJ0 (hJc0 c hc) ν γ x c r D hν hγ hx0 hD hpr' hJp (hJcp c hc) hJr (hJcr c hc)
    hupper (hlower c hc) (hgap c hc)
  have hrate := log_cut_error_powers_le γ a x (2*ν/γ) r η D K K
    hγ.ne' hx hη ha hr hpr hD hK hK
  have hXr : 0 ≤ x^(-r) := Real.rpow_nonneg hx0.le _
  have hXc : 0 ≤ (x*Real.exp (-γ*c))^(-r) := Real.rpow_nonneg (by positivity) _
  have hjc := hJcrK c hc
  have hb : x^(-(2*ν/γ))*(D*Real.exp (-γ*c)) +
      x^(-r)*((∫ ω, J ω^r ∂P)+(∫ ω, Jc c ω^r ∂P)) +
        (x*Real.exp (-γ*c))^(-r)*(∫ ω, Jc c ω^r ∂P) ≤
      x^(-(2*ν/γ))*(D*Real.exp (-γ*c)) + x^(-r)*(K+K) +
        (x*Real.exp (-γ*c))^(-r)*K := by
    have h1 := mul_le_mul_of_nonneg_left (add_le_add hJrK hjc) hXr
    have h2 := mul_le_mul_of_nonneg_left hjc hXc
    linarith only [h1,h2]
  have heq : D+K+2*K = D+3*K := by ring
  rw [heq] at hrate
  exact ht.trans (hb.trans hrate)


end DOZZ.Proofs
