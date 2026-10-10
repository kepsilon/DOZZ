/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ParetoCoefficient
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! First-order domination of the discarded bounded-maximum part of Williams' model. -/
@[expose] public section
open MeasureTheory Set Filter
namespace DOZZ.Proofs

/-- The signed inverse-power increment has its exact first-order majorant. -/
theorem reflected_negative_add_increment_bound (p A t : ℝ) (hp : 0 < p)
    (hA : 0 < A) (ht : 0 ≤ t) :
    |(A+t)^(-p)-A^(-p)| ≤ p*A^(-p-1)*t := by
  have hratio : 0 ≤ t/A := div_nonneg ht hA.le
  have h := reflected_negative_power_increment p (t/A) hp hratio
  have he : A+t = A*(1+t/A) := by field_simp
  have hs : (A+t)^(-p)-A^(-p) = A^(-p)*((1+t/A)^(-p)-1) := by
    rw [he, Real.mul_rpow hA.le (by linarith only [hratio])]
    ring
  rw [hs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hA.le _)]
  have hb := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hA.le (-p))
  calc
    A^(-p)*|(1+t/A)^(-p)-1| ≤ A^(-p)*(p*(t/A)) := hb
    _ = p*A^(-p-1)*t := by rw [Real.rpow_sub_one hA.ne']; ring

/-- A bounded Williams maximum and a cut below the full reflection mass are dominated by
its first moment, with the explicit retained inverse-power factor. -/
theorem reflected_bounded_maximum_increment_bound (p A b γ H m J j : ℝ)
    (hp : 0 < p) (hA : 0 < A) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hm : m ≤ H) (hj : 0 ≤ j) (hjJ : j ≤ J) :
    |(A+b*Real.exp (γ*m)*j)^(-p)-A^(-p)| ≤
      p*A^(-p-1)*b*Real.exp (γ*H)*J := by
  have ht : 0 ≤ b*Real.exp (γ*m)*j := by positivity
  have hexp : Real.exp (γ*m) ≤ Real.exp (γ*H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hm hγ)
  have hmass : b*Real.exp (γ*m)*j ≤ b*Real.exp (γ*H)*J :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexp hb) hjJ hj (by positivity)
  calc
    _ ≤ p*A^(-p-1)*(b*Real.exp (γ*m)*j) :=
      reflected_negative_add_increment_bound p A _ hp hA ht
    _ ≤ p*A^(-p-1)*(b*Real.exp (γ*H)*J) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

/-- The bounded-maximum contribution is integrable and is controlled by precisely the
outer first-order inverse moment and the reflection first moment. -/
theorem reflected_bounded_maximum_expectation_bound
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p γ H : ℝ) (hp : 0 < p) (hγ : 0 ≤ γ)
    (A b : Ω → ℝ) (m J j : Λ → ℝ)
    (hA : ∀ᵐ ω ∂P, 0 < A ω) (hb : ∀ᵐ ω ∂P, 0 ≤ b ω)
    (hj : ∀ᵐ v ∂R, 0 ≤ j v ∧ j v ≤ J v)
    (hF : Integrable (fun ω => b ω*(A ω)^(-p-1)) P) (hJ : Integrable J R)
    (hE : AEStronglyMeasurable (fun v : Ω × Λ => if m v.2 ≤ H then
      (A v.1+b v.1*Real.exp (γ*m v.2)*j v.2)^(-p)-(A v.1)^(-p) else 0) (P.prod R)) :
    Integrable (fun v : Ω × Λ => if m v.2 ≤ H then
      (A v.1+b v.1*Real.exp (γ*m v.2)*j v.2)^(-p)-(A v.1)^(-p) else 0) (P.prod R) ∧
    |∫ v : Ω × Λ, (if m v.2 ≤ H then
      (A v.1+b v.1*Real.exp (γ*m v.2)*j v.2)^(-p)-(A v.1)^(-p) else 0) ∂P.prod R| ≤
        p*Real.exp (γ*H)*(∫ ω, b ω*(A ω)^(-p-1) ∂P)*(∫ v, J v ∂R) := by
  let F := fun ω => b ω*(A ω)^(-p-1)
  let C := p*Real.exp (γ*H)
  have hdom : Integrable (fun v : Ω × Λ => C*(F v.1*J v.2)) (P.prod R) :=
    (hF.mul_prod hJ).const_mul C
  have hbound : ∀ᵐ v : Ω × Λ ∂P.prod R,
      ‖(if m v.2 ≤ H then
        (A v.1+b v.1*Real.exp (γ*m v.2)*j v.2)^(-p)-(A v.1)^(-p) else 0)‖ ≤
      C*(F v.1*J v.2) := by
    have hfst := measurePreserving_fst (μ := P) (ν := R)
    have hsnd := measurePreserving_snd (μ := P) (ν := R)
    filter_upwards [hfst.quasiMeasurePreserving.ae hA, hfst.quasiMeasurePreserving.ae hb,
      hsnd.quasiMeasurePreserving.ae hj] with v hAv hbv hjv
    by_cases hm : m v.2 ≤ H
    · rw [ite_eq_left hm, Real.norm_eq_abs]
      have hh := reflected_bounded_maximum_increment_bound p (A v.1) (b v.1) γ H
        (m v.2) (J v.2) (j v.2) hp hAv hbv hγ hm hjv.1 hjv.2
      convert hh using 1
      dsimp only [C,F]
      ring
    · rw [ite_eq_right hm, norm_zero]
      have hJv : 0 ≤ J v.2 := hjv.1.trans hjv.2
      dsimp only [C,F]
      positivity
  refine ⟨hdom.mono' hE hbound, ?_⟩
  have hi := norm_integral_le_of_norm_le hdom hbound
  rw [integral_const_mul, integral_prod_mul] at hi
  simpa only [Real.norm_eq_abs, C,F,mul_assoc] using hi

end DOZZ.Proofs
