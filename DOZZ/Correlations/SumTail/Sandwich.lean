/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SumTail.JointPowers
public import DOZZ.Correlations.Tails.TwoMassHalfThreshold
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! The sharp sum-tail estimate from the proved event sandwiches. -/

@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs

/-- The source's lower inclusion-exclusion and upper half-threshold bounds retain all six
ceiling constraints. The constant is independent of the particular exponents below `T`. -/
theorem sumtail_real_sum_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → ℝ) (hB : AEMeasurable B P) (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω)
    (T p2 p3 e2 e3 d ε β θ C H D c2 c3 : ℝ)
    (hp2 : 0 < p2) (hp3 : 0 < p3) (hp2T : p2 ≤ T) (hp3T : p3 ≤ T)
    (he2 : e2 ≤ 1) (he3 : e3 ≤ 1) (hd : 0 ≤ d) (hdθ : d ≤ θ)
    (hε : 0 ≤ ε) (hεθ : 2*ε ≤ θ) (hC : 0 ≤ C) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hc2 : |c2| ≤ H) (hc3 : |c3| ≤ H)
    (hβe2 : β ≤ p2+e2) (hβe3 : β ≤ p3+e3)
    (hβs2 : β ≤ p2+1/2) (hβs3 : β ≤ p3+1/2)
    (hβj2 : β ≤ p2+p3/2) (hβj3 : β ≤ p3+p2/2)
    (hone2 : ∀ x : ℝ, 1 ≤ x → |P.real {ω | x < A ω}-c2*x^(-p2)| ≤ C*x^(-p2-e2+d))
    (hone3 : ∀ x : ℝ, 1 ≤ x → |P.real {ω | x < B ω}-c3*x^(-p3)| ≤ C*x^(-p3-e3+d))
    (hjoint : ∀ u v : ℝ, 1 ≤ u → 1 ≤ v →
      P.real {ω | u < A ω ∧ v < B ω} ≤ D*u^(-p2+ε)*v^(-p3+ε)) :
    ∀ x : ℝ, 1 ≤ x → |P.real {ω | x < A ω+B ω}-(c2*x^(-p2)+c3*x^(-p3))| ≤
      ((1+2*H)*4^(T+1)+(2*C+D+2*((C+H*T)*2^(T+1))+2*D*2^T))*x^(-β+θ) := by
  have hT : 0 ≤ T := hp2.le.trans hp2T
  have hθ : 0 ≤ θ := hd.trans hdθ
  have hCb : 0 ≤ 2*C+D+2*((C+H*T)*2^(T+1))+2*D*2^T := by positivity
  have hCs : 0 ≤ (1+2*H)*4^(T+1) := by positivity
  intro x hx
  have hx0 : 0 < x := by linarith only [hx]
  have hpow : 0 ≤ x^(-β+θ) := Real.rpow_nonneg hx0.le _
  by_cases hx4 : 4 ≤ x
  · have hxt : 1 ≤ x-Real.sqrt x := by
      have := (sumtail_sqrt_shift_bounds x hx4).2.1
      linarith only [hx4,this]
    have hxhalf : 1 ≤ x/2 := by linarith only [hx4]
    have hxsqrt := (sumtail_sqrt_shift_bounds x hx4).1
    have he2x : |P.real {ω | x < A ω}-c2*x^(-p2)| ≤ C*x^(-β+θ) :=
      (hone2 x hx).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hβe2,hdθ])) hC)
    have he3x : |P.real {ω | x < B ω}-c3*x^(-p3)| ≤ C*x^(-β+θ) :=
      (hone3 x hx).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hβe3,hdθ])) hC)
    have hs2 := sumtail_shifted_one_error (fun t => P.real {ω | t < A ω}) T p2 e2 d θ β C H c2 x
      hp2 hp2T he2 hd hdθ hC hH hc2 hx4 hβe2 hβs2 (hone2 _ hxt)
    have hs3 := sumtail_shifted_one_error (fun t => P.real {ω | t < B ω}) T p3 e3 d θ β C H c3 x
      hp3 hp3T he3 hd hdθ hC hH hc3 hx4 hβe3 hβs3 (hone3 _ hxt)
    have hjx : P.real {ω | x < A ω ∧ x < B ω} ≤ D*x^(-β+θ) := by
      have hb := hjoint x x hx hx
      calc
        _ ≤ D*(x^(-p2+ε)*x^(-p3+ε)) := by simpa only [mul_assoc] using hb
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (sumtail_joint_equal_power p2 p3 ε β θ x hp3.le hεθ hβj2 hx) hD
    have hεθ' : 3*ε/2 ≤ θ := by linarith only [hε,hεθ]
    have hj1 : P.real {ω | x/2 < A ω ∧ Real.sqrt x < B ω} ≤ D*2^T*x^(-β+θ) := by
      have hb := hjoint (x/2) (Real.sqrt x) hxhalf hxsqrt
      calc
        _ ≤ D*((x/2)^(-p2+ε)*(Real.sqrt x)^(-p3+ε)) := by simpa only [mul_assoc] using hb
        _ ≤ D*(2^T*x^(-β+θ)) := mul_le_mul_of_nonneg_left
          (sumtail_joint_half_sqrt_power T p2 p3 ε β θ x hT hp2T hε hεθ' hβj2 hx4) hD
        _ = _ := by ring
    have hj2 : P.real {ω | Real.sqrt x < A ω ∧ x/2 < B ω} ≤ D*2^T*x^(-β+θ) := by
      have hb := hjoint (Real.sqrt x) (x/2) hxsqrt hxhalf
      calc
        _ ≤ D*((x/2)^(-p3+ε)*(Real.sqrt x)^(-p2+ε)) := by
          convert hb using 1
          ring
        _ ≤ D*(2^T*x^(-β+θ)) := mul_le_mul_of_nonneg_left
          (sumtail_joint_half_sqrt_power T p3 p2 ε β θ x hT hp3T hε hεθ' hβj3 hx4) hD
        _ = _ := by ring
    have hlo := (two_mass_tail_sandwich P A B hB hA0 hB0 x (Real.sqrt x)).1
    have hhi := two_mass_tail_half_threshold P A B x (Real.sqrt x)
    have hlo2 := (abs_le.mp he2x).1
    have hlo3 := (abs_le.mp he3x).1
    have hhi2 := (abs_le.mp hs2).2
    have hhi3 := (abs_le.mp hs3).2
    have herr : |P.real {ω | x < A ω+B ω}-(c2*x^(-p2)+c3*x^(-p3))| ≤
        (2*C+D+2*((C+H*T)*2^(T+1))+2*D*2^T)*x^(-β+θ) := by
      apply abs_le.mpr
      constructor <;> nlinarith only [hlo,hhi,hlo2,hlo3,hhi2,hhi3,hjx,hj1,hj2,
        mul_nonneg hCs hpow, mul_nonneg hC hpow, mul_nonneg hD hpow,
        mul_nonneg (show 0 ≤ (C+H*T)*2^(T+1) by positivity) hpow,
        mul_nonneg (show 0 ≤ D*2^T by positivity) hpow]
    exact herr.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCs) hpow)
  · have hβT : β ≤ T+1 := by linarith only [hβs2,hp2T]
    have hsmall := sumtail_small_power_absorption (T+1) β θ x (by positivity) hβT hθ hx (le_of_not_ge hx4)
    have hp2one : x^(-p2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith only [hp2])
    have hp3one : x^(-p3) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith only [hp3])
    have hcoef2 : |c2*x^(-p2)| ≤ H := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact (mul_le_mul_of_nonneg_right hc2 (Real.rpow_nonneg hx0.le _)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp2one hH)
    have hcoef3 : |c3*x^(-p3)| ≤ H := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact (mul_le_mul_of_nonneg_right hc3 (Real.rpow_nonneg hx0.le _)).trans
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp3one hH)
    calc
      _ ≤ |P.real {ω | x < A ω+B ω}|+|c2*x^(-p2)+c3*x^(-p3)| := abs_sub _ _
      _ ≤ 1+(H+H) := add_le_add
        (by rw [abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one)
        ((abs_add_le _ _).trans (add_le_add hcoef2 hcoef3))
      _ ≤ ((1+2*H)*4^(T+1))*x^(-β+θ) := by nlinarith only [hsmall,hH]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCb) hpow

end DOZZ.Proofs
