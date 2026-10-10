/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PinEnvelopeMoment
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Finite moments of the complete first-order copied-multiplier envelope. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The first-order coefficient is absorbed by a pure exponential of the pin correction. -/
theorem polynomial_pin_envelope_le (D d s : ℝ)
    (hD : 0 ≤ D) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    (d+s*(D+4))*Real.exp (D+4) ≤
      ((d+5*s)*Real.exp 4)*Real.exp (2*D) := by
  have he : 1 ≤ Real.exp D := Real.one_le_exp hD
  have hDe : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hc : d+s*(D+4) ≤ (d+5*s)*Real.exp D := by
    have h1 := mul_le_mul_of_nonneg_left he hd
    have h2 := mul_le_mul_of_nonneg_left hDe hs
    have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*s by positivity)
    nlinarith only [h1,h2,h3]
  calc
    _ ≤ ((d+5*s)*Real.exp D)*Real.exp (D+4) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = _ := by
      simp_rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Gaussian pin corrections have finite polynomial-exponential moments. The two pins
may be correlated; no independence is used. -/
theorem polynomial_pin_envelope_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N Nbar : Ω → ℝ) (hN : HasGaussianLaw N P) (hNb : HasGaussianLaw Nbar P)
    (hmN : (∫ ω, N ω ∂P) = 0) (hmNb : (∫ ω, Nbar ω ∂P) = 0)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ d s r : ℝ)
    (hd : 0 ≤ d) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal ((d+s*(pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))*
      Real.exp (pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4)) ^ r ∂P) < ⊤ := by
  let K := (d+5*s)*Real.exp 4
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hD (ω : Ω) : 0 ≤ pinCorrectionEnvelope z γ (N ω) (Nbar ω) := by
    unfold pinCorrectionEnvelope
    exact add_nonneg (mul_nonneg
      (div_nonneg (abs_nonneg _) (offCenter_pin_variance_pos z hz).le)
      (abs_nonneg _)) (sq_nonneg _)
  have hb := pin_envelope_exponential_moment P N Nbar hN hNb hmN hmNb
    (max (variance N P) (variance Nbar P)) (le_max_left _ _) (le_max_right _ _)
    z γ (|γ|/(2*Real.log ‖z‖)) (2*r) hz le_rfl (by positivity)
  have hfin : (∫⁻ ω, ENNReal.ofReal (Real.exp
      ((2*r)*pinCorrectionEnvelope z γ (N ω) (Nbar ω))) ∂P) < ⊤ :=
    lt_of_le_of_lt hb (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal K)^r * ENNReal.ofReal (Real.exp
        ((2*r)*pinCorrectionEnvelope z γ (N ω) (Nbar ω))) ∂P := by
      apply lintegral_mono
      intro ω
      have h := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (polynomial_pin_envelope_le _ d s (hD ω) hd hs)) hr
      rw [ENNReal.ofReal_mul hK, ENNReal.mul_rpow_of_nonneg _ _ hr,
        ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul] at h
      have he : (2*pinCorrectionEnvelope z γ (N ω) (Nbar ω))*r =
          (2*r)*pinCorrectionEnvelope z γ (N ω) (Nbar ω) := by ring
      simpa only [he] using h
    _ = (ENNReal.ofReal K)^r * ∫⁻ ω, ENNReal.ofReal (Real.exp
        ((2*r)*pinCorrectionEnvelope z γ (N ω) (Nbar ω))) ∂P :=
      lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg hr ENNReal.ofReal_ne_top).ne
    _ < ⊤ := ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hr ENNReal.ofReal_ne_top) hfin


end DOZZ.Proofs
