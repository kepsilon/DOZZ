/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PinWickBound
public import DOZZ.GFFStructure.HarmonicMoments

/-! Gaussian moments for the spatial correction envelope in the one-insertion tail estimate.
The two pins may be correlated; the bound only uses their centered Gaussian marginals. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The polynomial-exponential correction envelope is bounded by a pure exponential. -/
theorem pin_envelope_le_exp (z : ℂ) (γ N Nbar : ℝ) :
    pinCorrectionEnvelope z γ N Nbar *
      Real.exp (pinCorrectionEnvelope z γ N Nbar) ≤
        Real.exp (2 * pinCorrectionEnvelope z γ N Nbar) := by
  let D := pinCorrectionEnvelope z γ N Nbar
  have h := Real.add_one_le_exp D
  calc
    _ ≤ Real.exp D * Real.exp D :=
      mul_le_mul_of_nonneg_right (by linarith : D ≤ Real.exp D) (Real.exp_nonneg D)
    _ = _ := by rw [← Real.exp_add, ← two_mul]

/-- The correction exponent is dominated by absolute pin values with a fixed coefficient. -/
theorem pin_envelope_bound (z : ℂ) (γ N Nbar a : ℝ)
    (hz : 2 ≤ ‖z‖) (ha : |γ| / (2 * Real.log ‖z‖) ≤ a) :
    pinCorrectionEnvelope z γ N Nbar ≤ a * (|Nbar| + |N|) + γ ^ 2 := by
  unfold pinCorrectionEnvelope
  apply add_le_add _ le_rfl
  exact (mul_le_mul_of_nonneg_left (abs_sub Nbar N)
    (div_nonneg (abs_nonneg γ) (offCenter_pin_variance_pos z hz).le)).trans
    (mul_le_mul_of_nonneg_right ha (add_nonneg (abs_nonneg _) (abs_nonneg _)))

/-- Gaussian exponential moments absorb the random pin correction uniformly under variance
and coefficient bounds. No independence of the original pin and its lateral field is used. -/
theorem pin_envelope_exponential_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N Nbar : Ω → ℝ) (hN : HasGaussianLaw N P) (hNb : HasGaussianLaw Nbar P)
    (hmN : (∫ ω, N ω ∂P) = 0) (hmNb : (∫ ω, Nbar ω ∂P) = 0)
    (v : ℝ) (hvN : variance N P ≤ v) (hvNb : variance Nbar P ≤ v)
    (z : ℂ) (γ a l : ℝ) (hz : 2 ≤ ‖z‖)
    (ha : |γ| / (2 * Real.log ‖z‖) ≤ a) (hl : 0 ≤ l) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp
      (l * pinCorrectionEnvelope z γ (N ω) (Nbar ω))) ∂P) ≤
        ENNReal.ofReal (Real.exp (l * γ ^ 2)) *
          ENNReal.ofReal (2 * (Real.exp (v * (2 * (l * a)) ^ 2 / 2) +
            Real.exp (v * (2 * (l * a)) ^ 2 / 2))) := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp (l * γ ^ 2)) *
        (ENNReal.ofReal (Real.exp ((l*a)*|Nbar ω|)) *
          ENNReal.ofReal (Real.exp ((l*a)*|N ω|))) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left
        (pin_envelope_bound z γ (N ω) (Nbar ω) a hz ha) hl
      nlinarith only [h]
    _ = ENNReal.ofReal (Real.exp (l * γ ^ 2)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp ((l*a)*|Nbar ω|)) *
          ENNReal.ofReal (Real.exp ((l*a)*|N ω|)) ∂P :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl
      (gaussian_product_lintegral_exp_abs_le P Nbar N hNb hN hmNb hmN
        v v hvNb hvN (l*a))

/-- Every nonnegative moment of the polynomial-exponential envelope is finite under the
same Gaussian coefficient and variance bounds. -/
theorem pin_envelope_power_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N Nbar : Ω → ℝ) (hN : HasGaussianLaw N P) (hNb : HasGaussianLaw Nbar P)
    (hmN : (∫ ω, N ω ∂P) = 0) (hmNb : (∫ ω, Nbar ω ∂P) = 0)
    (v : ℝ) (hvN : variance N P ≤ v) (hvNb : variance Nbar P ≤ v)
    (z : ℂ) (γ a r : ℝ) (hz : 2 ≤ ‖z‖)
    (ha : |γ| / (2 * Real.log ‖z‖) ≤ a) (hr : 0 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (pinCorrectionEnvelope z γ (N ω) (Nbar ω) *
      Real.exp (pinCorrectionEnvelope z γ (N ω) (Nbar ω))) ^ r ∂P) ≤
        ENNReal.ofReal (Real.exp ((2*r) * γ ^ 2)) *
          ENNReal.ofReal (2 * (Real.exp (v * (2 * ((2*r) * a)) ^ 2 / 2) +
            Real.exp (v * (2 * ((2*r) * a)) ^ 2 / 2))) := by
  apply le_trans (lintegral_mono fun ω => ?_)
    (pin_envelope_exponential_moment P N Nbar hN hNb hmN hmNb v hvN hvNb
      z γ a (2*r) hz ha (by positivity))
  have h := ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (pin_envelope_le_exp z γ (N ω) (Nbar ω))) hr
  have he : (ENNReal.ofReal (Real.exp (2 * pinCorrectionEnvelope z γ (N ω) (Nbar ω)))) ^ r =
      ENNReal.ofReal (Real.exp ((2*r) * pinCorrectionEnvelope z γ (N ω) (Nbar ω))) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
    congr 2
    ring
  exact h.trans_eq he


end DOZZ.Proofs
