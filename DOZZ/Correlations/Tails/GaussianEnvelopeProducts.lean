/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PolynomialPinEnvelope

/-! Products of the Wick pin prefactor and correlated correction envelopes. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem product_power_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E F : Ω → ℝ≥0∞) (hE : AEMeasurable E P) (hF : AEMeasurable F P)
    (r : ℝ) (hr : 0 ≤ r)
    (hEm : (∫⁻ ω, E ω ^ (r*2) ∂P) < ⊤)
    (hFm : (∫⁻ ω, F ω ^ (r*2) ∂P) < ⊤) :
    (∫⁻ ω, (E ω * F ω)^r ∂P) < ⊤ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two
    (hE.pow_const r) (hF.pow_const r)
  have h1 : (∫⁻ ω, (E ω^r)^(2 : ℝ) ∂P) < ⊤ := by
    simpa only [← ENNReal.rpow_mul] using hEm
  have h2 : (∫⁻ ω, (F ω^r)^(2 : ℝ) ∂P) < ⊤ := by
    simpa only [← ENNReal.rpow_mul] using hFm
  have hfin := lt_of_le_of_lt h (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h1.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h2.ne))
  change (∫⁻ ω, E ω ^ r * F ω ^ r ∂P) < ⊤ at hfin
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hr] using hfin

/-- Every real power of a Gaussian Wick prefactor has finite extended-real expectation. -/
theorem gaussian_wick_ennreal_power_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → ℝ)
    (hU : HasGaussianLaw U P) (γ d r : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (γ*U ω-d))^r ∂P) < ⊤ := by
  have hi := (gaussian_integrable_exp_mul P U hU (r*γ)).const_mul (Real.exp (-r*d))
  have heq (ω : Ω) : ENNReal.ofReal (Real.exp (γ*U ω-d))^r =
      ENNReal.ofReal (Real.exp (-r*d)*Real.exp ((r*γ)*U ω)) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul, ← Real.exp_add]
    congr 2
    ring
  simp_rw [heq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => by positivity)]
  exact ENNReal.ofReal_lt_top


end DOZZ.Proofs
