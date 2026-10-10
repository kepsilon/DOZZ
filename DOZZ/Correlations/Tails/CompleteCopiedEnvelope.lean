/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GaussianEnvelopeProducts

/-! The complete error envelope of the one-insertion tail includes the copied lognormal pin. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

theorem complete_copied_error_envelope_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N Nbar : Ω → ℝ) (hN : HasGaussianLaw N P) (hNb : HasGaussianLaw Nbar P)
    (hmN : (∫ ω, N ω ∂P) = 0) (hmNb : (∫ ω, Nbar ω ∂P) = 0)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ d s r : ℝ)
    (hd : 0 ≤ d) (hs : 0 ≤ s) (hr : 0 ≤ r) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (γ*Nbar ω-γ^2*Real.log ‖z‖) *
      ((d+s*(pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))*
        Real.exp (pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))) ^ r ∂P) < ⊤ := by
  let S := fun ω => ENNReal.ofReal (Real.exp (γ*Nbar ω-γ^2*Real.log ‖z‖))
  let E := fun ω => ENNReal.ofReal
    ((d+s*(pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))*
      Real.exp (pinCorrectionEnvelope z γ (N ω) (Nbar ω)+4))
  have hSm : AEMeasurable S P :=
    ((hNb.aemeasurable.const_mul γ).sub_const _).exp.ennreal_ofReal
  have hDm : AEMeasurable (fun ω => pinCorrectionEnvelope z γ (N ω) (Nbar ω)) P := by
    unfold pinCorrectionEnvelope
    exact ((continuous_abs.measurable.comp_aemeasurable
      (hNb.aemeasurable.sub hN.aemeasurable)).const_mul _).add_const _
  have hEm : AEMeasurable E P :=
    ((((hDm.add_const 4).const_mul s).const_add d).mul (hDm.add_const 4).exp).ennreal_ofReal
  have hm := product_power_moment_lt_top P S E hSm hEm r hr
    (gaussian_wick_ennreal_power_lt_top P Nbar hNb γ (γ^2*Real.log ‖z‖) (r*2))
    (polynomial_pin_envelope_moment P N Nbar hN hNb hmN hmNb z hz γ d s (r*2)
      hd hs (by positivity))
  simpa only [S, E, ENNReal.ofReal_mul (Real.exp_nonneg _)] using hm


end DOZZ.Proofs
