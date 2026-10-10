/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.EquatorGFFChaosTransportLaw
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! One fixed equator GMC model supplies uniform moments for translated models. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem weighted_moment_model_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (α : ℝ) (z : ℂ) (ρ t : ℝ) :
    weightedGmcBallMoment P M γ α z ρ t = weightedGmcBallMoment P' M' γ α z ρ t := by
  have hw : Measurable (fun μ : Measure ℂ => weightedGmcBallMass γ μ α z ρ) := by
    have hk : Measurable (fun x : ℂ => (ENNReal.ofReal ‖x-z‖)^(-γ*α)) :=
      ENNReal.continuous_rpow_const.measurable.comp
        (ENNReal.measurable_ofReal.comp (measurable_id.sub_const z).norm)
    have hb : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
    have hm := Measure.measurable_lintegral (hk.indicator hb)
    simpa only [lintegral_indicator hb,
      weightedGmcBallMass, ENNReal.rpow_eq_pow] using hm
  exact equatorGFF_GMC_law_transport P X hX P' X' hX' γ hγ hγ2 M hM M' hM'
    (fun _ μ => weightedGmcBallMass γ μ α z ρ ^ t)
    ((hw.comp measurable_snd).pow_const t)

/-- The uniform grid bound can be chosen before the translated GFF/GMC realization. -/
theorem weighted_moment_uniform_models
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (A g : ℝ) (hg : 0 < g) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (P' : Measure Ω) (X' : Ω → Distr) (M' : Ω → Measure ℂ),
      IsEquatorGFF P' X' → IsGMCOf P' X' γ M' →
      ∀ α t : ℝ, |α| ≤ A → 0 < t → t+g ≤ 4/γ^2 →
        t+g ≤ 2/γ*(Q γ-α) → weightedGmcBallMoment P' M' γ α 0 ρ t ≤ K := by
  obtain ⟨K, hK, hb⟩ := weightedGmcBallMoment_uniform_center P X hX γ hγ hγ2 M hM ρ hρ hρ1 A g hg
  refine ⟨K, hK, ?_⟩
  intro P' X' M' hX' hM' α t hα ht hbulk hins
  rw [← weighted_moment_model_law P X hX P' X' hX' γ hγ hγ2 M hM M' hM' α 0 ρ t]
  exact hb α t hα ht hbulk hins


end DOZZ.Proofs
