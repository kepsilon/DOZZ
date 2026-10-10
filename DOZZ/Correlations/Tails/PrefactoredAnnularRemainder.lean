/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.AnnularRemainderMoments
public import DOZZ.Correlations.Tails.ActualPrefactorUniform
public import DOZZ.Correlations.Tails.TranslatedSourceMass

/-! Actual independent pin moments control the canonical annular remainder uniformly. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem prefactored_annular_remainder_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) (f α ρ : ℝ)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N) :
    AEMeasurable (fun q : Ω × Ω =>
      ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
        ∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) ρ,
          (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1) (P.prod P) := by
  let : IsProbabilityMeasure P := hX.1
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hk : Measurable (fun x : ℂ => (ENNReal.ofReal ‖x‖)^(-γ*α)) := by fun_prop
  have hd : MeasurableSet (Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) ρ) :=
    Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hm := (Measure.measurable_lintegral (hk.indicator hd)).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P _ hY γ hγ hγ2 N hN)
  have hmass : AEMeasurable (fun ω => ∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) ρ,
      (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N ω) P := by
    simpa only [lintegral_indicator hd,Function.comp_def] using hm
  have hpin := (hc.1 0).comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : Ω => z)))
  have hS := (((((hpin.comp (measurable_snd : Measurable (Prod.snd : Ω × Ω → Ω))).const_mul γ).sub_const (γ^2*Real.log ‖z‖)).exp).const_mul
    (f*‖z‖^(-4 : ℝ))).ennreal_ofReal
  exact hS.aemeasurable.mul (hmass.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving)

theorem prefactored_annular_remainder_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    (ρ A b R : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb : 0 ≤ b)
    (hR : 0 < R) (hRbulk : R < 4/γ^2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ f : ℝ, 0 ≤ f → f ≤ b →
      ∀ N : Ω → Measure ℂ, IsGMCOf P (translatedField X Xc z) γ N →
      ∀ α r : ℝ, 0 ≤ α → α ≤ A → 0 < r → r ≤ R →
      (∫⁻ q : Ω × Ω,
        (ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
          ∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) ρ,
            (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)^r ∂P.prod P) ≤ C := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨D,hD,hMass⟩ := annular_remainder_moment_uniform_models
    P X hX γ hγ hγ2 M hM {0} isCompact_singleton ρ A 1 R hρ hρ1 zero_le_one hR hRbulk
  obtain ⟨L,hL,hPin⟩ := actual_prefactor_moment_uniform
    P X Xc hX hc K hK hz γ b R hb hR
  refine ⟨D*L,ENNReal.mul_lt_top hD hL,?_⟩
  intro z hzk f hf hfb N hN α r hα hαA hr hrR
  let S : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))
  let mass : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) ρ,
    (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N ω
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hpin := (hc.1 0).comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : Ω => z)))
  have hS : Measurable S := ((((hpin.const_mul γ).sub_const _).exp).const_mul _).ennreal_ofReal
  have hk : Measurable (fun x : ℂ => (ENNReal.ofReal ‖x‖)^(-γ*α)) := by fun_prop
  have hd : MeasurableSet (Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) ρ) :=
    Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hmass : AEMeasurable mass P := by
    have h := (Measure.measurable_lintegral (hk.indicator hd)).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P _ hY γ hγ hγ2 N hN)
    simpa only [mass,lintegral_indicator hd,Function.comp_def] using h
  have hm : (∫⁻ ω, mass ω^r ∂P) ≤ D := by
    have h := hMass P _ N hY hN 0 (mem_singleton 0) α r hα hαA hr hrR
      (fun _ => 1) measurable_const (fun _ => ⟨zero_le_one,le_rfl⟩)
    simpa only [mass,sub_zero,ENNReal.ofReal_one,one_mul] using h
  change (∫⁻ q : Ω × Ω, (S q.2*mass q.1)^r ∂P.prod P) ≤ D*L
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,mul_comm (S _^r)]
  rw [lintegral_prod_mul (hmass.pow_const r) (hS.aemeasurable.pow_const r)]
  exact mul_le_mul' hm (hPin z hzk f hf hfb r hr hrR)


end DOZZ.Proofs
