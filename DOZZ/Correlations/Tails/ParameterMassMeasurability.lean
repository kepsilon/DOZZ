/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.SingularMassMeasurability

/-! Jointly measurable random weights against actual GMC versions. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Random parameters may depend on the field. Extended-real integrals need no
integrability assumption, including at an insertion singularity. -/
theorem gmc_parameter_lintegral_aemeasurable
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (θ : Ω → V) (hθ : AEMeasurable θ P)
    (F : V × ℂ → ℝ≥0∞) (hF : Measurable F) :
    AEMeasurable (fun ω => ∫⁻ x, F (θ ω, x) ∂M ω) P := by
  obtain ⟨N, hNm, hNf, hMN⟩ :=
    equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  let Nf : Ω → FiniteMeasure ℂ := fun ω => ⟨N ω, hNf ω⟩
  have hNfm : Measurable Nf := Measurable.subtype_mk hNm
  have hm := (measurable_lintegral_finiteMeasure_parameter hF).comp_aemeasurable
    (hθ.prodMk hNfm.aemeasurable)
  change AEMeasurable (fun ω => ∫⁻ x, F (θ ω, x) ∂N ω) P at hm
  apply hm.congr
  filter_upwards [hMN] with ω hω
  rw [hω]

/-- The real integral of a nonnegative integrable random test is measurable on the
actual GMC version, even when its parameter is correlated with the field. -/
theorem gmc_parameter_integral_aemeasurable
    {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (θ : Ω → V) (hθ : AEMeasurable θ P)
    (F : V × ℂ → ℝ) (hF : Measurable F) (hF0 : ∀ v x, 0 ≤ F (v,x))
    (hFi : ∀ ω, Integrable (fun x => F (θ ω,x)) (M ω)) :
    AEMeasurable (fun ω => ∫ x, F (θ ω,x) ∂M ω) P := by
  have hm := gmc_parameter_lintegral_aemeasurable P X hX γ hγ hγ2 M hM
    θ hθ (fun p => ENNReal.ofReal (F p)) (ENNReal.measurable_ofReal.comp hF)
  have heq (ω : Ω) : (∫⁻ x, ENNReal.ofReal (F (θ ω,x)) ∂M ω).toReal =
      ∫ x, F (θ ω,x) ∂M ω := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hFi ω)
      (ae_of_all _ fun x => hF0 _ x), ENNReal.toReal_ofReal
        (integral_nonneg (fun x => hF0 _ x))]
  simpa only [heq] using hm.ennreal_toReal



end DOZZ.Proofs
