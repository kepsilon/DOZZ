/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionMeasureLaw
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Inversion chart law of the equator chaos. -/
theorem equatorGFF_GMC_inversion_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, H ((M ω).map (fun x => x⁻¹)) ∂P = ∫⁻ ω, H (M ω) ∂P := by
  obtain ⟨N, hNmeas, hNfin, hMN⟩ :=
    equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hN : IsGMCOf P X γ N := by
    obtain ⟨_, Xc, hXc, hconv⟩ := hM
    refine ⟨hNfin, Xc, hXc, fun f => ?_⟩
    exact tendstoInMeasure_integral_after_ae_measure_change
      (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) M N f
      (hMN.mono fun _ h => h.symm) (hconv f)
  let : IsProbabilityMeasure P := hX.1
  let A := fun ω => (N ω).map (fun z : ℂ => z⁻¹)
  have hAmeas : Measurable A := (Measure.measurable_map _ measurable_inv).comp hNmeas
  have hAfin : ∀ ω, IsFiniteMeasure (A ω) := by
    intro ω
    let := hNfin ω
    infer_instance
  have hlaw : ∫⁻ ω, H (A ω) ∂P = ∫⁻ ω, H (N ω) ∂P := by
    apply finite_random_measure_law_of_open_fdd P A N hAmeas hNmeas hAfin hNfin
    · intro ι _ U hU
      exact gmc_inversion_open_mass_fintype_law P X hX γ hγ hγ2 N hN hNmeas U hU
    · exact hH
  calc
    ∫⁻ ω, H ((M ω).map (fun x => x⁻¹)) ∂P = ∫⁻ ω, H (A ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hMN] with ω hω
      rw [hω]
    _ = ∫⁻ ω, H (N ω) ∂P := hlaw
    _ = ∫⁻ ω, H (M ω) ∂P :=
      equatorGFF_GMC_law_transport P X hX P X hX γ hγ hγ2 N hN M hM
        (fun _ μ => H μ) (hH.comp measurable_snd)

end DOZZ.Proofs
