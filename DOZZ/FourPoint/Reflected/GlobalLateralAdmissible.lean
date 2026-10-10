/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalLateralCarrier
/-! Every local circle chart belongs to the same genuine global lateral carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The full punctured-plane lateral measure supplies all local admissible versions
simultaneously; chart radii may therefore tend to zero without changing the underlying carrier. -/
theorem reflected_global_lateral_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧
      IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity
        (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
        originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
        (fun ω => (N ω).restrict (originLateralChart ρ)) := by
  obtain ⟨N, hN, hi, hfin, heq⟩ := reflected_global_lateral_carrier
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  refine ⟨N, hN, hi, hfin, heq, ?_⟩
  intro ρ hρ
  let U := originLateralChart ρ
  have hU : MeasurableSet U := (isOpen_originLateralChart ρ).measurableSet
  obtain ⟨Nc, hNc, _, hcEq⟩ := exists_originLateralChartGMC_radial_removed_identity
    P X Xc hX hc hm hcont ρ γ hρ hγ hγ₂ M hM
  have hEq : Nc =ᵐ[P] (fun ω => (N ω).restrict U) := by
    filter_upwards [hcEq, heq] with ω hω hNω
    rw [hω, hNω]
  refine ⟨(measurable_measure_restrict U hU).comp hN, ?_, ?_, ?_⟩
  · intro ω
    change ((N ω).restrict U) Uᶜ = 0
    rw [Measure.restrict_apply hU.compl, compl_inter_self, measure_empty]
  · intro ω K hK hKU
    rw [Measure.restrict_apply hK.measurableSet]
    apply lt_of_le_of_lt (measure_mono inter_subset_left)
    apply hfin ω K hK
    intro x hx
    have hh : 2*ρ < ‖x‖ := hKU hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖x‖))
    simpa using hx0
  · intro f hfc hfU
    have ht := hNc.2.2.2 f hfc hfU
    have htests : (fun ω => ∫ x, f x ∂Nc ω) =ᵐ[P]
        fun ω => ∫ x, f x ∂(N ω).restrict U := by
      filter_upwards [hEq] with ω hω
      rw [hω]
    exact TendstoInMeasure.congr' (Eventually.of_forall fun _ => ae_of_all P fun _ => rfl)
      htests ht

end DOZZ.Proofs
