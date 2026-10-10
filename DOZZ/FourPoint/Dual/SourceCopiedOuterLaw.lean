/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.CopiedOuterLaw
public import DOZZ.FourPoint.Dual.SpatialBoundary
import Mathlib.Tactic
/-! Exact source joint law of the retained exterior and radial path. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- One actual removed lateral carrier preserves the joint radial-path/outer-mass law
at every retained dual scale. The sphere boundary and insertion roots are removed using
the supplied ordinary GMC, rather than assumed absent. -/
theorem dual_source_copied_outer_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      ∀ α₁ α₂ α₃ ξ : ℝ, ∀ z : ℂ, ‖z‖ < ‖z‖^(1-ξ) →
        P.map (fun ω => (originRadialPath Xc ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)) =
          (P.prod P).map (fun ω : Ω × Ω => (originRadialPath Xc ω.1,
            ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
              ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
                ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x)
                  ∂N ω.2)) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hNm, hi, hfin, heq, _, hwhole⟩ := reflected_copied_radial_plane_observable
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  refine ⟨N, hNm, hi, hfin, heq, ?_⟩
  intro α₁ α₂ α₃ ξ z hz
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  let k := fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)
  let f := U.indicator k
  have hU : MeasurableSet U := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (Set.Finite.measurableSet (by simp)).compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx hx0
    have he : x = 0 := mem_singleton_iff.mp hx0
    exact hx.2 (by simp [he])
  have hf : Measurable f := (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal.indicator hU
  have hint (μ : Measure ℂ) : (∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂μ) = ∫⁻ x in U, k x ∂μ := by
    rw [setLIntegral_indicator hU, inter_eq_left.mpr hU0]
  have he : (fun ω => ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) =ᵐ[P]
      (fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ) := by
    filter_upwards [dual_source_outerMass_eq_comparison_region P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ z hz] with ω hω
    rw [hint]
    exact hω.symm
  have hmass := ((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).congr he.symm
  have hl := dual_copied_radial_weighted_mass_joint_law P (originRadialPath Xc)
    (originRadialPath_aemeasurable P X Xc hc hcont) M N hNm hfin γ f hf hmass (hwhole f hf)
  have hpair : (fun ω => (originRadialPath Xc ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω)) =ᵐ[P]
      (fun ω => (originRadialPath Xc ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ)) :=
    he.mono fun ω hω => Prod.ext rfl hω
  rw [Measure.map_congr hpair] at hl
  have hcopied (a : TwoSidedPath) (μ : Measure ℂ) :
      (∫⁻ x in ({0} : Set ℂ)ᶜ, f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ) =
      ∫⁻ x in U, k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ := by
    have hp : (fun x => f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) =
        U.indicator (fun x => k x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) := by
      funext x
      by_cases hx : x ∈ U <;> simp [f, hx]
    rw [hp, setLIntegral_indicator hU, inter_eq_left.mpr hU0]
  simpa only [hcopied] using hl

end DOZZ.Proofs
