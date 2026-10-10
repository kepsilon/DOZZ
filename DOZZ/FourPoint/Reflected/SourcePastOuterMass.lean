/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.PastOuterMass
public import DOZZ.FourPoint.Reflected.SpatialBoundary
/-! The actual retained GMC mass is a stopped-past observable, shown by radial reinsertion. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Exact radial removal/reinsertion identifies the stopped-past mass code with the literal
ordinary-GMC outer mass, on one source full-measure event. -/
theorem reflected_source_outerMass_pastCode_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (A : Ω → TwoSidedPath) (N : Ω → Measure ℂ)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (A ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (α₁ α₂ α₃ ξ : ℝ) (z : ℂ) (T : ℝ≥0)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) :
    ∀ᵐ ω ∂P, reflectedPastOuterMassCode γ α₁ α₂ α₃ (‖z‖^(1-ξ)) z
      ((stopBrownianPath (radialPositiveHalf (A ω)) T,radialNegativeHalf (A ω)),N ω) =
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ := by
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  let F := fun x : ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)
  have hU : MeasurableSet U := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_insert.mpr (measurableSet_singleton (1 : ℂ)) : MeasurableSet ({0,1} : Set ℂ)).compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    have hn := hr.trans hx.1
    simpa only [mem_compl_iff,mem_singleton_iff] using norm_pos_iff.mp hn
  have hF : Measurable F := (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  filter_upwards [heq,reflected_source_outerMass_eq_comparison_region P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ ξ z hz] with ω hω ho
  rw [reflected_pastOuterMassCode_eq γ α₁ α₂ α₃ (‖z‖^(1-ξ)) z (A ω) T (N ω) hr hT (hfin ω)]
  have hW : Measurable (fun x : ℂ => ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [ho]
  change (∫⁻ x in U, F x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x) ∂N ω) =
    ∫⁻ x in U, F x ∂M ω
  rw [show (fun x : ℂ => F x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x)) =
    (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x)*F x) from
      funext fun _ => mul_comm _ _]
  have hw := setLIntegral_withDensity_eq_setLIntegral_mul (N ω) hW hF hU
  simp only [Pi.mul_apply] at hw
  rw [← hw]
  rw [hω,reflected_global_reinsertion_measure,Measure.restrict_restrict hU,inter_eq_left.mpr hU0]

end DOZZ.Proofs
