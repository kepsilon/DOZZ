/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.PlaneMassCode
public import DOZZ.FourPoint.Reflected.GlobalReinsertion
/-! Joint mass codes identify the copied spatial observable under product-law regrouping. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

noncomputable def reflectedReinsertedRegionMassCode (γ : ℝ) (U : Set ℂ) (K : ℂ → ℝ≥0∞)
    (p : TwoSidedPath × Measure ℂ) : ℝ≥0∞ :=
  reflectedPuncturedMassCode (fun q : TwoSidedPath × ℂ => U.indicator
    (fun x => K x*ENNReal.ofReal (reflected_global_reinsertionWeight γ q.1 x)) q.2) p

theorem reflected_reinsertedRegionMassCode_measurable (γ : ℝ) (U : Set ℂ) (hU : MeasurableSet U)
    (K : ℂ → ℝ≥0∞) (hK : Measurable K) : Measurable (reflectedReinsertedRegionMassCode γ U K) := by
  apply reflected_puncturedMassCode_measurable
  exact Measurable.ite (hU.preimage measurable_snd)
    ((hK.comp measurable_snd).mul (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal) measurable_const

theorem reflected_reinsertedRegionMassCode_eq (γ : ℝ) (U : Set ℂ) (hU : MeasurableSet U)
    (hU0 : U ⊆ ({0} : Set ℂ)ᶜ) (K : ℂ → ℝ≥0∞) (a : TwoSidedPath) (μ : Measure ℂ)
    (hfin : ∀ K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → μ K < ⊤) :
    reflectedReinsertedRegionMassCode γ U K (a,μ) =
      ∫⁻ x in U, K x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ := by
  rw [reflectedReinsertedRegionMassCode,reflected_puncturedMassCode_eq _ _ _ hfin]
  dsimp only [Prod.fst,Prod.snd]
  rw [setLIntegral_indicator hU,inter_eq_left.mpr hU0]

/-- Exact removal and reinsertion recover any measurable regional mass away from the origin. -/
theorem reflected_reinserted_region_eq (γ : ℝ) (a : TwoSidedPath) (μ : Measure ℂ)
    (U : Set ℂ) (hU : MeasurableSet U) (hU0 : U ⊆ ({0} : Set ℂ)ᶜ)
    (K : ℂ → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ x in U, K x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)
      ∂μ.withDensity (lateralRadialWeight γ a)) = ∫⁻ x in U, K x ∂μ := by
  have hW : Measurable (fun x : ℂ => ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [show (fun x : ℂ => K x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) =
    (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)*K x) from
      funext fun _ => mul_comm _ _]
  have hw := setLIntegral_withDensity_eq_setLIntegral_mul
    (μ.withDensity (lateralRadialWeight γ a)) hW hK hU
  simp only [Pi.mul_apply] at hw
  rw [← hw,reflected_global_reinsertion_measure,Measure.restrict_restrict hU,
    inter_eq_left.mpr hU0]

end DOZZ.Proofs
