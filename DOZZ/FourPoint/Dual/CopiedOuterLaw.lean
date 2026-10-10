/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.PastObservable
import Mathlib.Tactic
/-! Joint-law transport of exterior mass under independent radial reinsertion. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The full measurable reinsertion identity determines the joint law of the radial path
and exterior weighted mass, retaining every correlated terminal radial likelihood. -/
theorem dual_copied_radial_weighted_mass_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (M N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (γ : ℝ) (f : ℂ → ℝ≥0∞) (hf : Measurable f)
    (hmass : AEMeasurable (fun ω => ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) P)
    (hwhole : ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (A ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) ∂P) =
      ∫⁻ ω : Ω × Ω, G (A ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2)
          ∂P.prod P) :
    P.map (fun ω => (A ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω)) =
      (P.prod P).map (fun ω : Ω × Ω => (A ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2)) := by
  let F := fun p : TwoSidedPath × Ω => ∫⁻ x in ({0} : Set ℂ)ᶜ,
    f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
  have hFm : Measurable F := reflected_chart_parameter_mass_measurable
    ({0} : Set ℂ)ᶜ isClosed_singleton.isOpen_compl N hN hfin _
      ((hf.comp measurable_snd).mul (reflected_global_reinsertionWeight_measurable γ).ennreal_ofReal)
  have hAc : AEMeasurable (fun ω : Ω × Ω => A ω.1) (P.prod P) := hA.comp_fst
  have hpack : AEMeasurable (fun ω : Ω × Ω => (A ω.1, F (A ω.1,ω.2))) (P.prod P) :=
    hAc.prodMk (hFm.comp_aemeasurable (hAc.prodMk measurable_snd.aemeasurable))
  apply Measure.ext
  intro S hS
  let G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hG : Measurable G := measurable_const.indicator hS
  have he := hwhole G hG
  rw [← lintegral_map' hG.aemeasurable (hA.prodMk hmass), ← lintegral_map' hG.aemeasurable hpack] at he
  simpa only [G, lintegral_indicator hS, setLIntegral_one] using he

end DOZZ.Proofs
