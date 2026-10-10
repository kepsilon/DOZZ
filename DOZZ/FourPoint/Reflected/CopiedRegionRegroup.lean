/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedCarrierRegroup
public import DOZZ.FourPoint.Reflected.ReinsertedRegionCode
/-! Exact regrouping of the literal reinserted inner and exterior masses. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_copied_reinserted_regions_regroup
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → TwoSidedPath) (N : Ω → Measure ℂ)
    (hA : AEMeasurable A P) (hN : Measurable N) (hi : IndepFun A N P)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (γ : ℝ) (U V : Set ℂ) (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hU0 : U ⊆ ({0} : Set ℂ)ᶜ) (hV0 : V ⊆ ({0} : Set ℂ)ᶜ)
    (K : ℂ → ℝ≥0∞) (hK : Measurable K)
    (F : ℝ≥0∞ × ℝ≥0∞ → ℝ≥0∞) (hF : Measurable F) :
    let J := fun (W : Set ℂ) (a : TwoSidedPath) (ω : Ω) =>
      ∫⁻ x in W, K x*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
    (∫⁻ p : TwoSidedPath × (Ω × Ω), F (J U p.1 p.2.1,J V p.1 p.2.2)
      ∂(P.map A).prod (P.prod P)) =
    ∫⁻ ω : Ω × Ω, F (J U (A ω.1) ω.2,J V (A ω.1) ω.1) ∂P.prod P := by
  let CU := reflectedReinsertedRegionMassCode γ U K
  let CV := reflectedReinsertedRegionMassCode γ V K
  let G : TwoSidedPath × (Measure ℂ × Measure ℂ) → ℝ≥0∞ :=
    fun p => F (CU (p.1,p.2.1),CV (p.1,p.2.2))
  have hG : Measurable G := hF.comp
    (((reflected_reinsertedRegionMassCode_measurable γ U hU K hK).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    ((reflected_reinsertedRegionMassCode_measurable γ V hV K hK).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
  have he := reflected_copied_carrier_regroup P A N hA hN hi G hG
  dsimp only [G,CU,CV] at he
  simp_rw [reflected_reinsertedRegionMassCode_eq γ U hU hU0 K _ _ (hfin _),
    reflected_reinsertedRegionMassCode_eq γ V hV hV0 K _ _ (hfin _)] at he
  exact he

theorem reflected_copied_region_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → TwoSidedPath) (N : Ω → Measure ℂ) (hA : AEMeasurable A P) (hN : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (γ : ℝ) (U : Set ℂ) (hU : MeasurableSet U) (hU0 : U ⊆ ({0} : Set ℂ)ᶜ)
    (K : ℂ → ℝ≥0∞) (hK : Measurable K) :
    AEMeasurable (fun ω : Ω × Ω => ∫⁻ x in U,
      K x*ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2) (P.prod P) := by
  have hm := (reflected_reinsertedRegionMassCode_measurable γ U hU K hK).comp_aemeasurable
    ((hA.comp_quasiMeasurePreserving (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving).prodMk
      (hN.aemeasurable.comp_quasiMeasurePreserving (measurePreserving_snd (μ := P) (ν := P)).quasiMeasurePreserving))
  apply hm.congr
  exact Filter.Eventually.of_forall fun ω =>
    reflected_reinsertedRegionMassCode_eq γ U hU hU0 K (A ω.1) (N ω.2) (hfin ω.2)

end DOZZ.Proofs
