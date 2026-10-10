/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.IndependentRegroup
public import Mathlib.MeasureTheory.Integral.Prod
/-! Regrouping a common radial path and two independent lateral carriers. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_map_two_measures_prod_ae
    {Ω Λ α β : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (F : Ω → α) (G : Λ → β) (hF : AEMeasurable F P) (hG : AEMeasurable G R) :
    (P.prod R).map (fun ω : Ω × Λ => (F ω.1,G ω.2)) = (P.map F).prod (R.map G) := by
  have hf : ∀ᵐ ω : Ω × Λ ∂P.prod R, F ω.1 = hF.mk F ω.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hF.ae_eq_mk
  have hg : ∀ᵐ ω : Ω × Λ ∂P.prod R, G ω.2 = hG.mk G ω.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae hG.ae_eq_mk
  have he : (fun ω : Ω × Λ => (F ω.1,G ω.2)) =ᵐ[P.prod R]
      Prod.map (hF.mk F) (hG.mk G) := by
    filter_upwards [hf,hg] with ω hω hω'
    exact Prod.ext hω hω'
  rw [Measure.map_congr he,← Measure.map_prod_map P R hF.measurable_mk hG.measurable_mk,
    ← Measure.map_congr hF.ae_eq_mk,← Measure.map_congr hG.ae_eq_mk]

theorem reflected_copied_carrier_regroup
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Ω → α) (N : Ω → β)
    (hA : AEMeasurable A P) (hN : Measurable N) (hi : IndepFun A N P)
    (G : α × (β × β) → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p : α × (Ω × Ω), G (p.1,(N p.2.1,N p.2.2)) ∂(P.map A).prod (P.prod P)) =
      ∫⁻ ω : Ω × Ω, G (A ω.1,(N ω.2,N ω.1)) ∂P.prod P := by
  let H : α × (Ω × Ω) → α × (β × β) := fun p => (p.1,(N p.2.1,N p.2.2))
  have hH : Measurable H := measurable_fst.prodMk
    ((hN.comp (measurable_fst.comp measurable_snd)).prodMk
      (hN.comp (measurable_snd.comp measurable_snd)))
  have hlaw : ((P.map A).prod (P.prod P)).map H =
      (P.map A).prod ((P.map N).prod (P.map N)) := by
    change ((P.map A).prod (P.prod P)).map (Prod.map id (Prod.map N N)) = _
    rw [← Measure.map_prod_map _ _ measurable_id (hN.prodMap hN), Measure.map_id]
    rw [Measure.map_prod_map P P hN hN]
  have hbase (F : α × (β × β) → ℝ≥0∞) (hF : Measurable F) :
      (∫⁻ p : α × (Ω × Ω), F (H p) ∂(P.map A).prod (P.prod P)) =
        ∫⁻ ω : Ω × Ω, F (A ω.1,(N ω.1,N ω.2)) ∂P.prod P := by
    rw [← lintegral_map hF hH, hlaw,
      ← reflected_copied_triple_law P A N N hA hN.aemeasurable hN.aemeasurable hi]
    exact lintegral_map' hF.aemeasurable
      ((hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
        ((hN.aemeasurable.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
          (hN.aemeasurable.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)))
  let F : α × (β × β) → ℝ≥0∞ := fun p => G (p.1,(p.2.2,p.2.1))
  have hF : Measurable F := hG.comp (measurable_fst.prodMk
    ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd)))
  rw [← hbase F hF]
  change (∫⁻ p, G (H p) ∂(P.map A).prod (P.prod P)) =
    ∫⁻ p : α × (Ω × Ω), G (p.1,(N p.2.2,N p.2.1)) ∂(P.map A).prod (P.prod P)
  change (∫⁻ p, (G ∘ H) p ∂(P.map A).prod (P.prod P)) =
    ∫⁻ p, (F ∘ H) p ∂(P.map A).prod (P.prod P)
  rw [lintegral_prod _ (hG.comp hH).aemeasurable,
    lintegral_prod _ (hF.comp hH).aemeasurable]
  apply lintegral_congr
  intro a
  exact (lintegral_prod_swap (fun p : Ω × Ω => G (a,(N p.1,N p.2)))).symm

end DOZZ.Proofs
