/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Probability.Independence.Basic
/-! Regrouping the independent past and lateral inputs in the reflected comparison. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
namespace DOZZ.Proofs

/-- Independence of a pair from a third input, together with independence inside the pair,
retains independence when the second and third inputs are grouped. -/
theorem reflected_independence_regroup
    {Ω α β ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace ζ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → α) (H : Ω → β) (N : Ω → ζ)
    (hF : AEMeasurable F P) (hH : AEMeasurable H P) (hN : AEMeasurable N P)
    (hFH : IndepFun F H P) (hpair : IndepFun (fun ω => (F ω, H ω)) N P) :
    IndepFun F (fun ω => (H ω, N ω)) P := by
  have hHN : IndepFun H N P := hpair.comp measurable_snd measurable_id
  have hFHlaw := (indepFun_iff_map_prod_eq_prod_map_map hF hH).mp hFH
  have hHNlaw := (indepFun_iff_map_prod_eq_prod_map_map hH hN).mp hHN
  have hpairlaw := (indepFun_iff_map_prod_eq_prod_map_map (hF.prodMk hH) hN).mp hpair
  apply (indepFun_iff_map_prod_eq_prod_map_map hF (hH.prodMk hN)).mpr
  have he := (AEMeasurable.map_map_of_aemeasurable
    MeasurableEquiv.prodAssoc.measurable.aemeasurable ((hF.prodMk hH).prodMk hN)).symm
  change P.map (fun ω => (F ω, (H ω, N ω))) =
    (P.map (fun ω => ((F ω, H ω), N ω))).map MeasurableEquiv.prodAssoc at he
  rw [he, hpairlaw, hFHlaw, Measure.prodAssoc_prod, hHNlaw]

/-- Independent source copies push forward to the product of their actual marginal laws. -/
theorem reflected_map_prod_ae
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Ω → α) (G : Ω → β)
    (hF : AEMeasurable F P) (hG : AEMeasurable G P) :
    (P.prod P).map (fun ω : Ω × Ω => (F ω.1, G ω.2)) = (P.map F).prod (P.map G) := by
  have hf : ∀ᵐ ω : Ω × Ω ∂P.prod P, F ω.1 = hF.mk F ω.1 :=
    measurePreserving_fst.quasiMeasurePreserving.ae hF.ae_eq_mk
  have hg : ∀ᵐ ω : Ω × Ω ∂P.prod P, G ω.2 = hG.mk G ω.2 :=
    measurePreserving_snd.quasiMeasurePreserving.ae hG.ae_eq_mk
  have he : (fun ω : Ω × Ω => (F ω.1, G ω.2)) =ᵐ[P.prod P]
      Prod.map (hF.mk F) (hG.mk G) := by
    filter_upwards [hf, hg] with ω hω hω'
    exact Prod.ext hω hω'
  rw [Measure.map_congr he, ← Measure.map_prod_map P P hF.measurable_mk hG.measurable_mk,
    ← Measure.map_congr hF.ae_eq_mk, ← Measure.map_congr hG.ae_eq_mk]

/-- A copied inner input retains the joint outer-past law supplied by deterministic restart. -/
theorem reflected_copied_triple_law
    {Ω α β ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace ζ]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (D : Ω → β) (Z : Ω → ζ)
    (hY : AEMeasurable Y P) (hD : AEMeasurable D P) (hZ : AEMeasurable Z P)
    (hi : IndepFun Y D P) :
    (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, (D ω.1, Z ω.2))) =
      (P.map Y).prod ((P.map D).prod (P.map Z)) := by
  have he := AEMeasurable.map_map_of_aemeasurable
    MeasurableEquiv.prodAssoc.measurable.aemeasurable
    ((hY.prodMk hD).comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving |>.prodMk
      (hZ.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving))
  change ((P.prod P).map (fun ω : Ω × Ω => ((Y ω.1, D ω.1), Z ω.2))).map
    MeasurableEquiv.prodAssoc = (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, (D ω.1, Z ω.2))) at he
  rw [← he, reflected_map_prod_ae P (fun ω => (Y ω, D ω)) Z (hY.prodMk hD) hZ,
    (indepFun_iff_map_prod_eq_prod_map_map hY hD).mp hi, Measure.prodAssoc_prod]

end DOZZ.Proofs
