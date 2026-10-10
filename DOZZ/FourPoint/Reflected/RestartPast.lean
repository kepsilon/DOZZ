/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.RestartedWilliams
public import DOZZ.FourPoint.Reflected.IndependentRegroup
public import DOZZ.Brownian.Williams.StoppedPaths
/-! Full stopped-past independence at the deterministic radial restart. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The entire continuous future increment path is independent of the entire stopped past. -/
theorem reflected_brownian_future_indep_stopped_past
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P) (T : ℝ≥0) :
    IndepFun (brownianShiftPath T) (fun p => stopBrownianPath p T) P := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℝ≥0)
  let _ := hSc.to_subtype
  let E : BrownianPath → (S → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval fun t => ContinuousMap.measurable_eval t.1
  have hEmb : MeasurableEmbedding E := hmE.measurableEmbedding (by
    intro p q hpq
    apply ContinuousMap.ext
    exact congrFun (hSd.denseRange_val.equalizer p.continuous q.continuous hpq))
  let r : (Iic T → ℝ) → (S → ℝ) := fun p t => p ⟨min t.1 T, min_le_right _ _⟩
  have hr : Measurable r := Measurable.of_eval fun t => measurable_pi_apply _
  let e : (ℝ≥0 → ℝ) → (S → ℝ) := fun p t => p t.1
  have he : Measurable e := Measurable.of_eval fun t => measurable_pi_apply t.1
  have hi := (hB.indepFun_shift T).comp he hr
  change IndepFun (E ∘ brownianShiftPath T) (E ∘ (fun p => stopBrownianPath p T)) P at hi
  rw [IndepFun_iff_Indep, ← MeasurableSpace.comap_comp,
    ← MeasurableSpace.comap_comp, hEmb.comap_eq] at hi
  exact (IndepFun_iff_Indep _ _ P).mpr hi

/-- Pulling the canonical stopped-past law back along the actual radial path retains it. -/
theorem reflected_radial_future_indep_stopped_past
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Ω → TwoSidedPath)
    (hA : AEMeasurable A P) (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (T : ℝ≥0) :
    IndepFun (fun ω => brownianShiftPath T (radialPositiveHalf (A ω)))
      (fun ω => stopBrownianPath (radialPositiveHalf (A ω)) T) P := by
  let _ : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let D := fun ω => radialPositiveHalf (A ω)
  have hD : AEMeasurable D P := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hs : Measurable (brownianShiftPath T) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hp : Measurable (fun p => stopBrownianPath p T) :=
    continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hDb := radialPositiveHalf_map_isBrownian P A hA hB
  have hi := (indepFun_iff_map_prod_eq_prod_map_map hs.aemeasurable hp.aemeasurable).mp
    (reflected_brownian_future_indep_stopped_past (P.map D) hDb T)
  have he := AEMeasurable.map_map_of_aemeasurable (hs.prodMk hp).aemeasurable hD
  have hsmap := AEMeasurable.map_map_of_aemeasurable hs.aemeasurable hD
  have hpmap := AEMeasurable.map_map_of_aemeasurable hp.aemeasurable hD
  rw [he, hsmap, hpmap] at hi
  exact (indepFun_iff_map_prod_eq_prod_map_map
    (hs.comp_aemeasurable hD) (hp.comp_aemeasurable hD)).mpr hi

/-- The restarted inward path is independent of both the complete exterior half and the
stopped inward half, together with any actual lateral input independent of the full path. -/
theorem reflected_radial_future_indep_full_past_lateral
    {Ω ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace ζ]
    (P : Measure Ω) (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (hhalves : IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P)
    (N : Ω → ζ) (hN : AEMeasurable N P) (hi : IndepFun A N P) (T : ℝ≥0) :
    IndepFun (fun ω => brownianShiftPath T (radialPositiveHalf (A ω)))
      (fun ω => ((stopBrownianPath (radialPositiveHalf (A ω)) T,
        radialNegativeHalf (A ω)), N ω)) P := by
  let _ : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let F : TwoSidedPath → BrownianPath := fun a => brownianShiftPath T (radialPositiveHalf a)
  let H : TwoSidedPath → BrownianPath := fun a => stopBrownianPath (radialPositiveHalf a) T
  have hF : Measurable F := continuous_brownianShiftPath.measurable.comp
    (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hH : Measurable H := continuous_stopBrownianPath.measurable.comp
    (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hminus := continuous_radialNegativeHalf.measurable.comp_aemeasurable hA
  have hplus := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hpair : IndepFun (fun ω => (F (A ω), H (A ω)))
      (fun ω => radialNegativeHalf (A ω)) P := by
    have hm : Measurable (fun p => (brownianShiftPath T p, stopBrownianPath p T)) :=
      (continuous_brownianShiftPath.measurable.comp
        (measurable_const.prodMk measurable_id)).prodMk
      (continuous_stopBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
    exact (radialHalves_indepFun P A hhalves).comp₀ hplus hminus hm.aemeasurable
      measurable_id.aemeasurable
  have hfp := reflected_radial_future_indep_stopped_past P A hA hB T
  have hfull := reflected_independence_regroup P
    (fun ω => F (A ω)) (fun ω => H (A ω)) (fun ω => radialNegativeHalf (A ω))
    (hF.comp_aemeasurable hA) (hH.comp_aemeasurable hA) hminus hfp hpair
  have hfullN : IndepFun (fun ω => (F (A ω), (H (A ω), radialNegativeHalf (A ω)))) N P :=
    hi.comp₀ hA hN (hF.prodMk (hH.prodMk continuous_radialNegativeHalf.measurable)).aemeasurable
      measurable_id.aemeasurable
  exact reflected_independence_regroup P (fun ω => F (A ω))
    (fun ω => (H (A ω), radialNegativeHalf (A ω))) N
    (hF.comp_aemeasurable hA)
    ((hH.comp_aemeasurable hA).prodMk hminus) hN hfull hfullN

end DOZZ.Proofs
