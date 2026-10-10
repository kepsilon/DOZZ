/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedEntranceQuantileChainMeasurable

/-!
# One finite Markov step from an independent uniform input

This measure-theoretic lemma identifies rectangle probabilities for a sampled transition from
the one-step pushforward law. It uses an ordinary two-factor product measure; no countable product
or extension theorem is involved.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal
attribute [local instance] Measure.Subtype.measureSpace

namespace DOZZ.Proofs

/-- If each fresh input `u` samples the transition law `K x`, then an independent input pair
`(x,u)` gives the Markov rectangle formula for the graph `(x,f(x,u))`. -/
theorem map_prod_graph_apply_rect
    {X U Y : Type*} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace Y]
    (μ : Measure X) (η : Measure U) [SFinite η] (f : X × U → Y) (hf : Measurable f)
    (K : X → Measure Y)
    (hK : ∀ x, η.map (fun u => f (x, u)) = K x)
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (μ.prod η).map (fun z => (z.1, f z)) (A ×ˢ B) =
      ∫⁻ x in A, K x B ∂μ := by
  let F : X × U → X × Y := fun z => (z.1, f z)
  have hF : Measurable F := measurable_fst.prodMk hf
  have hRect : MeasurableSet (A ×ˢ B) := hA.prod hB
  have hPre : MeasurableSet (F ⁻¹' (A ×ˢ B)) := hRect.preimage hF
  rw [Measure.map_apply hF hRect, Measure.prod_apply hPre]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ A
  · have hfx : Measurable (fun u => f (x, u)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hset : Prod.mk x ⁻¹' (F ⁻¹' (A ×ˢ B)) =
        (fun u => f (x, u)) ⁻¹' B := by
      ext u
      simp [F, hx]
    rw [hset, Set.indicator_of_mem hx]
    rw [← Measure.map_apply hfx hB, hK x]
  · have hset : Prod.mk x ⁻¹' (F ⁻¹' (A ×ˢ B)) = ∅ := by
      ext u
      simp [F, hx]
    rw [hset]
    simp [hx]

/-- A fresh uniform level in the subtype `(0,1)` samples the explicit transition probability
measure from every positive start. -/
theorem conditionedPositiveTransitionQuantile_map_uniformSubtype
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (x : Set.Ioi (0 : ℝ)) :
    (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
      (fun u => conditionedTransitionQuantile ν t x.1 u.1) =
        conditionedPositiveTransitionMeasure ν t x.1 := by
  let μ := conditionedPositiveTransitionMeasure ν t x.1
  let q : ℝ → ℝ := fun u =>
    cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x.1 hν ht x.2
  have hqUniform : AEMeasurable q uniformOpenUnit := by
    simpa [q, uniformOpenUnit] using
      (aemeasurable_cdfGeneralizedQuantile_Ioo μ)
  have hcoe :
      (volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val = uniformOpenUnit := by
    rw [MeasurableSet.map_coe_volume measurableSet_Ioo, uniformOpenUnit]
  have hqMap : AEMeasurable q
      ((volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val) := by
    rw [hcoe]
    exact hqUniform
  have hval : AEMeasurable (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ)
      (volume : Measure (Set.Ioo (0 : ℝ) 1)) := measurable_subtype_coe.aemeasurable
  calc
    (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
        (fun u => conditionedTransitionQuantile ν t x.1 u.1) =
      ((volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val).map q := by
        change (volume : Measure (Set.Ioo (0 : ℝ) 1)).map (fun u => q u.1) = _
        exact (AEMeasurable.map_map_of_aemeasurable hqMap hval).symm
    _ = uniformOpenUnit.map q := by rw [hcoe]
    _ = μ := by
      dsimp [q, μ]
      exact conditionedPositiveTransitionQuantile_map_uniformOpenUnit hν ht x.2

/-- The two-coordinate law of a transition driven by a fresh independent uniform variable obeys
the usual Markov rectangle formula. This is the finite-grid conditional law used in the entrance
coupling and deterministic-time cylinder argument. -/
theorem conditionedPositiveTransitionQuantile_graph_apply_rect
    (ν t : ℝ) (hν : 0 ≤ ν) (ht : 0 < t)
    (μ : Measure (Set.Ioi (0 : ℝ)))
    (A : Set (Set.Ioi (0 : ℝ))) (B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (μ.prod (volume : Measure (Set.Ioo (0 : ℝ) 1))).map
      (fun z => (z.1, conditionedTransitionQuantile ν t z.1.1 z.2.1))
      (A ×ˢ B) =
        ∫⁻ x in A, conditionedPositiveTransitionMeasure ν t x.1 B ∂μ := by
  let : IsProbabilityMeasure (volume : Measure (Set.Ioo (0 : ℝ) 1)) := by
    refine ⟨?_⟩
    have hcoe :
        (volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val = uniformOpenUnit := by
      rw [MeasurableSet.map_coe_volume measurableSet_Ioo, uniformOpenUnit]
    calc
      (volume : Measure (Set.Ioo (0 : ℝ) 1)) Set.univ =
          ((volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val) Set.univ := by
            rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
            simp
      _ = uniformOpenUnit Set.univ := by rw [hcoe]
      _ = 1 := by simp [uniformOpenUnit, Real.volume_Ioo]
  let f : Set.Ioi (0 : ℝ) × Set.Ioo (0 : ℝ) 1 → ℝ := fun z =>
    conditionedTransitionQuantile ν t z.1.1 z.2.1
  have hf : Measurable f := measurable_conditionedTransitionQuantileOn ν t hν ht
  have hK (x : Set.Ioi (0 : ℝ)) :
      (volume : Measure (Set.Ioo (0 : ℝ) 1)).map (fun u => f (x, u)) =
        conditionedPositiveTransitionMeasure ν t x.1 := by
    exact conditionedPositiveTransitionQuantile_map_uniformSubtype hν ht x
  change (μ.prod (volume : Measure (Set.Ioo (0 : ℝ) 1))).map
      (fun z => (z.1, f z)) (A ×ˢ B) = _
  exact map_prod_graph_apply_rect μ (volume : Measure (Set.Ioo (0 : ℝ) 1))
    f hf (fun x => conditionedPositiveTransitionMeasure ν t x.1) hK A B hA hB


end DOZZ.Proofs

end
