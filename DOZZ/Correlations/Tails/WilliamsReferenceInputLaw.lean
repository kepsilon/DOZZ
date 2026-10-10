/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsInputCode

/-! Regroup the Williams reference law as level times conditioned-pair/lateral input. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem williams_reference_input_law
    (γ ν : ℝ) (hν : 0 < ν) (Qν : Measure BrownianPath) [IsProbabilityMeasure Qν]
    (L : Measure (Measure ℝ)) [IsProbabilityMeasure L]
    (hfin : ∀ᵐ Z ∂L, ∀ a b : ℝ, Z (Icc a b) < ⊤) :
    (((((brownianMaximumReferenceLaw ν).prod Qν).map
      (fun v => (v.1,negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod L).map
        (williamsMassFunctional γ) =
    ((brownianMaximumReferenceLaw ν).prod ((Qν.prod Qν).prod L)).map
      (williamsInputMassCode γ) := by
  let μ := brownianMaximumReferenceLaw ν
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw hν
  let Raw := ((ℝ × BrownianPath) × BrownianPath) × Measure ℝ
  let R : Measure Raw := ((μ.prod Qν).prod Qν).prod L
  let mark := fun v : ℝ × BrownianPath => (v.1,negativeConditionedLastExitSegment v.1 v.2)
  have hmark : Measurable mark := measurable_fst.prodMk measurable_lastExitSegment_joint
  let H : Raw → ((ℝ × StoppedBrownianPath) × BrownianPath) × Measure ℝ :=
    Prod.map (Prod.map mark id) id
  have hH : Measurable H := (hmark.prodMap measurable_id).prodMap measurable_id
  have hMarked : (((μ.prod Qν).map mark).prod Qν).prod L = R.map H := by
    rw [← Measure.map_id (μ := Qν), Measure.map_prod_map _ _ hmark measurable_id,
      ← Measure.map_id (μ := L), Measure.map_prod_map _ _ (hmark.prodMap measurable_id) measurable_id]
    simp only [Measure.map_id]
    rfl
  rw [hMarked,Measure.map_map (measurable_williamsMassFunctional γ) hH]
  let T : Raw → ℝ × ((BrownianPath × BrownianPath) × Measure ℝ) :=
    fun w => (w.1.1.1,((w.1.2,w.1.1.2),w.2))
  have hT : MeasurePreserving T R (μ.prod ((Qν.prod Qν).prod L)) := by
    have h1 := (measurePreserving_prodAssoc μ Qν Qν).prod (MeasurePreserving.id L)
    have h2 := measurePreserving_prodAssoc μ (Qν.prod Qν) L
    have h3 := (MeasurePreserving.id μ).prod
      ((Measure.measurePreserving_swap (μ := Qν) (ν := Qν)).prod (MeasurePreserving.id L))
    exact h3.comp (h2.comp h1)
  have hRfin : ∀ᵐ w ∂R, ∀ a b : ℝ, w.2 (Icc a b) < ⊤ :=
    (measurePreserving_snd (μ := (μ.prod Qν).prod Qν) (ν := L)).quasiMeasurePreserving.ae hfin
  have he : (williamsMassFunctional γ ∘ H) =ᵐ[R]
      (williamsInputMassCode γ ∘ T) := by
    filter_upwards [hRfin] with w hw
    change williamsMassFunctional γ
      (((w.1.1.1,negativeConditionedLastExitSegment w.1.1.1 w.1.1.2),w.1.2),w.2) = _
    rw [williamsMassFunctional_lastExit γ _ _ _ _ hw]
    exact congrArg (fun t => ENNReal.ofReal (Real.exp (γ*w.1.1.1))*t)
      (williamsCutMassCode_eq γ _ _ _ hw).symm
  rw [Measure.map_congr he,← Measure.map_map (measurable_williamsInputMassCode γ)
    hT.measurable,hT.map_eq]


end DOZZ.Proofs
