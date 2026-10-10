/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.StoppedPreterminalCylinders

/-!
# Uniqueness of stopped continuous path laws

The finite preterminal marked laws, the initial value, and the terminal value determine the
whole stopped-path measure. Finite evaluation cylinders generate the process sigma algebra,
and the continuous-path measurable structure is the pullback of that process structure.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- Adding the almost-sure initial value recovers cylinders at arbitrary nonnegative times. -/
theorem SameStoppedPreterminalLaws.cylinder_eq
    {μ η : Measure StoppedBrownianPath} [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : SameStoppedPreterminalLaws μ η)
    (hμpos : ∀ᵐ z ∂μ, 0 < z.1) (hηpos : ∀ᵐ z ∂η, 0 < z.1)
    (hμzero : ∀ᵐ z ∂μ, -(z.2 0) = 0) (hηzero : ∀ᵐ z ∂η, -(z.2 0) = 0)
    (c : ℝ) (hμend : ∀ᵐ z ∂μ, ∀ t, z.1 ≤ t → -(z.2 t) = c)
    (hηend : ∀ᵐ z ∂η, ∀ t, z.1 ≤ t → -(z.2 t) = c)
    (U : Set ℝ) (hU : MeasurableSet U) (I : Finset ℝ≥0)
    (S : ℝ≥0 → Set ℝ) (hS : ∀ t, MeasurableSet (S t)) :
    μ (stoppedPathCylinder U I S) = η (stoppedPathCylinder U I S) := by
  classical
  let J := I.erase 0
  have hJpos : ∀ t ∈ J, 0 < t := fun t ht =>
    pos_iff_ne_zero.mpr (Finset.mem_erase.mp ht).1
  by_cases h0 : (0 : ℝ≥0) ∈ I
  · by_cases hval : (0 : ℝ) ∈ S 0
    · have hevent (M : Measure StoppedBrownianPath) (hz : ∀ᵐ z ∂M, -(z.2 0) = 0) :
          stoppedPathCylinder U I S =ᵐ[M] stoppedPathCylinder U J S := by
        filter_upwards [hz] with z hzero
        apply propext
        simp only [stoppedPathCylinder, mem_ofPred_eq]
        constructor
        · rintro ⟨hU, hI⟩
          exact ⟨hU, fun t ht => hI t (Finset.mem_of_mem_erase ht)⟩
        · rintro ⟨hU, hJ⟩
          refine ⟨hU, ?_⟩
          intro t ht
          by_cases ht0 : t = 0
          · subst t
            rwa [hzero]
          · exact hJ t (Finset.mem_erase.mpr ⟨ht0, ht⟩)
      rw [measure_congr (hevent μ hμzero), measure_congr (hevent η hηzero)]
      exact h.positive_cylinder_eq hμpos hηpos c hμend hηend U hU J hJpos S hS
    · have hzero (M : Measure StoppedBrownianPath) (hz : ∀ᵐ z ∂M, -(z.2 0) = 0) :
          M (stoppedPathCylinder U I S) = 0 := by
        apply measure_eq_zero_iff_ae_notMem.mpr
        filter_upwards [hz] with z hz
        intro hmem
        have hv := hmem.2 0 h0
        rw [hz] at hv
        exact hval hv
      rw [hzero μ hμzero, hzero η hηzero]
  · exact h.positive_cylinder_eq hμpos hηpos c hμend hηend U hU I
      (fun t ht => pos_iff_ne_zero.mpr (by intro heq; subst t; exact h0 ht)) S hS

/-- The complete stopped continuous path measure is determined by the actual preterminal
marked laws, its positive lifetime, its initial value, and its fixed terminal value. -/
theorem SameStoppedPreterminalLaws.measure_eq
    {μ η : Measure StoppedBrownianPath} [IsFiniteMeasure μ] [IsFiniteMeasure η]
    (h : SameStoppedPreterminalLaws μ η)
    (hμpos : ∀ᵐ z ∂μ, 0 < z.1) (hηpos : ∀ᵐ z ∂η, 0 < z.1)
    (hμzero : ∀ᵐ z ∂μ, -(z.2 0) = 0) (hηzero : ∀ᵐ z ∂η, -(z.2 0) = 0)
    (c : ℝ) (hμend : ∀ᵐ z ∂μ, ∀ t, z.1 ≤ t → -(z.2 t) = c)
    (hηend : ∀ᵐ z ∂η, ∀ t, z.1 ≤ t → -(z.2 t) = c) : μ = η := by
  classical
  let f : StoppedBrownianPath → ℝ × (ℝ≥0 → ℝ) := fun z =>
    ((z.1 : ℝ), fun t => -(z.2 t))
  have hf : Measurable f := (NNReal.continuous_coe.measurable.comp measurable_fst).prodMk
    (measurable_pi_iff.mpr fun t => ((ContinuousMap.measurable_eval t).comp measurable_snd).neg)
  have hprocess : μ.map f = η.map f := by
    apply Measure.ext_prod
    intro U V hU hV
    let μU := ((μ.map f).restrict (U ×ˢ univ)).map Prod.snd
    let ηU := ((η.map f).restrict (U ×ˢ univ)).map Prod.snd
    have hslice (M : Measure StoppedBrownianPath) (W : Set (ℝ≥0 → ℝ)) (hW : MeasurableSet W) :
        (((M.map f).restrict (U ×ˢ univ)).map Prod.snd) W =
          M (f ⁻¹' (U ×ˢ W)) := by
      rw [Measure.map_apply measurable_snd hW,
        Measure.restrict_apply (hW.preimage measurable_snd)]
      have he : Prod.snd ⁻¹' W ∩ (U ×ˢ univ) = U ×ˢ W := by
        ext z
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and, and_comm]
      rw [he, Measure.map_apply hf (hU.prod hW)]
    have heq : μU = ηU := by
      apply ext_of_generate_finite
        (squareCylinders fun _ : ℝ≥0 => {A : Set ℝ | MeasurableSet A})
        generateFrom_squareCylinders.symm
        (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp))
      · rintro W ⟨I, S, hS, rfl⟩
        have hmS : ∀ t, MeasurableSet (S t) := by simpa only [mem_univ_pi, mem_ofPred_eq] using hS
        have hmW : MeasurableSet ((I : Set ℝ≥0).pi S) :=
          MeasurableSet.pi (Finset.countable_toSet _) (fun t _ => hmS t)
        rw [hslice _ _ hmW, hslice _ _ hmW]
        have hpre : f ⁻¹' (U ×ˢ (I : Set ℝ≥0).pi S) = stoppedPathCylinder U I S := by
          ext z
          simp [f, stoppedPathCylinder, mem_pi]
        rw [hpre]
        exact h.cylinder_eq hμpos hηpos hμzero hηzero c hμend hηend U hU I S hmS
      · rw [hslice _ univ MeasurableSet.univ, hslice _ univ MeasurableSet.univ]
        have hpre : f ⁻¹' (U ×ˢ univ) = {z : StoppedBrownianPath | (z.1 : ℝ) ∈ U} := by
          ext z
          simp [f]
        rw [hpre]
        exact h.lifetime_event_eq hμpos hηpos U hU
    have hh := congrArg (fun M : Measure (ℝ≥0 → ℝ) => M V) heq
    rw [Measure.map_apply hf (hU.prod hV), Measure.map_apply hf (hU.prod hV)]
    rwa [hslice _ V hV, hslice _ V hV] at hh
  apply Measure.ext_prod
  intro A B hA hB
  let U : Set ℝ := Real.toNNReal ⁻¹' A
  have hU : MeasurableSet U := hA.preimage measurable_real_toNNReal
  obtain ⟨W, hW, hBW⟩ := brownianPath_measurableSpace_eq_comap.le B hB
  let V : Set (ℝ≥0 → ℝ) := (fun g t => -(g t)) ⁻¹' W
  have hV : MeasurableSet V := hW.preimage
    (measurable_pi_iff.mpr fun t => (measurable_pi_apply t).neg)
  have hpre : f ⁻¹' (U ×ˢ V) = A ×ˢ B := by
    rw [← hBW]
    ext z
    simp only [mem_preimage, mem_prod, f, U, V, Real.toNNReal_coe, neg_neg]
  have heq := congrArg (fun M : Measure (ℝ × (ℝ≥0 → ℝ)) => M (U ×ˢ V)) hprocess
  rwa [Measure.map_apply hf (hU.prod hV), Measure.map_apply hf (hU.prod hV), hpre] at heq

end DOZZ.Proofs
end
