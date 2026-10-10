/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianLaw
public import DOZZ.Statements.Brownian.BrownianPathMeasurableSpaceEqISupComapEval
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Uniqueness of continuous path laws from entrance FDDs

The positive-time finite-dimensional laws determine the law on continuous paths once the value
at time zero is fixed almost surely. This isolates the uniqueness half of the conditioned entrance
law construction from its separate process-existence problem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

private def conditionedEvalRect (I : Finset ℝ≥0) (S : ℝ≥0 → Set ℝ) : Set BrownianPath :=
  {p | ∀ t ∈ I, p t ∈ S t}

private def conditionedEvalRectangles : Set (Set BrownianPath) :=
  {A | ∃ I : Finset ℝ≥0, ∃ S : ℝ≥0 → Set ℝ,
    (∀ t, MeasurableSet (S t)) ∧ A = conditionedEvalRect I S}

private theorem conditionedEvalRect_measure_eq_of_pos
    {ν : ℝ} {P Q : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (I : Finset ℝ≥0) (hI : ∀ t ∈ I, t ≠ 0)
    (S : ℝ≥0 → Set ℝ) (hS : ∀ t, MeasurableSet (S t)) :
    P (conditionedEvalRect I S) = Q (conditionedEvalRect I S) := by
  classical
  let n := I.card
  by_cases hIempty : I = ∅
  · simp [conditionedEvalRect, hIempty, hP.2.1.measure_univ, hQ.2.1.measure_univ]
  · have hn : 0 < n := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hIempty)
    let e : Fin n ≃o I := I.orderIsoOfFin rfl
    let times : Fin n → ℝ≥0 := fun i => (e i).val
    have htime : ∀ i, 0 < (times i : ℝ) := by
      intro i
      have hi := hI (e i).val (e i).property
      exact_mod_cast (pos_iff_ne_zero.mpr hi)
    have hmono : StrictMono times := e.strictMono
    have fddP := hP.2.2.2 n hn times htime hmono
    have fddQ := hQ.2.2.2 n hn times htime hmono
    have hlaw : P.map (fun p i => p (times i)) = Q.map (fun p i => p (times i)) :=
      fddP.trans fddQ.symm
    let A : Set (Fin n → ℝ) := ⋂ i, {x | x i ∈ S (times i)}
    have hA : MeasurableSet A := by
      apply MeasurableSet.iInter
      intro i
      exact MeasurableSet.preimage (hS (times i)) (measurable_pi_apply i)
    let f : BrownianPath → Fin n → ℝ := fun p i => p (times i)
    have hf : Measurable f := measurable_pi_iff.mpr fun i => ContinuousMap.measurable_eval _
    have hpre : f ⁻¹' A = conditionedEvalRect I S := by
      ext p
      simp only [Set.mem_preimage, A, conditionedEvalRect, f, Set.mem_ofPred_eq,
        Set.mem_iInter]
      constructor
      · intro h t ht
        let i : Fin n := e.symm ⟨t, ht⟩
        have hi := h i
        simpa [times, i] using hi
      · intro h i
        exact h (e i).val (e i).property
    calc
      P (conditionedEvalRect I S) = P (f ⁻¹' A) := by rw [hpre]
      _ = (P.map f) A := (Measure.map_apply hf hA).symm
      _ = (Q.map f) A := by rw [hlaw]
      _ = Q (f ⁻¹' A) := Measure.map_apply hf hA
      _ = Q (conditionedEvalRect I S) := by rw [hpre]

private theorem conditionedEvalRect_measure_eq
    {ν : ℝ} {P Q : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (I : Finset ℝ≥0) (S : ℝ≥0 → Set ℝ)
    (hS : ∀ t, MeasurableSet (S t)) :
    P (conditionedEvalRect I S) = Q (conditionedEvalRect I S) := by
  classical
  by_cases h0 : (0 : ℝ≥0) ∈ I
  · let J := I.erase 0
    let T : ℝ≥0 → Set ℝ := S
    have hJpos : ∀ t ∈ J, t ≠ 0 := by
      intro t ht
      exact (Finset.mem_erase.mp ht).1
    have hJ := conditionedEvalRect_measure_eq_of_pos hP hQ J hJpos T hS
    by_cases hval : (0 : ℝ) ∈ S 0
    · have hPae : (conditionedEvalRect I S : Set BrownianPath) =ᵐ[P]
          conditionedEvalRect J T := by
        filter_upwards [hP.2.2.1] with p hp0
        apply propext
        simp only [conditionedEvalRect, Set.mem_ofPred_eq]
        constructor
        · intro hp t ht
          exact hp t (Finset.mem_of_mem_erase ht)
        · intro hp t ht
          by_cases ht0 : t = 0
          · subst t
            rw [hp0]
            exact hval
          · exact hp t (Finset.mem_erase.mpr ⟨ht0, ht⟩)
      have hQae : (conditionedEvalRect I S : Set BrownianPath) =ᵐ[Q]
          conditionedEvalRect J T := by
        filter_upwards [hQ.2.2.1] with p hp0
        apply propext
        simp only [conditionedEvalRect, Set.mem_ofPred_eq]
        constructor
        · intro hp t ht
          exact hp t (Finset.mem_of_mem_erase ht)
        · intro hp t ht
          by_cases ht0 : t = 0
          · subst t
            rw [hp0]
            exact hval
          · exact hp t (Finset.mem_erase.mpr ⟨ht0, ht⟩)
      rw [measure_congr hPae, measure_congr hQae]
      exact hJ
    · have hPzero : P (conditionedEvalRect I S) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hP.2.2.1] with p hp0
        intro hp
        have hmem := hp 0 h0
        rw [hp0] at hmem
        exact hval hmem
      have hQzero : Q (conditionedEvalRect I S) = 0 := by
        rw [measure_eq_zero_iff_ae_notMem]
        filter_upwards [hQ.2.2.1] with p hp0
        intro hp
        have hmem := hp 0 h0
        rw [hp0] at hmem
        exact hval hmem
      rw [hPzero, hQzero]
  · exact conditionedEvalRect_measure_eq_of_pos hP hQ I (by
      intro t ht ht0
      apply h0
      simpa [ht0] using ht) S hS

private theorem conditionedEvalRectangles_isPiSystem :
    IsPiSystem conditionedEvalRectangles := by
  classical
  intro A hA B hB
  rcases hA with ⟨I, S, hS, rfl⟩
  rcases hB with ⟨J, T, hT, rfl⟩
  intro _hne
  let R : ℝ≥0 → Set ℝ := fun t =>
    (if t ∈ I then S t else Set.univ) ∩ (if t ∈ J then T t else Set.univ)
  refine ⟨I ∪ J, R, ?_, ?_⟩
  · intro t
    dsimp [R]
    split_ifs <;> simp [hS, hT]
  ext p
  simp only [Set.mem_inter_iff, conditionedEvalRect, Set.mem_ofPred_eq, R]
  constructor
  · rintro ⟨hI, hJ⟩ t ht
    rcases Finset.mem_union.mp ht with ht | ht
    · have hfirst : p t ∈ (if t ∈ I then S t else Set.univ) := by
        simpa [ht] using hI t ht
      have hsecond : p t ∈ (if t ∈ J then T t else Set.univ) := by
        by_cases htJ : t ∈ J
        · simpa [htJ] using hJ t htJ
        · simp [htJ]
      exact ⟨hfirst, hsecond⟩
    · have hfirst : p t ∈ (if t ∈ I then S t else Set.univ) := by
        by_cases htI : t ∈ I
        · simpa [htI] using hI t htI
        · simp [htI]
      have hsecond : p t ∈ (if t ∈ J then T t else Set.univ) := by
        simpa [ht] using hJ t ht
      exact ⟨hfirst, hsecond⟩
  · intro h
    constructor
    · intro t ht
      simpa [ht] using (h t (Finset.mem_union.mpr (Or.inl ht))).1
    · intro t ht
      simpa [ht] using (h t (Finset.mem_union.mpr (Or.inr ht))).2

/-- Two conditioned entrance laws with the same parameter coincide as measures on continuous
paths. The value at zero and the positive-time entrance FDDs generate the path sigma algebra. -/
theorem isNegativeConditionedBrownianLaw_eq
    (ν : ℝ) {P Q : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hQ : IsNegativeConditionedBrownianLaw ν Q) : P = Q := by
  classical
  have hgen : (inferInstance : MeasurableSpace BrownianPath) =
      MeasurableSpace.generateFrom conditionedEvalRectangles := by
    apply le_antisymm
    · rw [brownianPath_measurableSpace_eq_iSup_comap_eval]
      apply iSup_le
      intro t
      rw [MeasurableSpace.le_def]
      intro s hs
      change (∃ u, MeasurableSet u ∧ (fun p : BrownianPath => p t) ⁻¹' u = s) at hs
      rcases hs with ⟨u, hu, rfl⟩
      refine MeasurableSpace.measurableSet_generateFrom ⟨{t}, fun _ => u, (fun _ => hu), ?_⟩
      ext p
      simp [conditionedEvalRect, Finset.mem_singleton]
    · apply MeasurableSpace.generateFrom_le
      intro A hA
      rcases hA with ⟨I, S, hS, rfl⟩
      have hrect : conditionedEvalRect I S = ⋂ t : {t : ℝ≥0 // t ∈ I},
          {p : BrownianPath | p t.val ∈ S t.val} := by
        ext p
        simp [conditionedEvalRect]
      rw [hrect]
      apply MeasurableSet.iInter
      intro t
      exact MeasurableSet.preimage (hS t.val) (ContinuousMap.measurable_eval t.val)
  have : IsProbabilityMeasure P := hP.2.1
  have : IsProbabilityMeasure Q := hQ.2.1
  refine ext_of_generate_finite conditionedEvalRectangles hgen
    conditionedEvalRectangles_isPiSystem ?_ ?_
  · intro A hA
    rcases hA with ⟨I, S, hS, rfl⟩
    exact conditionedEvalRect_measure_eq hP hQ I S hS
  · rw [hP.2.1.measure_univ, hQ.2.1.measure_univ]

/-- Once a conditioned entrance law has been constructed, the FDD characterization
`DOZZ.IsNegativeConditionedBrownianLaw` fixes it uniquely. This packages the completed
uniqueness argument for the existence proof. -/
theorem existsUnique_negativeConditionedBrownianLaw_of_exists
    (ν : ℝ)
    (hex : ∃ P : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν P) :
    ∃! P : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν P := by
  obtain ⟨P, hP⟩ := hex
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  exact (isNegativeConditionedBrownianLaw_eq ν hP hQ).symm

end DOZZ.Proofs

end
