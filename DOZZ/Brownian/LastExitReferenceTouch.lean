/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitReferenceKernel
public import DOZZ.Brownian.Williams.MaximumGeometry

/-!
# No tangencies for the deterministic-time Brownian reference future

The atomless drifted-Brownian maximum law removes the only discrepancy between strict rational
survival and avoidance at every real future time. This is the boundary input needed to turn the
late-time rational survival limit into a last-exit bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A positive rational future stays strictly positive and approaches zero somewhere. For a
continuous positive path this records a real-time touch of the boundary. -/
def brownianPositiveRationalTouchZero : Set (ℚ → ℝ) :=
  {y | (∀ r : ℚ, 0 < (r : ℝ) → 0 < y r) ∧
    ∀ n : ℕ, ∃ r : ℚ, 0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)}

theorem measurableSet_brownianPositiveRationalTouchZero :
    MeasurableSet brownianPositiveRationalTouchZero := by
  change MeasurableSet
    ({y : ℚ → ℝ | (∀ r : ℚ, 0 < (r : ℝ) → 0 < y r) ∧
      ∀ n : ℕ, ∃ r : ℚ, 0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} : Set (ℚ → ℝ))
  have hposEq : {y : ℚ → ℝ | ∀ r : ℚ, 0 < (r : ℝ) → 0 < y r} =
      ⋂ r : ℚ, if hr : 0 < (r : ℝ) then {y : ℚ → ℝ | 0 < y r} else Set.univ := by
    ext y
    simp
  have hpos : MeasurableSet
      {y : ℚ → ℝ | ∀ r : ℚ, 0 < (r : ℝ) → 0 < y r} := by
    rw [hposEq]
    exact MeasurableSet.iInter fun r => by
      by_cases hr : 0 < (r : ℝ)
      · simp only [hr, dite_true]
        exact measurableSet_lt measurable_const (measurable_pi_apply r)
      · simp [hr]
  have hnearEq (n : ℕ) : {y : ℚ → ℝ | ∃ r : ℚ,
      0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} =
      ⋃ r : ℚ, if hr : 0 < (r : ℝ) then
        {y : ℚ → ℝ | y r < 1 / ((n : ℝ) + 1)} else ∅ := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨r, hr, hy⟩
      exact ⟨r, by simpa only [hr, dite_true, mem_ofPred_eq] using
        (show y r < 1 / ((n : ℝ) + 1) from hy)⟩
    · rintro ⟨r, hr⟩
      by_cases hq : 0 < (r : ℝ)
      · simp only [hq, dite_true, mem_ofPred_eq] at hr
        exact ⟨r, hq, by simpa only [one_div] using hr⟩
      · simp [hq] at hr
  have hnear : MeasurableSet
      {y : ℚ → ℝ | ∀ n : ℕ, ∃ r : ℚ,
        0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} := by
    rw [show {y : ℚ → ℝ | ∀ n : ℕ, ∃ r : ℚ,
        0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} =
        ⋂ n : ℕ, {y : ℚ → ℝ | ∃ r : ℚ,
          0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)} by
          ext y
          simp]
    exact MeasurableSet.iInter fun n => by
      rw [hnearEq n]
      exact MeasurableSet.iUnion fun r => by
        by_cases hr : 0 < (r : ℝ)
        · simp only [hr, dite_true]
          exact measurableSet_lt (measurable_pi_apply r) measurable_const
        · simp [hr]
  change MeasurableSet
    ({y : ℚ → ℝ | ∀ r : ℚ, 0 < (r : ℝ) → 0 < y r} ∩
      {y : ℚ → ℝ | ∀ n : ℕ, ∃ r : ℚ,
        0 < (r : ℝ) ∧ y r < 1 / ((n : ℝ) + 1)})
  exact hpos.inter hnear

private theorem rational_strict_upper_bound_path
    (q : BrownianPath) {a : ℝ}
    (hq : ∀ r : ℚ, ∀ hr : 0 < (r : ℝ), q ⟨(r : ℝ), hr.le⟩ < a)
    (t : ℝ≥0) : q t ≤ a := by
  by_contra hnot
  have hgt : a < q t := lt_of_not_ge hnot
  let F : ℝ → ℝ := fun s => q ⟨max s 0, le_max_right s 0⟩
  have hF : Continuous F := by
    apply q.continuous.comp
    exact (continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk
      (fun s => le_max_right s 0)
  have hF_eval (s : ℝ) (hs : 0 ≤ s) : F s = q ⟨s, hs⟩ := by
    change q ⟨max s 0, le_max_right s 0⟩ = q ⟨s, hs⟩
    congr 1
    exact Subtype.ext (max_eq_left hs)
  have hopen : IsOpen (F ⁻¹' Set.Ioi a) := isOpen_Ioi.preimage hF
  have htmem : (t : ℝ) ∈ F ⁻¹' Set.Ioi a := by
    rw [Set.mem_preimage, hF_eval (t : ℝ) t.property]
    exact hgt
  by_cases htpos : 0 < (t : ℝ)
  · let U : Set ℝ := Set.Ioi 0 ∩ F ⁻¹' Set.Ioi a
    have hU : IsOpen U := isOpen_Ioi.inter hopen
    obtain ⟨r, hrU⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨t, htpos, htmem⟩
    have hr : 0 < (r : ℝ) ∧ a < F (r : ℝ) := hrU
    have hrat := hq r hr.1
    have hEval := hF_eval (r : ℝ) hr.1.le
    linarith [hr.2, hrat, hEval]
  · have ht0 : t = 0 := by
      apply Subtype.ext
      exact le_antisymm (le_of_not_gt htpos) t.property
    subst t
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds htmem)
    obtain ⟨r, hr0, hrδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ by positivity)
    have hdist : dist (r : ℝ) 0 < δ := by
      change ‖(r : ℝ) - 0‖ < δ
      rw [sub_zero, Real.norm_eq_abs, abs_of_pos hr0]
      exact hrδ
    have hrpos : 0 < (r : ℝ) := hr0
    have hFr : a < F (r : ℝ) := hball (Metric.mem_ball.mpr hdist)
    have hrat := hq r hrpos
    have hEval := hF_eval (r : ℝ) hrpos.le
    linarith [hFr, hrat, hEval]

/-- The Brownian reference future started at any positive state has zero mass on rational
survival accompanied by a real-time boundary touch. -/
theorem brownianUpperConditionedReferenceFutureKernel_measure_touchZero
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν a : ℝ) (hν : 0 < ν) (ha : 0 < a) :
    brownianUpperConditionedReferenceFutureKernel B ν hν a
      brownianPositiveRationalTouchZero = 0 := by
  classical
  let D : BrownianPath → BrownianPath := driftedBrownianPath (-ν)
  let eval : BrownianPath → (ℚ → ℝ) :=
    brownianUpperConditionedPositiveRationalEvals a
  let A : Set BrownianPath := eval ⁻¹' brownianPositiveRationalTouchZero
  have hD : Measurable D := continuous_driftedBrownianPath.measurable.comp
    ((measurable_const (a := -ν)).prodMk measurable_id)
  have hEval : Measurable eval :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hA : MeasurableSet A :=
    measurableSet_brownianPositiveRationalTouchZero.preimage hEval
  have hmax : AEMeasurable (driftedBrownianMaximum ν) B :=
    aemeasurable_driftedBrownianMaximum B hB ν hν
  have hmap : B.map (driftedBrownianMaximum ν) = brownianMaximumReferenceLaw ν :=
    brownianPath_globalMaximum_map B hB ν hν
  let _ := noAtoms_brownianMaximumReferenceLaw ν
  have hmaxzero : B {p | driftedBrownianMaximum ν p = a} = 0 := by
    have hsingle := congrArg (fun m : Measure ℝ => m {a}) hmap
    rw [Measure.map_apply_of_aemeasurable hmax (measurableSet_singleton a)] at hsingle
    simpa only [Set.preimage, mem_singleton_iff, eq_comm, measure_singleton] using hsingle
  have hsubset : D ⁻¹' A ⊆ {p | driftedBrownianMaximum ν p = a} := by
    intro p hp
    have htouch : eval (D p) ∈ brownianPositiveRationalTouchZero := hp
    have hrat : ∀ r : ℚ, ∀ hr : 0 < (r : ℝ),
        D p ⟨(r : ℝ), hr.le⟩ < a := by
      intro r hr
      have h := htouch.1 r hr
      have htime : (⟨max (r : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) =
          ⟨(r : ℝ), hr.le⟩ := by
        apply Subtype.ext
        exact max_eq_left hr.le
      change 0 < a - D p ⟨max (r : ℝ) 0, le_max_right _ _⟩ at h
      rw [htime] at h
      linarith
    have hweak := rational_strict_upper_bound_path (D p) hrat
    have hbound : BddAbove (Set.range (fun t : ℝ≥0 => D p t)) :=
      ⟨a, fun z hz => by rcases hz with ⟨t, rfl⟩; exact hweak t⟩
    have hsup : driftedBrownianMaximum ν p =
        sSup (Set.range (fun t : ℝ≥0 => D p t)) := by
      unfold driftedBrownianMaximum
      congr 1
      ext z
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, by simp [D, driftedBrownianPath, neg_mul, sub_eq_add_neg]⟩
      · rintro ⟨t, ht⟩
        exact ⟨t, by simpa [D, driftedBrownianPath, neg_mul, sub_eq_add_neg] using ht⟩
    have hle : driftedBrownianMaximum ν p ≤ a := by
      rw [hsup]
      exact csSup_le (Set.range_nonempty _) (by
        rintro z ⟨t, rfl⟩
        exact hweak t)
    have hge : a ≤ driftedBrownianMaximum ν p := by
      by_contra hnot
      have hMa : sSup (Set.range (fun t : ℝ≥0 => D p t)) < a := by
        rw [← hsup]
        exact lt_of_not_ge hnot
      let gap : ℝ := a - sSup (Set.range (fun t : ℝ≥0 => D p t))
      have hgap : 0 < gap := by dsimp [gap]; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / gap)
      have hn1 : 0 < (n : ℝ) + 1 := by positivity
      have hinv : 1 / ((n : ℝ) + 1) < gap := by
        apply (div_lt_iff₀ hn1).2
        have hncast : (1 / gap : ℝ) < (n : ℝ) + 1 := by
          exact lt_trans hn (by norm_num)
        calc
          1 = (1 / gap) * gap := by field_simp [ne_of_gt hgap]
          _ < ((n : ℝ) + 1) * gap := mul_lt_mul_of_pos_right hncast hgap
          _ = gap * ((n : ℝ) + 1) := by ring
      obtain ⟨r, hr, hnear⟩ := htouch.2 n
      have hEval : eval (D p) r = a - D p ⟨(r : ℝ), hr.le⟩ := by
        simp [eval, brownianUpperConditionedPositiveRationalEvals,
          brownianUpperConditionedPositivePath, max_eq_left hr.le]
      have hDnear : a - 1 / ((n : ℝ) + 1) < D p ⟨(r : ℝ), hr.le⟩ := by
        rw [hEval] at hnear
        linarith
      have hDs : D p ⟨(r : ℝ), hr.le⟩ ≤
          sSup (Set.range (fun t : ℝ≥0 => D p t)) :=
        le_csSup hbound (Set.mem_range_self (⟨(r : ℝ), hr.le⟩ : ℝ≥0))
      dsimp [gap] at hinv
      linarith
    exact le_antisymm hle hge
  have hraw : B (D ⁻¹' A) = 0 := measure_mono_null hsubset hmaxzero
  have hlaw : brownianBelowConditionedLaw B ν a A = 0 := by
    rw [brownianBelowConditionedLaw, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply hD hA, Measure.restrict_apply (hD hA)]
    have hsmall : B (D ⁻¹' A ∩ {p | ∀ t : ℝ≥0, D p t < a}) = 0 :=
      measure_mono_null Set.inter_subset_left hraw
    rw [hsmall]
    simp
  have hkernel : brownianUpperConditionedReferenceFutureKernel B ν hν a
      brownianPositiveRationalTouchZero = 0 := by
    have hC : MeasurableSet brownianPositiveRationalTouchZero :=
      measurableSet_brownianPositiveRationalTouchZero
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned
      B ν a hν ha]
    rw [Measure.map_apply hEval hC]
    exact hlaw
  exact hkernel

end DOZZ.Proofs

end
