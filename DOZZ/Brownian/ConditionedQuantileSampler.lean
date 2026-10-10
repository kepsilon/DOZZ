/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedQuantileMeasurable
public import DOZZ.Brownian.ConditionedKernelGridComparison
public import DOZZ.Brownian.ConditionedEntranceProbability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The generalized quantile samples its probability law

The common-uniform coupling uses generalized CDF inverses. This file verifies that the inverse
map, under a uniform level, has exactly the input probability law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Topology
open scoped Topology

namespace DOZZ.Proofs

/-- On uniform levels, the generalized inverse lies below `x` exactly when the CDF at `x`
reaches the level. -/
theorem cdfGeneralizedQuantile_le_iff
    (μ : Measure ℝ) [IsProbabilityMeasure μ] {u x : ℝ}
    (hu : 0 < u) (hu1 : u < 1) :
    cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u ≤ x ↔
      u ≤ ProbabilityTheory.cdf μ x := by
  let F := ProbabilityTheory.cdf μ
  let S : Set ℝ := {y | u ≤ F y}
  have hnonempty : S.Nonempty := by
    have hev : ∀ᶠ y : ℝ in atTop, u < F y :=
      (ProbabilityTheory.tendsto_cdf_atTop μ).eventually (Ioi_mem_nhds hu1)
    obtain ⟨y, hy⟩ := Filter.eventually_atTop.1 hev
    exact ⟨y, le_of_lt (hy y le_rfl)⟩
  have hbounded : BddBelow S := by
    have hev : ∀ᶠ y : ℝ in atBot, F y < u :=
      (ProbabilityTheory.tendsto_cdf_atBot μ).eventually (Iio_mem_nhds hu)
    obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 hev
    refine ⟨a, ?_⟩
    intro y hy
    change u ≤ F y at hy
    by_contra hnot
    exact (not_lt_of_ge hy) (ha y (le_of_lt (lt_of_not_ge hnot)))
  change sInf S ≤ x ↔ u ≤ F x
  constructor
  · intro hqx
    have hseq0 : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
      have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add hsmall
    have hseq : Tendsto (fun n : ℕ => x + 1 / ((n : ℝ) + 1)) atTop
        (𝓝[Set.Ici x] x) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨hseq0, Filter.Eventually.of_forall ?_⟩
      intro n
      simp only [Set.mem_Ici]
      exact le_add_of_nonneg_right (by positivity)
    have hFright : Tendsto F (𝓝[Set.Ici x] x) (𝓝 (F x)) :=
      F.right_continuous x |>.tendsto
    have hFseq : Tendsto (fun n : ℕ => F (x + 1 / ((n : ℝ) + 1))) atTop
        (𝓝 (F x)) := by
      convert hFright.comp hseq using 1
      rfl
    have hvalues : ∀ n : ℕ, u ≤ F (x + 1 / ((n : ℝ) + 1)) := by
      intro n
      by_contra hnot
      have hlt : F (x + 1 / ((n : ℝ) + 1)) < u := lt_of_not_ge hnot
      have hbelow : x + 1 / ((n : ℝ) + 1) ≤ sInf S := by
        apply le_csInf hnonempty
        intro y hy
        change u ≤ F y at hy
        by_contra hxy
        have hyx : y ≤ x + 1 / ((n : ℝ) + 1) := le_of_lt (lt_of_not_ge hxy)
        have hmono := ProbabilityTheory.monotone_cdf μ hyx
        exact (not_lt_of_ge hy) (lt_of_le_of_lt hmono hlt)
      have he : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hclosed : IsClosed (Set.Ici u) := isClosed_Ici
    have hlimit : F x ∈ Set.Ici u :=
      hclosed.mem_of_tendsto hFseq (Filter.Eventually.of_forall hvalues)
    exact hlimit
  · intro hux
    exact csInf_le hbounded hux

/-- A uniform random variable on `(0,1)`, using unnormalized Lebesgue restriction (whose total
mass is one). -/
noncomputable def uniformOpenUnit : Measure ℝ :=
  (volume : Measure ℝ).restrict (Set.Ioo 0 1)

instance isProbabilityMeasure_uniformOpenUnit : IsProbabilityMeasure uniformOpenUnit := by
  refine ⟨?_⟩
  simp [uniformOpenUnit, Real.volume_Ioo]

/-- Applying the generalized quantile of a probability law to a uniform level has that law. -/
theorem cdfGeneralizedQuantile_map_uniformOpenUnit
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (uniformOpenUnit).map (fun u => cdfGeneralizedQuantile
      (ProbabilityTheory.cdf μ) u) = μ := by
  let Q : ℝ → ℝ := fun u => cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u
  have hQ : AEMeasurable Q uniformOpenUnit := by
    simpa [Q, uniformOpenUnit] using aemeasurable_cdfGeneralizedQuantile_Ioo μ
  let : IsProbabilityMeasure (uniformOpenUnit.map Q) :=
    (Measure.isProbabilityMeasure_map_iff hQ).2 inferInstance
  apply Measure.ext_of_Iic
  intro x
  have hset : (Q ⁻¹' Set.Iic x) ∩ Set.Ioo 0 1 =
      Set.Ioc 0 (ProbabilityTheory.cdf μ x) ∩ Set.Iio 1 := by
    ext u
    constructor
    · intro hu
      have hq : Q u ≤ x := hu.1
      have hu01 : u ∈ Set.Ioo 0 1 := hu.2
      have hux : u ≤ ProbabilityTheory.cdf μ x :=
        (cdfGeneralizedQuantile_le_iff μ hu01.1 hu01.2).mp hq
      exact ⟨⟨hu01.1, hux⟩, hu01.2⟩
    · intro hu
      have hu01 : u ∈ Set.Ioo 0 1 := ⟨hu.1.1, hu.2⟩
      have hq : Q u ≤ x :=
        (cdfGeneralizedQuantile_le_iff μ hu01.1 hu01.2).mpr hu.1.2
      exact ⟨hq, hu01⟩
  calc
    (uniformOpenUnit.map Q) (Set.Iic x) =
        uniformOpenUnit (Q ⁻¹' Set.Iic x) :=
      Measure.map_apply_of_aemeasurable hQ measurableSet_Iic
    _ = (volume : Measure ℝ) ((Q ⁻¹' Set.Iic x) ∩ Set.Ioo 0 1) := by
      rw [uniformOpenUnit, Measure.restrict_apply' measurableSet_Ioo]
    _ = (volume : Measure ℝ)
        (Set.Ioc 0 (ProbabilityTheory.cdf μ x) ∩ Set.Iio 1) := by rw [hset]
    _ = ENNReal.ofReal (ProbabilityTheory.cdf μ x) := by
      by_cases hF : ProbabilityTheory.cdf μ x < 1
      · have hsub : Set.Ioc 0 (ProbabilityTheory.cdf μ x) ⊆ Set.Iio 1 := by
          intro y hy
          exact lt_of_le_of_lt hy.2 hF
        rw [Set.inter_eq_left.mpr hsub, Real.volume_Ioc]
        simp
      · have hFone : ProbabilityTheory.cdf μ x = 1 :=
          le_antisymm (ProbabilityTheory.cdf_le_one μ x) (le_of_not_gt hF)
        rw [hFone]
        have hset' : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio 1 =
            Set.Ioc 0 1 \ {1} := by
          ext y
          simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio,
            Set.mem_sdiff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨⟨hpos, hle⟩, hlt⟩
            exact ⟨⟨hpos, hle⟩, by intro heq; subst y; linarith⟩
          · rintro ⟨⟨hpos, hle⟩, hne⟩
            have hlt : y < 1 := by
              by_contra hnot
              exact hne (le_antisymm hle (le_of_not_gt hnot))
            exact ⟨⟨hpos, hle⟩, hlt⟩
        rw [hset', measure_sdiff_null']
        · rw [Real.volume_Ioc]
          simp
        · simp [Set.mem_Ioc]
    _ = μ (Set.Iic x) := ProbabilityTheory.ofReal_cdf μ x

/-- The entrance-density quantile sampler pushes uniform levels to the explicit entrance law. -/
theorem conditionedPositiveEntranceQuantile_map_uniformOpenUnit
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) :
    (uniformOpenUnit).map (fun u => cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t)) u) =
        conditionedPositiveEntranceMeasure ν t := by
  let : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν t) :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t hν ht
  exact cdfGeneralizedQuantile_map_uniformOpenUnit
    (conditionedPositiveEntranceMeasure ν t)

/-- The transition-kernel quantile sampler pushes uniform levels to the explicit conditioned
transition law. -/
theorem conditionedPositiveTransitionQuantile_map_uniformOpenUnit
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) :
    (uniformOpenUnit).map (conditionedTransitionQuantile ν t x) =
      conditionedPositiveTransitionMeasure ν t x := by
  let : IsProbabilityMeasure (conditionedPositiveTransitionMeasure ν t x) :=
    isProbabilityMeasure_conditionedPositiveTransitionMeasure ν t x hν ht hx
  change (uniformOpenUnit).map (fun u => cdfGeneralizedQuantile
    (ProbabilityTheory.cdf (conditionedPositiveTransitionMeasure ν t x)) u) = _
  exact cdfGeneralizedQuantile_map_uniformOpenUnit
    (conditionedPositiveTransitionMeasure ν t x)

end DOZZ.Proofs

end
