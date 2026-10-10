/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelQuantileMeasurable
public import DOZZ.Brownian.ConditionedEntranceGridComparison
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-!
# Measurable uniform-driven entrance chains

Use one uniform coordinate for the entrance value and fresh later coordinates for each transition.
This matches the finite-grid comparison and gives a measurable sampled chain at every finite time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Topology
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace

namespace DOZZ.Proofs

/-- The positive-state chain started from the entrance quantile at `t₀`. Coordinate zero samples
the entrance law; coordinate `n+1` samples the transition from step `n` to step `n+1`. -/
noncomputable def conditionedPositiveEntranceQuantileWalkOn
    (ν t₀ : ℝ) (dt : ℕ → ℝ) (u : ℕ → Set.Ioo (0 : ℝ) 1)
    (hν : 0 ≤ ν) (ht₀ : 0 < t₀) (hdt : ∀ n, 0 < dt n) : ℕ → Set.Ioi (0 : ℝ)
  | 0 => ⟨cdfGeneralizedQuantile
      (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t₀)) (u 0).1,
      conditionedPositiveEntranceQuantile_pos hν ht₀ (u 0).2.1 (u 0).2.2⟩
  | n + 1 => ⟨conditionedTransitionQuantile ν (dt n)
      (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt u hν ht₀ hdt n).1
      (u (n + 1)).1,
      conditionedPositiveTransitionQuantile_pos hν (hdt n)
        (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt u hν ht₀ hdt n).2
        (u (n + 1)).2.1 (u (n + 1)).2.2⟩

private theorem measurable_conditionedPositiveEntranceQuantile
    {ν t₀ : ℝ} (hν : 0 ≤ ν) (ht₀ : 0 < t₀) :
    Measurable (fun u : Set.Ioo (0 : ℝ) 1 =>
      cdfGeneralizedQuantile
        (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t₀)) u.1) := by
  let : IsProbabilityMeasure (conditionedPositiveEntranceMeasure ν t₀) :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t₀ hν ht₀
  apply Monotone.measurable
  intro u v huv
  exact cdfGeneralizedQuantile_monoOn_Ioo
    (conditionedPositiveEntranceMeasure ν t₀) u.2 v.2 huv

/-- Every fixed-time coordinate of the entrance quantile walk is measurable in the whole sequence
of independent uniform inputs. -/
theorem measurable_conditionedPositiveEntranceQuantileWalkOn
    (ν t₀ : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀)
    (hdt : ∀ n, 0 < dt n) (n : ℕ) :
    Measurable (fun u : ℕ → Set.Ioo (0 : ℝ) 1 =>
      conditionedPositiveEntranceQuantileWalkOn ν t₀ dt u hν ht₀ hdt n) := by
  induction n with
  | zero =>
      have hbase := measurable_conditionedPositiveEntranceQuantile hν ht₀
      have hreal : Measurable (fun u : ℕ → Set.Ioo (0 : ℝ) 1 =>
          cdfGeneralizedQuantile
            (ProbabilityTheory.cdf (conditionedPositiveEntranceMeasure ν t₀))
            (u 0).1) := hbase.comp (measurable_pi_apply 0)
      exact hreal.subtype_mk (h := fun u =>
        conditionedPositiveEntranceQuantile_pos hν ht₀ (u 0).2.1 (u 0).2.2
      )
  | succ n ih =>
      have hstep := measurable_conditionedTransitionQuantileOn ν (dt n) hν (hdt n)
      have hreal := hstep.comp (ih.prodMk (measurable_pi_apply (n + 1)))
      exact hreal.subtype_mk (h := fun u =>
        conditionedPositiveTransitionQuantile_pos hν (hdt n)
          (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt u hν ht₀ hdt n).2
        (u (n + 1)).2.1 (u (n + 1)).2.2
      )




/-- The time-zero coordinate of the measurable entrance chain has the explicit entrance law under
a single uniform input. -/
theorem conditionedPositiveEntranceQuantileWalkOn_initial_law
    (ν t₀ : ℝ) (dt : ℕ → ℝ) (hν : 0 ≤ ν) (ht₀ : 0 < t₀)
    (hdt : ∀ n, 0 < dt n) :
    (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
      (fun u => (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt (fun _ => u)
        hν ht₀ hdt 0).1) =
        conditionedPositiveEntranceMeasure ν t₀ := by
  let μ := conditionedPositiveEntranceMeasure ν t₀
  let q : ℝ → ℝ := fun u =>
    cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u
  let : IsProbabilityMeasure μ :=
    isProbabilityMeasure_conditionedPositiveEntranceMeasure ν t₀ hν ht₀
  have hqSubtype : Measurable (fun u : Set.Ioo (0 : ℝ) 1 => q u.1) := by
    dsimp [q, μ]
    exact measurable_conditionedPositiveEntranceQuantile hν ht₀
  have hqUniform : AEMeasurable q uniformOpenUnit := by
    simpa [q, μ, uniformOpenUnit] using
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
  have hsubtypeSampler :
      (volume : Measure (Set.Ioo (0 : ℝ) 1)).map (fun u => q u.1) = μ := by
    calc
      (volume : Measure (Set.Ioo (0 : ℝ) 1)).map (fun u => q u.1) =
          ((volume : Measure (Set.Ioo (0 : ℝ) 1)).map Subtype.val).map q :=
            (AEMeasurable.map_map_of_aemeasurable hqMap hval).symm
      _ = uniformOpenUnit.map q := by rw [hcoe]
      _ = μ := by
        dsimp [q, μ]
        exact conditionedPositiveEntranceQuantile_map_uniformOpenUnit hν ht₀
  calc
    (volume : Measure (Set.Ioo (0 : ℝ) 1)).map
        (fun u => (conditionedPositiveEntranceQuantileWalkOn ν t₀ dt (fun _ => u)
          hν ht₀ hdt 0).1) =
      (volume : Measure (Set.Ioo (0 : ℝ) 1)).map (fun u => q u.1) := by
        rfl
    _ = μ := hsubtypeSampler

end DOZZ.Proofs

end
