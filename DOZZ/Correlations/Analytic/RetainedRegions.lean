/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedVertexKernel
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Topology.MetricSpace.Bounded

/-! Bounded retained regions exhausting the plane away from the fixed insertion points. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The retained region uses inward holes and an outward boundary at the same scale. -/
def retainedRegion {N : ℕ} (z : Fin N → ℂ) (r : ℝ) : Set ℂ :=
  {x | ‖x‖ < Real.exp r ∧ ∀ i, Real.exp (-r) < ‖x - z i‖}

theorem retainedRegion_isOpen {N : ℕ} (z : Fin N → ℂ) (r : ℝ) :
    IsOpen (retainedRegion z r) := by
  have he : retainedRegion z r =
      {x | ‖x‖ < Real.exp r} ∩ ⋂ i, {x | Real.exp (-r) < ‖x - z i‖} := by
    ext x
    simp only [retainedRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [he]
  exact (isOpen_lt continuous_norm continuous_const).inter
    (isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
      ((continuous_id.sub continuous_const).norm)))

theorem retainedRegion_isBounded {N : ℕ} (z : Fin N → ℂ) (r : ℝ) :
    Bornology.IsBounded (retainedRegion z r) := by
  have hb : Bornology.IsBounded (Metric.ball (0 : ℂ) (Real.exp r)) := Metric.isBounded_ball
  apply hb.subset
  intro x hx
  exact Metric.mem_ball.mpr (by simpa only [dist_zero_right] using hx.1)

theorem retainedRegion_mono {N : ℕ} (z : Fin N → ℂ) :
    Monotone (retainedRegion z) := by
  intro r s hrs x hx
  exact ⟨hx.1.trans_le (Real.exp_le_exp.mpr hrs), fun i =>
    lt_of_le_of_lt (Real.exp_le_exp.mpr (neg_le_neg hrs)) (hx.2 i)⟩

/-- Every point other than an insertion eventually belongs to every retained region. -/
theorem eventually_mem_retainedRegion {N : ℕ} (z : Fin N → ℂ) (x : ℂ)
    (hx : ∀ i, x ≠ z i) : ∀ᶠ n : ℕ in atTop, x ∈ retainedRegion z n := by
  have hout : ∀ᶠ n : ℕ in atTop, ‖x‖ < Real.exp (n : ℝ) :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop ‖x‖
  have hin : ∀ᶠ n : ℕ in atTop, ∀ i, Real.exp (-(n : ℝ)) < ‖x - z i‖ := by
    rw [eventually_all]
    intro i
    have hpos : 0 < ‖x - z i‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hx i))
    exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
      (gt_mem_nhds hpos)
  filter_upwards [hout, hin] with n ho hi
  exact ⟨ho, hi⟩

/-- Restricting any measurable weight to the retained regions converges to its full mass when
the original measure has no insertion atoms. The weight may be singular at those atoms. -/
theorem retained_weighted_mass_tendsto {N : ℕ} (μ : Measure ℂ)
    (z : Fin N → ℂ) (hatom : ∀ i, μ {z i} = 0)
    (w : ℂ → ℝ≥0∞) :
    Tendsto (fun n : ℕ => ∫⁻ x in retainedRegion z n, w x ∂μ) atTop
      (𝓝 (∫⁻ x, w x ∂μ)) := by
  let ν := μ.withDensity w
  have hne : ∀ᵐ x ∂ν, ∀ i, x ≠ z i := by
    rw [ae_all_iff]
    intro i
    exact measure_eq_zero_iff_ae_notMem.mp
      ((withDensity_absolutelyContinuous μ w) (hatom i))
  have hunion : ν (⋃ n : ℕ, retainedRegion z n) = ν Set.univ := by
    apply measure_congr
    filter_upwards [hne] with x hx
    have hmem := (eventually_mem_retainedRegion z x hx).exists
    exact propext ⟨fun _ => Set.mem_univ x, fun _ => Set.mem_iUnion.mpr hmem⟩
  have ht := tendsto_measure_iUnion_atTop (μ := ν)
    ((retainedRegion_mono z).comp (fun n m hnm => Nat.cast_le.mpr hnm))
  simp only [Function.comp_def] at ht
  rw [hunion] at ht
  have he (n : ℕ) : ν (retainedRegion z n) =
      ∫⁻ x in retainedRegion z n, w x ∂μ :=
    withDensity_apply w (retainedRegion_isOpen z n).measurableSet
  have he0 : ν Set.univ = ∫⁻ x, w x ∂μ := by
    rw [withDensity_apply w MeasurableSet.univ, Measure.restrict_univ]
  simpa only [he, he0] using ht

end DOZZ.Proofs
