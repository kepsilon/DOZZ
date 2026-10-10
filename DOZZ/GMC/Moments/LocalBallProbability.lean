/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Normalized Lebesgue measure on a disk, used for local finite-cutoff chaos integrals. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Normalized volume on the subtype of the closed disk of radius `R`. -/
noncomputable def localBallProbability (R : ℝ) :
    Measure {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R} := by
  let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
  letI : MeasureSpace S := Measure.Subtype.measureSpace
  exact ((volume : Measure S) Set.univ)⁻¹ • (volume : Measure S)

theorem localBallProbability_isProbability {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (localBallProbability R) := by
  let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
  let : MeasureSpace S := Measure.Subtype.measureSpace
  have htotal : (volume : Measure S) Set.univ = ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞) := by
    rw [Measure.Subtype.volume_univ Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
      Complex.volume_closedBall]
  have hne : (volume : Measure S) Set.univ ≠ 0 := by
    rw [htotal]
    have hR' : ENNReal.ofReal R ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hR
    have hπ : (NNReal.pi : ℝ≥0∞) ≠ 0 := by
      rw [ENNReal.coe_ne_zero]
      exact ne_of_gt NNReal.pi_pos
    exact ne_of_gt (ENNReal.mul_pos (pow_ne_zero 2 hR') hπ)
  have htop : (volume : Measure S) Set.univ ≠ ∞ := by
    rw [htotal]
    exact ENNReal.mul_ne_top (by simp) (by simp)
  refine ⟨?_⟩
  change (((volume : Measure S) Set.univ)⁻¹ • (volume : Measure S)) Set.univ = 1
  rw [Measure.smul_apply]
  exact ENNReal.inv_mul_cancel hne htop

end DOZZ.Proofs
