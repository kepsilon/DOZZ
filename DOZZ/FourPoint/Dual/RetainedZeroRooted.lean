/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.RetainedZeroMass
public import DOZZ.FourPoint.Fusion.RootedLowerBound
import Mathlib.Tactic

/-! # Uniform rooted lower bounds for the actual dual retained mass

The source's rooted inverse moment is bounded using a fixed retained disk.
The rooting point can be anywhere; no subcritical charge condition at it is used.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The covariance lower bound survives the actual moving spatial restriction. -/
theorem dual_rooted_retainedZero_lower (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ) (u : ℂ) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
        dualRetainedZeroMass γ α₁ α₂ α₃ r μ ≤
      dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u μ) := by
  let D : Set ℂ := {x | r ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have he : (gmcRootedMeasure γ u μ).restrict D = gmcRootedMeasure γ u (μ.restrict D) := by
    unfold gmcRootedMeasure
    exact restrict_withDensity hD _
  unfold dualRetainedZeroMass
  rw [he]
  exact fusion_rootedCoulombMass_lower γ u (μ.restrict D) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃

/-- One fixed disk controls every rooted dual retained mass simultaneously. -/
theorem dual_rooted_retainedZero_fixed_disk_lower (γ α₁ α₂ α₃ r : ℝ) (μ : Measure ℂ)
    (u : ℂ) (hr : r ≤ 1) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2) *
      ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
        (4 : ℝ) ^ (-|γ * α₃|))) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u μ) := by
  have hb := dual_retainedZero_fixed_disk_lower γ α₁ α₂ α₃ r μ hr
  have hroot := dual_rooted_retainedZero_lower γ α₁ α₂ α₃ r μ u
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le, mul_assoc]
  exact (mul_le_mul' le_rfl hb).trans hroot

end DOZZ.Proofs
