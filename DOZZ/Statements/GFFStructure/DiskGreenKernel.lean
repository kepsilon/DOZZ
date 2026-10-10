/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.ExteriorPinnedKernel

/-! The definition `DOZZ.diskGreenKernel`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Disk Green integrand, zero-extended off the positive-radius disk product and at its diagonal.
The diagonal choice is null for area integrals and for products of two circle measures. -/
noncomputable def diskGreenKernel (c : ℂ) (ρ : ℝ) (_hρ : 0 < ρ) (z w : ℂ) : ℝ := by
  classical
  exact if z ∈ ball c ρ ∧ w ∈ ball c ρ ∧ z ≠ w then
    Real.log ‖((ρ : ℂ) ^ 2 - (z - c) * star (w - c)) / ((ρ : ℂ) * (z - w))‖
  else 0

end DOZZ
