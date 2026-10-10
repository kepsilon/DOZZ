/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.ComplexifyNCharges

/-! The definition `DOZZ.UniformPositiveC1Family`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A class of measurable real weights with common open-neighborhood regularity, positivity at the
center, and uniform global/local bounds. The derivative bound is on a smaller closed ball whose
points lie inside the `ContDiffOn` domain, so `fderiv` cannot use its zero junk at a boundary. -/
def UniformPositiveC1Family (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ) : Prop :=
  0 < radius ∧ 0 ≤ supBound ∧ 0 ≤ derivBound ∧ 0 < lowerBound ∧
    ∀ z ∈ K, ∀ F ∈ Family z, Measurable F ∧
      (∀ x, 0 ≤ F x ∧ |F x| ≤ supBound) ∧ lowerBound ≤ F z ∧
        ContDiffOn ℝ 1 F (Metric.ball z (2 * radius)) ∧
        ∀ w ∈ Metric.closedBall z radius, ‖fderiv ℝ F w‖ ≤ derivBound

end DOZZ
