/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMoment

/-! The definition `DOZZ.IsCenteredGaussianField`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- A jointly measurable centered Gaussian field; its finite coordinate families use the
a.e.-measurable Gaussian predicate. -/
def IsCenteredGaussianField {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (P : Measure Ω) (Φ : Ω → S → ℝ) : Prop :=
  Measurable (fun q : Ω × S => Φ q.1 q.2) ∧
    ∀ (n : ℕ) (x : Fin n → S), IsCenteredJointlyGaussian P (fun ω i => Φ ω (x i))

end DOZZ
