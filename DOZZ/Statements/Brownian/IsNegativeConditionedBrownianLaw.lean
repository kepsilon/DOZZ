/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedFDDDensity

/-! The definition `DOZZ.IsNegativeConditionedBrownianLaw`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- A probability law on continuous paths is the drift-`ν` Brownian law conditioned to stay
negative, with entrance at zero, exactly when its finite-dimensional laws have the entrance and
Doob-transition densities above. This is a source characterization, not a chosen representative. -/
def IsNegativeConditionedBrownianLaw (ν : ℝ) (P : Measure BrownianPath) : Prop :=
  0 ≤ ν ∧ IsProbabilityMeasure P ∧
    (∀ᵐ p ∂P, p 0 = 0) ∧
      ∀ (n : ℕ), 0 < n →
        ∀ times : Fin n → ℝ≥0,
          (∀ i, 0 < (times i : ℝ)) → StrictMono times →
            P.map (fun p i => p (times i)) =
              (volume : Measure (Fin n → ℝ)).withDensity
                (fun x => ENNReal.ofReal
                  (max 0 (negativeConditionedFDDDensity ν
                    (List.ofFn fun i => (times i : ℝ)) (List.ofFn fun i => x i))))

end DOZZ
