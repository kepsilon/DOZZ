/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath
import DOZZ.Brownian.Williams.Disintegration

/-! The statement `DOZZ.brownian_williams_maximum_disintegration`,
proved by `DOZZ.Proofs.brownian_williams_maximum_disintegration`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Williams' maximum decomposition is a path-law identity, with maximum density
`2ν exp(-2νm) dm`, a positive-drift first-hit segment, and an independent conditioned post-path.
Each first-hit pushforward is guarded by AE measurability. See [KRV, Lemma 3.1]. -/
theorem brownian_williams_maximum_disintegration
    (P : Measure BrownianPath)
    (hB : ProbabilityTheory.IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) :
    (AEMeasurable (driftedBrownianMaximum ν) P) ∧
    (AEMeasurable (brownianPreMaximumSegment ν) P) ∧
    (AEMeasurable (brownianPostMaximumPath ν) P) ∧
    (∀ m : ℝ, 0 < m → AEMeasurable (positiveDriftFirstHitSegment ν m) P) ∧
    ∀ (F : ℝ × StoppedBrownianPath → ℝ≥0∞) (G : BrownianPath → ℝ≥0∞),
      Measurable F → Measurable G →
        (AEMeasurable (fun m : ℝ =>
          ∫⁻ u, F (m, u) ∂P.map (positiveDriftFirstHitSegment ν m))
            (brownianMaximumReferenceLaw ν) ∧
        ∫⁻ p, F (driftedBrownianMaximum ν p, brownianPreMaximumSegment ν p) *
          G (brownianPostMaximumPath ν p) ∂P =
        ∫⁻ m,
          (∫⁻ u, F (m, u) ∂P.map (positiveDriftFirstHitSegment ν m)) *
            (∫⁻ q, G q ∂Qν) ∂brownianMaximumReferenceLaw ν) := by exact DOZZ.Proofs.brownian_williams_maximum_disintegration P hB ν hν Qν hQν

end DOZZ
