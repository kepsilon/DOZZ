/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.UniformPositiveC1Family
import DOZZ.Correlations.Continuity.UnitVolume

/-! The statement `DOZZ.unitVolumeNPoint_jointly_continuous_parameters`,
proved by `DOZZ.Proofs.unitVolumeNPoint_jointly_continuous_parameters`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Normalized unit-volume N-point moments are jointly continuous in `γ` and the charges on compact
subsets of the strict extended domain, including across `γ² = 2`. -/
theorem unitVolumeNPoint_jointly_continuous_parameters
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 3 ≤ N)
    (P : Measure Ω) (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ)
    (z : Fin N → ℂ) (hz : ∀ i j, i ≠ j → z i ≠ z j)
    (K : Set (ℝ × (Fin N → ℝ))) (hK : IsCompact K)
    (hKdom : ∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ ExtendedSeibergN q.1 q.2)
    (hX : IsEquatorGFF P X)
    (hM : ∀ q ∈ K, IsGMCOf P X q.1 (M q.1)) :
    ContinuousOn (fun q => unitVolumeNPointCorrelation P (M q.1) q.1 q.2 z) K := by exact DOZZ.Proofs.unitVolumeNPoint_jointly_continuous_parameters hN P X M z hz K hK hKdom hX hM

end DOZZ
