/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Continuity.FourPoint

/-! The statement `DOZZ.fourPointMoment_jointly_continuous_parameters`,
proved by `DOZZ.Proofs.fourPointMoment_jointly_continuous_parameters`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Joint continuity of the `(z, 0, 1, ∞)` four-point moment in `γ` and the charges on compact
subsets of the strict extended domain. -/
theorem fourPointMoment_jointly_continuous_parameters
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : ℝ → Ω → Measure ℂ) (z : ℂ) (hz : z ≠ 0 ∧ z ≠ 1)
    (K : Set (ℝ × (Fin 4 → ℝ))) (hK : IsCompact K)
    (hKdom : ∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ ExtendedSeibergN q.1 q.2)
    (hX : IsEquatorGFF P X) (hM : ∀ q ∈ K, IsGMCOf P X q.1 (M q.1)) :
    ContinuousOn (fun q : ℝ × (Fin 4 → ℝ) =>
      (∫⁻ ω, ENNReal.rpow
        (coulombMass q.1 (M q.1 ω) ![q.2 0, q.2 1, q.2 2] ![z, 0, 1] (q.2 3))
        (-nPointSExp q.1 q.2) ∂P).toReal) K := by exact DOZZ.Proofs.fourPointMoment_jointly_continuous_parameters P X M z hz K hK hKdom hX hM

end DOZZ
