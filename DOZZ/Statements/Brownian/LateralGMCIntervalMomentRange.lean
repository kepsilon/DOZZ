/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.LateralMoments.IntervalRange

/-! The statement `DOZZ.lateralGMC_interval_moment_range`,
proved by `DOZZ.Proofs.lateralGMC_interval_moment_range`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Every translate of a fixed bounded interval has the full positive and negative moment range,
locally uniformly in compact charge and moment ranges with strict subcritical slack. See
[KRV, (zmoment)]. -/
theorem lateralGMC_interval_moment_range
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kγ Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKq : IsCompact Kq)
    (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (a b : ℝ) (hab : a < b)
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
        (∫⁻ ω, ENNReal.rpow ((Z γ ω) (Set.Ioc (a + t) (b + t))) q ∂P) ≤ C := by exact DOZZ.Proofs.lateralGMC_interval_moment_range P Kγ Kq hKγ hKq Z hZ a b hab hq

end DOZZ
