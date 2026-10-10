/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.TwoSided.TwoSidedReflectionMassMomentRange

/-! The statement `DOZZ.twoSidedReflectionMass_moment_range`,
proved by `DOZZ.Proofs.twoSidedReflectionMass_moment_range`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The two-sided conditioned integral has every real moment below `4/γ²`, locally uniformly on
compact positive-drift and strict subcritical parameter ranges. See [KRV, Lemma 3.3] and its
proof in [KRV, §12.3]. -/
theorem twoSidedReflectionMass_moment_range
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kγ Kν Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKν : IsCompact Kν)
    (hKq : IsCompact Kq)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (hν : ∀ ν ∈ Kν, 0 < ν)
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) q ∂P) ≤ C := by exact DOZZ.Proofs.twoSidedReflectionMass_moment_range P Kγ Kν Kq hKγ hKν hKq B Z hData hν hq

end DOZZ
