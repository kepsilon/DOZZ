/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion

/-! The definition `DOZZ.IsCompatibleAdmissibleRegularizations`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Two admissible regularizations of one field are compatible when they are jointly Gaussian,
their mixed covariance obeys the logarithmic bound, the second has the same-center coarse estimate
against the first one's coarse barrier family, and both the separated off-diagonal and the
fixed-coarse covariances of the second approach those of the first. -/
def IsCompatibleAdmissibleRegularizations {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ) : Prop :=
  (∀ (n : ℕ) (q : Fin n → Bool × ℝ × ℂ),
      (∀ i, 0 < (q i).2.1 ∧ (q i).2.1 ≤ min ε₀ ε₁) →
      IsCenteredJointlyGaussian P (fun ω i =>
        if (q i).1 then Y ω (q i).2.1 (q i).2.2 else Z ω (q i).2.1 (q i).2.2)) ∧
  (∀ K, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε δ, 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ ε₁ →
      ∀ x ∈ K, ∀ y ∈ K,
        |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Z ω δ y) -
          Real.log (1 / max ‖x - y‖ (max ε δ))| ≤ C) ∧
  (∀ K, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ ε₀ →
      ∀ ε, 0 < ε → ε ≤ min ε₁ (Real.exp (-(k : ℝ))) → ∀ x ∈ K,
        |gaussianCovariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x)
            (fun ω => Z ω ε x) - (k : ℝ)| ≤ C) ∧
  (∀ K, IsCompact K → K ⊆ U → ∀ s : ℝ, 0 < s → ∀ η : ℝ, 0 < η →
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε δ' : ℝ, 0 < ε → ε ≤ min δ (min ε₀ ε₁) →
      0 < δ' → δ' ≤ min δ (min ε₀ ε₁) → ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
        |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Z ω δ' y) -
            gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ' y)| < η ∧
        |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Z ω δ' y) -
            gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ' y)| < η) ∧
  (∀ K, IsCompact K → K ⊆ U → ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ min ε₀ ε₁ →
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ min δ (min ε₀ ε₁) →
      ∀ x ∈ K, ∀ y ∈ K,
        |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Y ω (Real.exp (-(k : ℝ))) y) -
          gaussianCovariance P (fun ω => Y ω ε x)
            (fun ω => Y ω (Real.exp (-(k : ℝ))) y)| < η)

end DOZZ
