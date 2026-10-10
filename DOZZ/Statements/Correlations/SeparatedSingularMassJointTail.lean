/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
import DOZZ.Correlations.SeparatedTail.JointTail

/-! The statement `DOZZ.separatedSingularMass_joint_tail`,
proved by `DOZZ.Proofs.separatedSingularMass_joint_tail`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The separated-mass near-independence inequality, with the compact geometry, charge slack, and
multiplier bounds needed for one uniform constant. -/
theorem separatedSingularMass_joint_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (K2 K3 : Set ℂ) (hK2 : IsCompact K2) (hK3 : IsCompact K3)
    (hpos2 : ∀ z ∈ K2, 2 ≤ ‖z‖) (hpos3 : ∀ z ∈ K3, 2 ≤ ‖z‖)
    (hsep : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
    (A2 A3 : Set ℝ) (hA2 : IsCompact A2) (hA3 : IsCompact A3)
    (hα2 : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
    (hα3 : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
    (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hF2 : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
    (hF3 : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound)
    (ε : ℝ) (hε : 0 < ε)
    (hε2 : ∀ α ∈ A2, ε < reflectionExponent γ α)
    (hε3 : ∀ α ∈ A3, ε < reflectionExponent γ α) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
        ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ u v : ℝ, 1 ≤ u → 1 ≤ v →
          (P {ω | ENNReal.ofReal u < localSingularMass M F2 z2 γ α2 ω ∧
            ENNReal.ofReal v < localSingularMass M F3 z3 γ α3 ω}).toReal ≤
            C * Real.rpow u (-reflectionExponent γ α2 + ε) *
              Real.rpow v (-reflectionExponent γ α3 + ε) := by exact DOZZ.Proofs.separatedSingularMass_joint_tail P X M γ hγ hγ2 hX hM K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3 F2s F3s radius supBound derivBound lowerBound hF2 hF3 ε hε hε2 hε3

end DOZZ
