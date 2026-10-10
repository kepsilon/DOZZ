/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SumTail.Reduction
import DOZZ.Statements.Correlations.OneInsertionTailUniform

/-! Proof of `DOZZ.twoInsertion_tail_sum_uniform` ([KRV, Lemma 7.3]), with every input supplied by
the one-insertion theorem `DOZZ.oneInsertion_tail_uniform` and the separated joint-tail inequality
`DOZZ.separatedSingularMass_joint_tail`. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

theorem twoInsertion_tail_sum_uniform
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
    (hF3 : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α, (α ∈ A2 ∨ α ∈ A3) → IsReflectionData P γ α (B α) Z) ∧
        ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
          ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
            ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x <
                  localSingularMass M F2 z2 γ α2 ω + localSingularMass M F3 z3 γ α3 ω}).toReal -
                (oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z) *
                    Real.rpow x (-reflectionExponent γ α2) +
                  oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z) *
                    Real.rpow x (-reflectionExponent γ α3))| ≤
                C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ)) := by
  exact sumtail_twoInsertion_tail_sum_uniform_of_oneInsertion_tail P X M γ hγ hγ2 hX hM
    K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
    F2s F3s radius supBound derivBound lowerBound hF2 hF3
    (DOZZ.oneInsertion_tail_uniform P X M γ hγ hγ2 hX hM)

end DOZZ.Proofs
