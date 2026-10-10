/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CoulombMass
import DOZZ.GMC.SharpMoments.SeibergUniform

/-! The statement `DOZZ.equatorGFF_extendedSeiberg_moment_uniform`,
proved by `DOZZ.Proofs.equatorGFF_extendedSeiberg_moment_uniform`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Uniform higher moments on compact admissible `U_N` parameter sets, yielding uniform
integrability of the extended Seiberg moments. -/
theorem equatorGFF_extendedSeiberg_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ}
    (S : Set ((Fin N → ℂ) × (Fin N → ℝ) × ℝ)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S,
      Function.Injective c.1 ∧ (∀ k, c.2.1 k < Q γ) ∧ c.2.2 < Q γ ∧
      (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ < 4 / γ ^ 2 ∧
      (∀ k, (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ <
        2 / γ * (Q γ - c.2.1 k)) ∧
      (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ < 2 / γ * (Q γ - c.2.2)) :
    ∃ η : ℝ, 0 < η ∧ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ S,
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) c.2.1 c.1 c.2.2)
        ((1 + η) * ((2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ)) ∂P ≤ B := by exact DOZZ.Proofs.equatorGFF_extendedSeiberg_moment_uniform P X hX γ hγ hγ2 M hM S hS hadm

end DOZZ
