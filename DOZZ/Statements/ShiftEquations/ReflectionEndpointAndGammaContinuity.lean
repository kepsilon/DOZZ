/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Assembly.EndpointContinuity

/-! The statement `DOZZ.reflection_endpoint_and_gamma_continuity`,
proved by `DOZZ.Proofs.reflection_endpoint_and_gamma_continuity`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The unit-volume reflection moment tends to 1 and R to -1 as α tends to Q from below. The last
two conjuncts record local gamma-continuity on strict admissible compact parameter sets of the
reflection moments, of R off its Gamma poles (`ReflectionPoleFree`), and of the unit-volume
structure constants, the additional input for rational gamma². -/
theorem reflection_endpoint_and_gamma_continuity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (hX : IsEquatorGFF P X)
    (μ : ℝ) (hμ : 0 < μ)
    (hM : ∀ γ, 0 < γ → γ < 2 → IsGMCOf P X γ (M γ)) :
    ∃ B : ℝ → ℝ → Ω →
        BrownianPath × BrownianPath,
      ∃ Z : ℝ → Ω → Measure ℝ,
        (∀ γ, 0 < γ → γ < 2 →
          IsSourceLateralProjection P X γ (M γ) (Z γ) ∧
            ∀ α, γ / 2 < α → α < Q γ →
              IsReflectionData P γ α (B γ α) (Z γ)) ∧
          (∀ γ, 0 < γ → γ < 2 →
            Tendsto (fun α : ℝ =>
              reflectionBarR P γ α (B γ α) (Z γ))
              (𝓝[<] (Q γ)) (𝓝 1) ∧
            Tendsto (fun α : ℝ =>
              reflectionR P γ μ α (B γ α) (Z γ))
              (𝓝[<] (Q γ)) (𝓝 (-1))) ∧
          (∀ K : Set (ℝ × ℝ), IsCompact K →
            (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) →
              ContinuousOn (fun q => reflectionBarR P q.1 q.2 (B q.1 q.2) (Z q.1)) K ∧
                ((∀ q ∈ K, ReflectionPoleFree q.1 q.2) →
                  ContinuousOn (fun q => reflectionR P q.1 μ q.2 (B q.1 q.2) (Z q.1)) K)) ∧
          ∀ K : Set (ℝ × (Fin 3 → ℝ)), IsCompact K →
            (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧
              ExtendedSeiberg3 q.1 (q.2 0) (q.2 1) (q.2 2)) →
              ContinuousOn (fun q => unitVolumeStructureConstant P (M q.1) q.1
                (q.2 0) (q.2 1) (q.2 2)) K := by exact DOZZ.Proofs.reflection_endpoint_and_gamma_continuity P X M hX μ hμ hM

end DOZZ
