/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shifts.Seeds.Extraction
import DOZZ.Correlations.Tails.ReflectionWitness

/-!
# The second dual crossing seed from the dual fusion

On the whole seed domain `α, ε, α' < Q`, `α + ε + α' > 2Q + 2/γ`, one has
`R(ε) C(2Q - ε - 2/γ, α, α') = L(ε, α, α') R(α) C(ε, 2Q - α - 2/γ, α')` with `dualCrossingL`, two
reflection witnesses `B(ε)`, `B(α)` and one lateral measure from the supplied space. The only input
is the complete statement of `dual_full_fusion_and_asymptotic`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

universe u

namespace DOZZ.Proofs

/-- **The second dual crossing seed** from the statement of the dual fusion
(`dual_full_fusion_and_asymptotic`, quantified over `Ω : Type u`). The conclusion is that of
`dual_crossing_seed_two`. -/
theorem dual_crossing_seed_two_of_fusion
    (hFusion : ∀ {Ω : Type u} [MeasurableSpace Ω]
      {H : ℂ → ℂ → ℂ → ℂ → ℂ}
      (_hH : IsGaussHypergeometricFamily H)
      (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
      (γ μ α₁ α₂ α₃ η ξ : ℝ)
      (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
      (_hη : 0 < η) (_hη₂ : η < γ / 2) (_hξ : 0 < ξ) (_hξ₂ : ξ < 1)
      (_hαlo : Q γ - η < α₁) (_hαhi : α₁ < Q γ)
      (_hα₂ : α₂ < Q γ) (_hα₃ : α₃ < Q γ)
      (_hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
      (_hslack₁ : (4 / γ) * (Q γ - α₁) < ξ)
      (_hslack₂ : (4 / γ) * (Q γ - α₁) <
        (1 - ξ) * (4 - γ * α₁ - 2 * γ * η))
      (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
        ∃ Z : Ω → Measure ℝ,
          IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ α₁ (B α₁) Z ∧
          let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
          let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
          let c := gaussParameterC γ (2 / γ) α₁
          let κ := (4 / γ) * (Q γ - α₁)
          (∃ r : ℂ → ℝ,
            (∀ z, fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
              structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ +
                reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                    (‖z‖ ^ κ : ℝ) + r z) ∧
              Tendsto (fun z => r z / ‖z‖ ^ κ)
                (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0)) ∧
            (∀ z ∈ gaussCutPlane,
              fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
                structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
                    ‖gaussFMinus H a b c z‖ ^ 2 +
                  reflectionR P γ μ α₁ (B α₁) Z *
                    structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
                      ‖gaussFPlus H a b c z‖ ^ 2))
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' := by
  obtain ⟨B, Z, hSLP, hB⟩ := exists_source_reflection_witness P X M γ hγ hγ₂ hX hM
  refine ⟨B ε, B α, Z, hSLP, hB ε hε, hB α hα, ?_⟩
  exact dual_seed_two_identity P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM (B ε) (B α) Z
    (dual_reflection_identity_of_fusion P X M γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM
      (B α) Z (hB α hα) hFusion)
    (dual_reflection_identity_of_fusion P X M γ μ ε α α' hγ hγ₂ hμ hε hα hα' (by linarith)
      hX hM (B ε) Z (hB ε hε) hFusion)

end DOZZ.Proofs

end
