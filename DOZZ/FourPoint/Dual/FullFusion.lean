/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.FullInverseWitness
public import DOZZ.FourPoint.Dual.FullFusionAssembly
/-! The corrected dual full fusion formula and same-source asymptotic. -/
public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The actual stochastic full-kernel limit and the physical classification give the
literal dual fusion conclusions on one source reflection family. -/
theorem dual_full_fusion_and_asymptotic {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ η ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η) (hη₂ : η < γ / 2) (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hαlo : Q γ - η < α₁) (hαhi : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hslack₁ : (4 / γ) * (Q γ - α₁) < ξ)
    (hslack₂ : (4 / γ) * (Q γ - α₁) <
      (1 - ξ) * (4 - γ * α₁ - 2 * γ * η))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
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
                    ‖gaussFPlus H a b c z‖ ^ 2) := by
  obtain ⟨B, Z, hSource, hData, hLimit⟩ := dual_source_full_inverse_fusion_witness
    P M X γ α₁ α₂ α₃ η ξ hγ hγ₂ hη hη₂ hξ hξ₂ hαlo hαhi hα₂ hα₃ hs
      hslack₁ hslack₂ hX hM
  refine ⟨B, Z, hSource, hData, ?_⟩
  exact dual_full_fusion_of_normalized_inverse_limit hH P M X γ μ α₁ α₂ α₃ η ξ
    hγ hγ₂ hμ hη hη₂ hξ hξ₂ hαlo hαhi hα₂ hα₃ hs hslack₁ hslack₂ hX hM B Z hData hLimit

end DOZZ.Proofs
