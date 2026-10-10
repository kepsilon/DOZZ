/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.SourceTailReduction

/-! The pole-free full residue from the two exact insertion-tail inputs
`DOZZ.oneInsertion_tail_uniform` and `DOZZ.twoInsertion_tail_sum_uniform`. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The full residue (erratum K30, see docs/ERRATA-AND-DEVIATIONS.md), conditional only on the
literal uniform one-insertion and two-insertion tail statements `DOZZ.oneInsertion_tail_uniform`
and `DOZZ.twoInsertion_tail_sum_uniform`, taken as hypotheses. Gamma poles remain excluded by the
premise `DOZZ.ReflectionPoleFree`. -/
theorem residue_structureConstant_bridge_of_insertion_tails
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ α2 α3 : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hPole : ReflectionPoleFree γ α3)
    (hone : ∀
    (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (_hKα : IsCompact Kα)
    (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound),
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧
        ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
                oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) *
                  Real.rpow x (-reflectionExponent γ α)| ≤
                C * Real.rpow x (-reflectionExponent γ α - η) )
    (htwo : ∀
    (K2 K3 : Set ℂ) (_hK2 : IsCompact K2) (_hK3 : IsCompact K3)
    (_hpos2 : ∀ z ∈ K2, 2 ≤ ‖z‖) (_hpos3 : ∀ z ∈ K3, 2 ≤ ‖z‖)
    (_hsep : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
    (A2 A3 : Set ℝ) (_hA2 : IsCompact A2) (_hA3 : IsCompact A3)
    (_hα2 : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
    (_hα3 : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
    (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hF2 : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
    (_hF3 : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound),
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
                C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ)) )
    : ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * structureConstant P M γ μ
          (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionR P γ μ α3 (B α3) Z)) := by
  obtain ⟨B, Z, hZ, hB, hunit⟩ := residue_unitVolume_bridge_of_insertion_tails
    P X M γ α2 α3 hγ hγ2 hα hX hM hone htwo
  exact ⟨B, Z, hZ, hB, residue_full_limit_of_unit_limit P M γ μ α2 α3
    hγ hμ hα.2.2.2 (B α3) Z hPole hunit⟩

end DOZZ.Proofs
