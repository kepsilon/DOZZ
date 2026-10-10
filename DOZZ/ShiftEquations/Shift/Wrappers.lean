/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.FirstShift
public import DOZZ.Correlations.Analytic.StructureConstantHolomorphic
public import DOZZ.Correlations.Residue.Assembly
public import DOZZ.Correlations.SumTail.Assembly

/-!
# The `R̄` representation and the first shift, with the holomorphic extension discharged

`unitVolumeStructureConstant_holomorphic_near_extended_domain` is proved, so the reductions for
`DOZZ.reflectionBarR_holomorphic_representation` and `DOZZ.reflectionR_first_shift_meromorphic` need
only the γ/2 crossing (`gammaHalf_crossing`), the residue bridge, and (for the first shift) the tail
estimate `twoInsertion_tail_sum_uniform`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The `R̄` representation from the γ/2 crossing and the residue bridge.** -/
theorem reflectionBarR_holomorphic_representation_of_crossing_bridge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    (I : Set ℝ) (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) :=
  reflectionBarR_holomorphic_representation_of_deps P X M γ hγ hγ2 hX hM hCross hBridge
    (unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM) I hI

/-- **The first shift of `R` from the γ/2 crossing, the residue bridge and the two-insertion tail
estimate.** -/
theorem reflectionR_first_shift_meromorphic_of_crossing_bridge_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    (hTail : ∀ (K2 K3 : Set ℂ) (_ : IsCompact K2) (_ : IsCompact K3)
      (_ : ∀ z ∈ K2, 2 ≤ ‖z‖) (_ : ∀ z ∈ K3, 2 ≤ ‖z‖)
      (_ : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
      (A2 A3 : Set ℝ) (_ : IsCompact A2) (_ : IsCompact A3)
      (_ : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
      (_ : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
      (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
      (_ : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
      (_ : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound),
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
                  C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ))) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) :=
  reflectionR_first_shift_meromorphic_of_deps P X M γ μ hγ hγ2 hμ hX hM hCross hBridge hTail
    (unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM)

/-- **The `R̄` representation from the γ/2 crossing alone** (the residue bridge is the theorem
`unitVolumeStructureConstant_threeToTwo_residue_bridge`). -/
theorem reflectionBarR_holomorphic_representation_of_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (I : Set ℝ) (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) :=
  reflectionBarR_holomorphic_representation_of_crossing_bridge P X M γ hγ hγ2 hX hM hCross
    (fun α2 α3 hα =>
      unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ α2 α3 hγ hγ2 hα hX hM) I hI

/-- **The first shift of `R` from the γ/2 crossing alone** (the residue bridge and the tail estimate
are the theorems `unitVolumeStructureConstant_threeToTwo_residue_bridge` and
`twoInsertion_tail_sum_uniform`). -/
theorem reflectionR_first_shift_meromorphic_of_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) :=
  reflectionR_first_shift_meromorphic_of_crossing_bridge_tail P X M γ μ hγ hγ2 hμ hX hM hCross
    (fun α2 α3 hα =>
      unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ α2 α3 hγ hγ2 hα hX hM)
    (fun K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3 F2s F3s radius supBound
        derivBound lowerBound hF2 hF3 =>
      twoInsertion_tail_sum_uniform P X M γ hγ hγ2 hX hM K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3
        hA2 hA3 hα2 hα3 F2s F3s radius supBound derivBound lowerBound hF2 hF3)

end DOZZ.Proofs

end
