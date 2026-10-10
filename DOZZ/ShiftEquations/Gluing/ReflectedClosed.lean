/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.ReflectedWrapper
public import DOZZ.ShiftEquations.FirstStrip.Closed
public import DOZZ.ShiftEquations.Shift.Wrappers

/-!
# The reflected shift and gluing from the first reflection shift alone, and from the γ/2 crossing

With `DOZZ.structureConstant_first_shift_strip` proved from the unreflected formula
(`structureConstant_first_shift_strip_unconditional`),
`DOZZ.structureConstant_reflected_shift_and_gluing` needs only
`DOZZ.reflectionR_first_shift_meromorphic`, and that needs only the unit-volume conjunct of the γ/2
crossing `DOZZ.gammaHalf_crossing`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The reflected shift and gluing from the first reflection shift.** -/
theorem structureConstant_reflected_shift_and_gluing_of_firstShiftReflection
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hFirstShift : ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
          ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
            MeromorphicOn R {z | |z.im| < h} ∧
            (∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
            ∀ᶠ z in codiscrete ℂ,
              R (z - γ / 2) =
                -(μ * Real.pi : ℂ) * R z /
                  (lFun (-((γ : ℂ) ^ 2) / 4) *
                    lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                    lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) =
                  (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)) :=
  structureConstant_reflected_shift_and_gluing_of_shifts P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃
    hα₂ hα₃ hFirstShift
    (structureConstant_first_shift_strip_unconditional P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃)

/-- **The reflected shift and gluing from the γ/2 crossing.** `hCross` is the unit-volume conjunct
of `gammaHalf_crossing`. -/
theorem structureConstant_reflected_shift_and_gluing_of_crossing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
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
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) =
                  (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)) :=
  structureConstant_reflected_shift_and_gluing_of_firstShiftReflection P X M γ μ η hγ hγ2 hμ hη hX
    hM α₂ α₃ hα₂ hα₃
    (reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM hCross)

end DOZZ.Proofs

end
