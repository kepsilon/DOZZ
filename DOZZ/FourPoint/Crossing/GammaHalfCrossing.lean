/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.BPZReduction
public import DOZZ.Statements.Hypergeom.GaussHypergeometricExists
public import DOZZ.Statements.FourPoint.DegenerateFourPointBPZ
public import DOZZ.Statements.FourPoint.GammaHalfFullUnreflectedFormula
import Mathlib.Tactic

/-! # The half-charge crossing reduction

Both external hypotheses retain all binders and the exact conclusions of the statements
`DOZZ.degenerateFourPoint_BPZ` and `DOZZ.gammaHalf_full_unreflected_formula`, for the ambient
probability space. The proofs of these two statements can be passed directly to this reduction,
which gives the unconditional theorem `gammaHalf_crossing`. The target is the exact conclusion of
`DOZZ.gammaHalf_crossing`.
-/

public section
open MeasureTheory
namespace DOZZ.Proofs

/-- The conclusion of `DOZZ.gammaHalf_crossing` follows from the two exact theorem inputs
`DOZZ.degenerateFourPoint_BPZ` and `DOZZ.gammaHalf_full_unreflected_formula`. The Gauss family,
physical guards, normalization and coefficient extraction are all discharged. -/
theorem gammaHalf_crossing_of_unreflected {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hεlo : γ / 2 < ε) (hεhi : ε < 2 / γ)
    (hα : α < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hBPZ : ∀
      (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
      (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
      (_hχ : χ = γ / 2 ∨ χ = 2 / γ)
      (_hα₁ : α₁ < Q γ) (_hα₂ : α₂ < Q γ) (_hα₃ : α₃ < Q γ)
      (_hs : 2 * Q γ + χ < α₁ + α₂ + α₃)
      (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
      IsRealGaussSolution
        (gaussParameterA γ χ α₁ α₂ α₃)
        (gaussParameterB γ χ α₁ α₂ α₃)
        (gaussParameterC γ χ α₁)
        (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z))
    (hUnreflected : ∀
      {H : ℂ → ℂ → ℂ → ℂ → ℂ}
      (_hH : IsGaussHypergeometricFamily H)
      (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
      (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
      (_hαlo : γ / 2 < α₁) (_hαhi : α₁ < 2 / γ)
      (_hα₂ : α₂ < Q γ) (_hα₃ : α₃ < Q γ)
      (_hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
      (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
      let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
      let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
      let c := gaussParameterC γ (γ / 2) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
              ‖gaussFMinus H a b c z‖ ^ 2 +
            (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
              structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
                ‖gaussFPlus H a b c z‖ ^ 2) :
    structureConstant P M γ μ (α' - γ / 2) ε α =
        gammaHalfCrossingMultiplier γ μ α' ε α *
          structureConstant P M γ μ α' (ε + γ / 2) α ∧
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by
  obtain ⟨H, hH⟩ := DOZZ.gauss_hypergeometric_exists
  have hεQ : ε < Q γ := by unfold Q; linarith only [hεhi, hγ]
  have hsum : 2 * Q γ + γ / 2 < α' + ε + α := by linarith only [hs]
  have hsum' : 2 * Q γ + γ / 2 < ε + α' + α := by linarith only [hs]
  have hbpz := hBPZ P X M γ μ (γ / 2) α' ε α hγ hγ₂ hμ
    (Or.inl rfl) hα' hεQ hα hsum hX hM
  have hformula := hUnreflected hH P X M γ μ ε α' α hγ hγ₂ hμ
    hεlo hεhi hα' hα hsum' hX hM
  exact gammaHalf_crossing_of_BPZ_and_unreflected hH P X M γ μ α' ε α
    hγ hγ₂ hμ hεhi hα hα' hs hX hM (by simpa only [neg_div] using hbpz) hformula

/-- Unconditional crossing theorem, with precisely the statement of `DOZZ.gammaHalf_crossing`. -/
theorem gammaHalf_crossing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hεlo : γ / 2 < ε) (hεhi : ε < 2 / γ)
    (hα : α < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    structureConstant P M γ μ (α' - γ / 2) ε α =
        gammaHalfCrossingMultiplier γ μ α' ε α *
          structureConstant P M γ μ α' (ε + γ / 2) α ∧
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by
  exact gammaHalf_crossing_of_unreflected P X M γ μ α' ε α
    hγ hγ₂ hμ hεlo hεhi hα hα' hs hX hM
    DOZZ.degenerateFourPoint_BPZ DOZZ.gammaHalf_full_unreflected_formula


end DOZZ.Proofs
