/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.Assembly
public import DOZZ.FourPoint.Crossing.ZeroChannel
import Mathlib.Tactic

/-! # A crossing reduction with the two BPZ inputs explicit

The inputs are the literal half-charge BPZ conclusion (`DOZZ.degenerateFourPoint_BPZ`) and the
literal unreflected formula conclusion (`DOZZ.gammaHalf_full_unreflected_formula`). The diagonal
classification `DOZZ.degenerateFourPoint_diagonal_classification` is discharged here by the generic
classification and the full-domain probabilistic collision limit.
-/

public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Both crossing identities of `DOZZ.gammaHalf_crossing` follow from the two literal independent
BPZ inputs. -/
theorem gammaHalf_crossing_of_BPZ_and_unreflected {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hεhi : ε < 2 / γ) (hα : α < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hBPZ : IsRealGaussSolution
      (gaussParameterA γ (γ / 2) α' ε α) (gaussParameterB γ (γ / 2) α' ε α)
      (gaussParameterC γ (γ / 2) α')
      (fun z => fourPointT P M γ μ (-γ / 2) α' ε α z))
    (hformula :
      let a := gaussParameterA γ (γ / 2) ε α' α
      let b := gaussParameterB γ (γ / 2) ε α' α
      let c := gaussParameterC γ (γ / 2) ε
      ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) ε α' α z =
        structureConstant P M γ μ (ε - γ / 2) α' α * ‖gaussFMinus H a b c z‖ ^ 2 +
        (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re) *
          structureConstant P M γ μ (ε + γ / 2) α' α * ‖gaussFPlus H a b c z‖ ^ 2) :
    structureConstant P M γ μ (α' - γ / 2) ε α =
      gammaHalfCrossingMultiplier γ μ α' ε α *
        structureConstant P M γ μ α' (ε + γ / 2) α ∧
    unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
      gammaHalfUnitCrossingMultiplier γ μ α' ε α *
        unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by
  have hεQ : ε < Q γ := by unfold Q; linarith only [hεhi, hγ]
  have hsum : 2 * Q γ + γ / 2 < α' + ε + α := by linarith only [hs]
  have hdiag := gammaHalf_zero_channel_of_gauss_solution hH P X M γ μ α' ε α
    hγ hγ2 hμ hα' hεQ hα hsum hX hM hBPZ
  exact gammaHalf_crossing_of_diagonal_and_unreflected hH P X M γ μ α' ε α
    hγ hγ2 hμ hεhi hα hα' hs hX hM hdiag hformula

end DOZZ.Proofs
