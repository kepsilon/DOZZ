/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.Reflection
public import DOZZ.FourPoint.Crossing.Parameters
public import DOZZ.Statements.Hypergeom.PlanarGaussConstant
public import DOZZ.Statements.Hypergeom.GaussGPlus
public import DOZZ.Hypergeom.BasisRegularity
import Mathlib.Tactic

/-! # Using the literal unreflected formula in its admissible channel

The sole analytic premise below is the conclusion of
`gammaHalf_full_unreflected_formula`, specialized with epsilon as the first
charge. The charge a is not required to lie below 2/gamma. Reflection gives a
diagonal one-channel formula on the original cut plane.
-/

public section
open MeasureTheory
namespace DOZZ.Proofs

/-- The exact unreflected formula in the epsilon channel transfers to the
original one-channel basis by the affine moment identity. -/
theorem gammaHalf_one_channel_of_full_unreflected {Ω : Type*} [MeasurableSpace Ω]
    (H : ℂ → ℂ → ℂ → ℂ → ℂ)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ a ε c : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hformula :
      let A := gaussParameterA γ (γ / 2) ε a c
      let B := gaussParameterB γ (γ / 2) ε a c
      let C := gaussParameterC γ (γ / 2) ε
      ∀ w ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) ε a c w =
        structureConstant P M γ μ (ε - γ / 2) a c * ‖gaussFMinus H A B C w‖ ^ 2 +
        (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re) *
          structureConstant P M γ μ (ε + γ / 2) a c * ‖gaussFPlus H A B C w‖ ^ 2) :
    let A := gaussParameterA γ (γ / 2) a ε c
    let B := gaussParameterB γ (γ / 2) a ε c
    let C := gaussParameterC γ (γ / 2) a
    ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-γ / 2) a ε c z =
      structureConstant P M γ μ (ε - γ / 2) a c * ‖gaussGMinus H A B C z‖ ^ 2 +
      (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * ε)).re) *
        structureConstant P M γ μ (ε + γ / 2) a c * ‖gaussGPlus H A B C z‖ ^ 2 := by
  dsimp only at hformula ⊢
  have hA : gaussParameterA γ (γ / 2) ε a c = gaussParameterA γ (γ / 2) a ε c := by
    unfold gaussParameterA
    ring
  have hB : gaussParameterB γ (γ / 2) ε a c = gaussParameterB γ (γ / 2) a ε c := by
    unfold gaussParameterB
    ring
  have hC := crossing_gammaHalf_channel_parameter γ a ε c hγ.ne'
  have hCC : (gaussParameterC γ (γ / 2) ε : ℂ) =
      1 + (gaussParameterA γ (γ / 2) a ε c : ℂ) +
        (gaussParameterB γ (γ / 2) a ε c : ℂ) - (gaussParameterC γ (γ / 2) a : ℂ) := by
    exact_mod_cast hC
  intro z hz
  rw [gammaHalf_fourPoint_reflection P X M γ μ a ε c hγ hγ2 hX hM z,
    hformula (1 - z) (one_sub_gaussCutPlane_subset_gaussCutPlane hz), hA, hB]
  unfold gaussFMinus gaussFPlus gaussGMinus gaussGPlus
  rw [hCC]
  have hpow (A B C : ℂ) : 1 - (1 + A + B - C) = C - A - B := by ring
  have hplusA (A B C : ℂ) : A - (1 + A + B - C) + 1 = C - B := by ring
  have hplusB (A B C : ℂ) : B - (1 + A + B - C) + 1 = C - A := by ring
  have hplusC (A B C : ℂ) : 2 - (1 + A + B - C) = 1 + C - A - B := by ring
  rw [hpow, hplusA, hplusB, hplusC]

end DOZZ.Proofs
