/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Residual.Assembly
public import DOZZ.ShiftEquations.DualFirstCase.Assembly
public import DOZZ.ShiftEquations.Gluing.ReflectedClosed

/-!
# The residual factor from the γ/2 crossing, the two dual seeds and the off-pole identification

The residual-factor statement `unitVolume_residual_factor_eq_one` (the single input of the
conditional assembly `dozz_main_of_residual_factor` of the DOZZ formula) follows from
`unitVolume_residual_factor_eq_one_of_shifts` with

* the first structure shift closed (`structureConstant_first_shift_strip_unconditional`, from the
  unreflected formula), and
* the first-case dual structure shift (`structureConstant_dual_shift_strip_first_case`) from the two
  dual crossing seeds, the reflected shift and gluing
  (`structureConstant_reflected_shift_and_gluing`) and the off-pole identification
  `reflection_Rtheor_off_poles`; the reflected shift and gluing come from the crossing alone
  (`structureConstant_reflected_shift_and_gluing_of_crossing`).

The four inputs are the statements of `gammaHalf_crossing`, `dual_crossing_seed_one`,
`dual_crossing_seed_two` and `reflection_Rtheor_off_poles`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

universe u

namespace DOZZ.Proofs

/-- **The residual factor from the γ/2 crossing, the two dual seeds and the off-pole
identification.** -/
theorem unitVolume_residual_factor_eq_one_of_crossing_seeds
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ) (U : ℂ → ℂ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hU : IsUpsilon γ U)
    (hCross : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hεlo : γ / 2 < ε) (_hεhi : ε < 2 / γ)
    (_hα : α < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ < α + α' + ε - γ / 2)
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    structureConstant P M γ μ (α' - γ / 2) ε α =
        gammaHalfCrossingMultiplier γ μ α' ε α *
          structureConstant P M γ μ α' (ε + γ / 2) α ∧
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hseedOne : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        structureConstant P M γ μ (α - 2 / γ) ε α' =
          dualCrossingMultiplier γ α' α ε *
            reflectionR P γ μ ε Bε Z *
              structureConstant P M γ μ α (2 * Q γ - ε - 2 / γ) α')
    (hseedTwo : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (hOff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hμ : 0 < μ)
    (_hα : γ / 2 < α ∧ α < Q γ) (_hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (_hData : IsReflectionData P γ α B Z),
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ cγ : ℂ, cγ = 1 ∧
              ∀ α₁ α₂ α₃ : ℝ,
                Q γ - η < α₁ → α₁ < Q γ →
                Q γ - η < α₂ → α₂ < Q γ →
                Q γ - η < α₃ → α₃ < Q γ →
                  (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
                    cγ * ((μ : ℂ) ^ ((sExp γ α₁ α₂ α₃ : ℂ)) /
                      Complex.Gamma (sExp γ α₁ α₂ α₃ : ℂ) *
                        dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ)) := by
  refine unitVolume_residual_factor_eq_one_of_shifts P X M γ μ η U hγ hγ2 hγirr hμ hη hX hM hU
    (fun η' hη' α₂ α₃ hα₂ hα₃ =>
      structureConstant_first_shift_strip_unconditional P X M γ μ η' hγ hγ2 hμ hη' hX hM α₂ α₃ hα₂ hα₃)
    (fun η' hη' hsmall α₂ α₃ hα₂ hα₃ => ?_)
  obtain ⟨-, -, -, -, h, hh, C, -, hCm, -, hCv, -, -, -, hs⟩ :=
    structureConstant_dual_shift_strip_first_case P X M γ μ η' hγ hγ2 hγirr hμ hη' hX hM α₂ α₃ hα₂
      hα₃ hsmall hseedOne hseedTwo
      (fun P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃ =>
        structureConstant_reflected_shift_and_gluing_of_crossing P X M γ μ η hγ hγ2 hμ hη hX hM α₂
          α₃ hα₂ hα₃ (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
            (hCross P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2))
      hOff
  exact ⟨h, hh, C, hCm, hCv, hs⟩

end DOZZ.Proofs

end
