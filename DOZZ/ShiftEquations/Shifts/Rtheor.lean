/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.RtheorIdentification
public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.Brownian.ReflectionPoleIsolation
import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.ShiftEquations.Shift.Wrappers
import DOZZ.ShiftEquations.DualR.Wrapper
import DOZZ.ShiftEquations.Reflection.EndpointContinuity

/-!
# `R = R^DOZZ` from the second dual crossing seed

The two Brownian `R_theor` statements are proved in `RtheorIdentification` from the statements
`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionR_dual_shift_unknown_constant` and
`DOZZ.reflection_endpoint_and_gamma_continuity` at universe `0` ([KRV, §10.6]). Using the γ/2
crossing `gammaHalf_crossing`, the reductions below discharge all three from the statement of
`dual_crossing_seed_two` alone:

* the first shift is `reflectionR_first_shift_meromorphic_of_crossing`;
* the dual shift with unknown constant is
  `reflectionR_dual_shift_unknown_constant_of_crossing_seed`;
* the endpoint limits and continuity in `γ` are
  `reflection_endpoint_and_gamma_continuity_of_representation`, fed the `R̄` representation
  `reflectionBarR_holomorphic_representation_of_crossing`.

So both `R_theor` statements depend only on the second dual seed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- **`R = R^DOZZ` off the poles, from the second dual seed.** `hseedTwo` is the complete statement
of `dual_crossing_seed_two` at universe `0`. -/
theorem reflection_Rtheor_off_poles_of_seedTwo
    (hseedTwo : ∀ {Ω : Type} [MeasurableSpace Ω]
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
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) :=
  reflection_Rtheor_off_poles_of_shift_equations
    (fun P X M γ μ hγ hγ2 hμ hX hM =>
      reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM
        fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
          (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)
    (fun P X M γ μ hγ hγ2 hγirr hμ hX hM =>
      reflectionR_dual_shift_unknown_constant_of_crossing_seed P X M γ μ hγ hγ2 hγirr hμ hX hM
        (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
          (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)
        fun α ε α' h1 h2 h3 h4 => hseedTwo P M X γ μ α ε α' hγ hγ2 hμ h1 h2 h3 h4 hX hM)
    (fun P X M hX μ hμ hM =>
      reflection_endpoint_and_gamma_continuity_of_representation P X M hX μ hμ hM
        fun γ Mγ hγ hγ2 hMγ I _ hI =>
          reflectionBarR_holomorphic_representation_of_crossing P X Mγ γ hγ hγ2 hX hMγ
            (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
              (gammaHalf_crossing P X Mγ γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hMγ).2)
            I hI)
    P γ μ α hγ hγ2 hμ hα hPole B Z hData

/-- **`R - R^DOZZ → 0` at the poles, from the second dual seed.** -/
theorem reflection_Rtheor_punctured_of_seedTwo
    (hseedTwo : ∀ {Ω : Type} [MeasurableSpace Ω]
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
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α₀ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα₀ : γ / 2 < α₀ ∧ α₀ < Q γ)
    (n : ℕ) (hn : reflectionExponent γ α₀ = n + 1)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ =>
      (reflectionR P γ μ α (B α) Z : ℂ) - reflectionDOZZ γ μ (α : ℂ))
        (𝓝[≠] α₀) (𝓝 0) :=
  reflection_Rtheor_punctured_of_offPoleEquality P γ μ α₀ hγ hγ2 hμ hα₀ n hn B Z hData
    fun α h1 h2 hPole hD => reflection_Rtheor_off_poles_of_seedTwo hseedTwo P γ μ α hγ hγ2 hμ
      ⟨h1, h2⟩ hPole (B α) Z hD

end DOZZ.Proofs

end
