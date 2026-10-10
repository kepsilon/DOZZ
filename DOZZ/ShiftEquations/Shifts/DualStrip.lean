/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.ShiftEquations.DualFirstCase.Assembly
import DOZZ.Correlations.Tails.ReflectionWitness
import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.ShiftEquations.Gluing.ReflectedClosed
import DOZZ.ShiftEquations.Residual.Composition
import DOZZ.FourPoint.Crossing.GammaHalfCrossing
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Brownian.Reflection.RtheorIdentification
import DOZZ.DOZZAlgebra.FormulaReflection
import DOZZ.DOZZAlgebra.FormulaShiftBinv
import DOZZ.Roots.Existence
import DOZZ.Roots.MainConditional

/-!
# The dual structure shift on the box

The statement `structureConstant_dual_shift_strip` allows every `η` with `Q - 2η > γ`, while the
source's dual fusion reaches every spectator pair of the box only when `η ≤ γ/4`. The proof splits
accordingly.

* `η ≤ γ/4`: the first-case dual structure shift `structureConstant_dual_shift_strip_first_case`,
  whose reflected-shift input `structureConstant_reflected_shift_and_gluing` comes from the γ/2
  crossing.
* `η > γ/4`: the DOZZ formula. The total representatives are `C = dozzFormula γ μ U · α₂ α₃` and
  `R = reflectionDOZZ γ μ`; the gluing and the dual shift are `dozzFormula_reflection` and
  `dozzFormula_shift_binv`. The DOZZ formula on the physical interval `(2η, Q)` is given by the
  conditional assembly `dozz_main_of_residual_factor`, whose single input, the residual factor
  `unitVolume_residual_factor_eq_one`, is supplied by
  `unitVolume_residual_factor_eq_one_of_crossing_seeds`.

In both cases the reflection coefficient is identified on the whole physical interval by the
off-pole identification `reflection_Rtheor_off_poles` and, at the Gamma poles `p_α ∈ ℕ_{>0}`, by the
vanishing of both totalized coefficients.

This module imports the conditional assembly `dozz_main_of_residual_factor` of the DOZZ formula;
neither the modules of `DOZZ/Roots` nor the first-case helper import this module.

The remaining inputs of `structureConstant_dual_shift_strip_of_seeds` are the statements of
`dual_crossing_seed_one`, `dual_crossing_seed_two` and `reflection_Rtheor_off_poles`, quantified
over `Ω : Type u`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

universe u

namespace DOZZ.Proofs

/-! ### The reflection coefficients on the physical interval -/

/-- At a Gamma pole `p_α = n + 1` the totalized probabilistic coefficient vanishes. -/
theorem reflectionR_eq_zero_of_reflectionExponent_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ μ α : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    {n : ℕ} (hn : reflectionExponent γ α = (n + 1 : ℕ)) :
    reflectionR P γ μ α B Z = 0 := by
  unfold reflectionR
  rw [hn, Real.Gamma_neg_nat_eq_zero, mul_zero, zero_mul, zero_mul]

/-- At a Gamma pole `p_α = n + 1` the totalized DOZZ coefficient vanishes. -/
theorem reflectionDOZZ_ofReal_eq_zero_of_reflectionExponent_eq {γ μ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (hμ : 0 < μ) {n : ℕ} (hn : reflectionExponent γ α = (n + 1 : ℕ)) :
    reflectionDOZZ γ μ (α : ℂ) = 0 := by
  rw [reflectionDOZZ_ofReal γ μ α hγ hγ2 hμ, hn, Real.Gamma_neg_nat_eq_zero, zero_div,
    mul_zero, Complex.ofReal_zero]

/-- **Physical values of `R^DOZZ`.** Given the off-pole identification, the totalized DOZZ
coefficient equals the probabilistic coefficient of a witness family at every charge of the physical
interval; at the Gamma poles both vanish. -/
theorem reflectionDOZZ_eq_reflectionR_of_offPoles {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z)
    (hOff : ∀ α : ℝ, γ / 2 < α ∧ α < Q γ → ReflectionPoleFree γ α →
      ∀ (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ),
        IsReflectionData P γ α B Z → (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ))
    (α : ℝ) (h1 : γ / 2 < α) (h2 : α < Q γ) :
    reflectionDOZZ γ μ (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ) := by
  by_cases hPole : ReflectionPoleFree γ α
  · exact (hOff α ⟨h1, h2⟩ hPole (B α) Z (hB α h1 h2)).symm
  · have hn : ∃ n : ℕ, reflectionExponent γ α = (n + 1 : ℕ) := by
      by_contra h
      exact hPole fun n hn => h ⟨n, hn⟩
    obtain ⟨n, hn⟩ := hn
    rw [reflectionDOZZ_ofReal_eq_zero_of_reflectionExponent_eq hγ hγ2 hμ hn,
      reflectionR_eq_zero_of_reflectionExponent_eq P γ μ α (B α) Z hn, Complex.ofReal_zero]

/-- The physical triples of the box: for `α ∈ (2η, Q)` and spectators in `(Q - η, Q)` the zero mode
is positive, so the triple satisfies the extended Seiberg bounds and avoids the Gamma poles of
`s`. -/
theorem dualStrip_physical_triple {γ η α α₂ α₃ : ℝ} (hγ : 0 < γ)
    (hα : 2 * η < α ∧ α < Q γ) (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ) :
    0 < sExp γ α α₂ α₃ ∧ ExtendedSeiberg3 γ α α₂ α₃ := by
  have hs : 0 < sExp γ α α₂ α₃ := by
    unfold sExp
    exact div_pos (by linarith [hα.1, hα₂.1, hα₃.1]) hγ
  refine ⟨hs, hα.2, hα₂.2, hα₃.2, ?_⟩
  have h2γ : 0 < 2 / γ := div_pos two_pos hγ
  have h1 : 0 < 4 / γ ^ 2 := by positivity
  have h2 : 0 < 2 / γ * (Q γ - α) := mul_pos h2γ (sub_pos.mpr hα.2)
  have h3 : 0 < 2 / γ * (Q γ - α₂) := mul_pos h2γ (sub_pos.mpr hα₂.2)
  have h4 : 0 < 2 / γ * (Q γ - α₃) := mul_pos h2γ (sub_pos.mpr hα₃.2)
  have hmin := lt_min h1 (lt_min h2 (lt_min h3 h4))
  linarith

/-! ### The second case: the DOZZ formula -/

/-- **The dual structure shift from the DOZZ formula** (the second case, `η > γ/4`). `hMain` is the
DOZZ formula on the physical interval `(2η, Q)` and `hOff` the off-pole identification, both at the
supplied space. The representatives are total: `C` is the DOZZ formula in its first charge and `R`
the DOZZ reflection coefficient. -/
theorem structureConstant_dual_shift_strip_of_dozzFormula
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ) (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    (hMain : ∀ α : ℝ, 2 * η < α → α < Q γ →
      (structureConstant P M γ μ α α₂ α₃ : ℂ) = dozzFormula γ μ U α α₂ α₃)
    (hOff : ∀ α : ℝ, γ / 2 < α ∧ α < Q γ → ReflectionPoleFree γ α →
      ∀ (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ),
        IsReflectionData P γ α B Z → (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, R z = reflectionDOZZ γ μ z) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              ∀ᶠ z in codiscrete ℂ,
                C (z + 2 / γ) =
                  -(1 / (Real.pi * dualMu γ μ)) *
                    shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
                      C (z - 2 / γ) := by
  obtain ⟨B, Z, hSLP, hB⟩ := exists_source_reflection_witness P X M γ hγ hγ2 hX hM
  have hB' : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z :=
    fun α _ hα => hB α hα
  have hk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ) := fun k hk =>
    four_div_sq_ne_int_of_irrational hγirr k (by rw [Int.cast_natCast]; exact hk)
  exact ⟨B, Z, hSLP, hB', 1, one_pos, fun z => dozzFormula γ μ U z α₂ α₃, reflectionDOZZ γ μ,
    (meromorphicOn_dozzFormula hγ hγ2 hμ hU _ _).mono_set (subset_univ _),
    (meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set (subset_univ _),
    fun α h1 h2 => (hMain α h1 h2).symm,
    reflectionDOZZ_eq_reflectionR_of_offPoles P γ μ hγ hγ2 hμ B Z hB' hOff,
    Eventually.of_forall fun _ => rfl,
    dozzFormula_reflection hγ hγ2 hμ hU _ _,
    dozzFormula_shift_binv hγ hγ2 hk hμ hU _ _⟩

/-! ### The dual structure shift from the dual seeds and the off-pole identification -/

/-- **The dual structure shift from the two dual crossing seeds and the off-pole identification.**
The three inputs are the complete statements of `dual_crossing_seed_one`, `dual_crossing_seed_two`
and `reflection_Rtheor_off_poles`, quantified over `Ω : Type u`. For `η ≤ γ/4` the first-case helper
applies, with the reflected shift and gluing from the γ/2 crossing; for `η > γ/4` the DOZZ formula
from the conditional assembly `dozz_main_of_residual_factor`, whose residual input comes from the same
three statements and the crossing. -/
theorem structureConstant_dual_shift_strip_of_seeds
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
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
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, R z = reflectionDOZZ γ μ z) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              ∀ᶠ z in codiscrete ℂ,
                C (z + 2 / γ) =
                  -(1 / (Real.pi * dualMu γ μ)) *
                    shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
                      C (z - 2 / γ) := by
  rcases le_or_gt η (γ / 4) with hsmall | -
  · -- first case: the dual fusion reaches every spectator pair of the box
    exact structureConstant_dual_shift_strip_first_case P X M γ μ η hγ hγ2 hγirr hμ hη hX hM
      α₂ α₃ hα₂ hα₃ hsmall hseedOne hseedTwo
      (fun P X M γ μ η hγ hγ2 hμ hη hX hM α₂ α₃ hα₂ hα₃ =>
        structureConstant_reflected_shift_and_gluing_of_crossing P X M γ μ η hγ hγ2 hμ hη hX hM
          α₂ α₃ hα₂ hα₃ fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
            (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)
      hOff
  · -- second case: the DOZZ formula of the conditional root
    obtain ⟨U, hU⟩ := (dozz_existence γ hγ hγ2).1
    refine structureConstant_dual_shift_strip_of_dozzFormula P X M γ μ η hγ hγ2 hγirr hμ hX hM
      α₂ α₃ U hU (fun α h1 h2 => ?_) fun α hα hPole B Z hD =>
        hOff P γ μ α hγ hγ2 hμ hα hPole B Z hD
    obtain ⟨hs, hES⟩ := dualStrip_physical_triple hγ ⟨h1, h2⟩ hα₂ hα₃
    refine dozz_main_of_residual_factor γ μ hγ hγ2 hμ α α₂ α₃ hES (fun n hn => ?_) U hU P X M hX hM
      fun P X M γ μ η U hγ hγ2 hγirr hμ hη hX hM hU =>
        unitVolume_residual_factor_eq_one_of_crossing_seeds P X M γ μ η U hγ hγ2 hγirr hμ hη hX
          hM hU (fun P X M γ μ α' ε α hγ hγ₂ hμ hεlo hεhi hα hα' hs hX hM =>
            gammaHalf_crossing P X M γ μ α' ε α hγ hγ₂ hμ hεlo hεhi hα hα' hs hX hM)
          hseedOne hseedTwo hOff
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

end DOZZ.Proofs

end
