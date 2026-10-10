/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.Coefficient
public import DOZZ.ShiftEquations.Gluing.CoefficientAlgebra
public import DOZZ.ShiftEquations.Gluing.Meromorphy
public import DOZZ.ShiftEquations.Gluing.RealPoint
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.LFun
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.ShiftEquations.Shift.FirstShift
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import DOZZ.Brownian.Reflection.WitnessIndependence

/-!
# The reflected shift and gluing from the first shifts and the two γ/2 diagonal formulas

For real `α₁` with `Q - γ/16 < α₁ < Q`, the classification
(`DOZZ.degenerateFourPoint_diagonal_classification`) and the reflected formula
(`DOZZ.gammaHalf_reflected_formula`) give `R(α₁) C(2Q - α₁ - γ/2) = ρ C(α₁ - γ/2)`; with the first
reflection shift (`DOZZ.reflectionR_first_shift_meromorphic`) at `α₁ + γ/2` and the Gamma identity
`ρ D = 𝒜`, this is the reflected shift at `α₁` ([KRV, Corollary 10.2], erratum K11, see
docs/ERRATA-AND-DEVIATIONS.md). Both sides are meromorphic on a strip, so it holds near every point
of the strip. Combined with the first structure shift (`DOZZ.structureConstant_first_shift_strip`)
at `z - γ/2` it gives the gluing `C(z) = R(z) C(2Q - z)` ([KRV, Lemma 10.5]). Cutting both functions
off outside a thinner strip makes both identities hold along the codiscrete filter of `ℂ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- On the near-`Q` window, the Gauss parameter `c` of the γ/2 formulas lies in `(0, 1)`. -/
theorem gaussParameterC_half_mem {γ α₁ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (h1 : Q γ - γ / 16 < α₁) (h2 : α₁ < Q γ) :
    0 < gaussParameterC γ (γ / 2) α₁ ∧ gaussParameterC γ (γ / 2) α₁ < 1 := by
  unfold gaussParameterC
  have hpos : 0 < γ / 2 * (Q γ - α₁) := mul_pos (by positivity) (by linarith)
  have hlt : γ / 2 * (Q γ - α₁) < γ / 2 * (γ / 16) :=
    mul_lt_mul_of_pos_left (by linarith) (by positivity)
  constructor <;> nlinarith

/-- **The reflected coefficient at real charges near `Q`**
(`DOZZ.degenerateFourPoint_diagonal_classification` and `DOZZ.gammaHalf_reflected_formula` at the
same charges): `R(α₁) C(2Q - α₁ - γ/2) = ρ C(α₁ - γ/2)`. -/
theorem reflected_coefficient_real {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ α₂ α₃ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hDiagonal : ∀ {H : ℂ → ℂ → ℂ → ℂ → ℂ}, IsGaussHypergeometricFamily H → ∀ α₁ : ℝ,
      α₁ < Q γ → 2 * Q γ + γ / 2 < α₁ + α₂ + α₃ →
      let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
      let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
      let c := gaussParameterC γ (γ / 2) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            (‖gaussFMinus H a b c z‖ ^ 2 +
              gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2))
    (hReflected : ∀ {H : ℂ → ℂ → ℂ → ℂ → ℂ}, IsGaussHypergeometricFamily H → ∀ α₁ : ℝ,
      α₁ < Q γ → 2 * Q γ + γ / 2 < α₁ + α₂ + α₃ → Q γ - α₁ < γ / 2 →
      (∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ γ * (Q γ - α₁) < ξ ∧
        γ * (Q γ - α₁) < (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2)) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
        ∃ Z : Ω → Measure ℝ,
          IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ α₁ (B α₁) Z ∧
          let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
          let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
          let c := gaussParameterC γ (γ / 2) α₁
          ∀ z ∈ gaussCutPlane,
            fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
              structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
                  ‖gaussFMinus H a b c z‖ ^ 2 +
                reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                    ‖gaussFPlus H a b c z‖ ^ 2)
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {B : ℝ → Ω → BrownianPath × BrownianPath} {Z : Ω → Measure ℝ}
    (hRD : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z)
    {α₁ : ℝ} (h1 : Q γ - γ / 16 < α₁) (h2 : α₁ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    reflectionR P γ μ α₁ (B α₁) Z * structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ =
      gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
          (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ := by
  have hc := gaussParameterC_half_mem hγ hγ2 h1 h2
  have hα₁ : γ / 2 < α₁ := by
    have h2γ : γ / 16 < 2 / γ := by
      rw [div_lt_div_iff₀ (by norm_num) hγ]
      nlinarith
    rw [show Q γ = 2 / γ + γ / 2 from rfl] at h1
    linarith
  have h22 := hDiagonal hH α₁ h2 hs
  obtain ⟨B', Z', -, hRD', h37⟩ := hReflected hH α₁ h2 hs (by linarith)
    (reflected_near_window hγ hγ2 h1 h2)
  have h37' : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
          ‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
        (reflectionR P γ μ α₁ (B' α₁) Z' *
          structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃) *
          ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 := by
    intro z hz
    rw [← neg_div]
    exact h37 z hz
  have hK := second_coefficient_of_classification P M hH γ μ (γ / 2) α₁ α₂ α₃ _
    (complex_ne_int_of_mem_unit hc.1 hc.2) h22 h37'
  rw [reflectionR_eq_of_isReflectionData P P γ μ α₁ (B α₁) Z (B' α₁) Z'
    (hRD α₁ hα₁ h2) hRD', hK]

end DOZZ.Proofs

end
