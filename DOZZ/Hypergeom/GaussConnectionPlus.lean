/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import DOZZ.Hypergeom.ConnectionFormulaFromBox
public import DOZZ.Hypergeom.ODE.ConnectionEulerPlusCoefficientBox

/-! Proof of `DOZZ.gauss_connection_plus`, the powered zero-basis Gauss connection formula. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The powered Gauss connection formula follows from the two Euler coefficient boxes. -/
theorem gauss_connection_plus {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFPlus H a b c z =
        (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
          (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) *
            gaussGMinus H a b c z +
        (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
          (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) *
            gaussGPlus H a b c z := by
  let firstBox : GaussConnectionOpenBox := {
    S := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
    T := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
    V := Metric.ball (1 / 4 : ℂ) (1 / 8 : ℝ)
    c₀ := 3 / 4
    δ₀ := 1 / 4
    a₀ := 1 / 4
    hSopen := Metric.isOpen_ball
    hTopen := Metric.isOpen_ball
    hVopen := Metric.isOpen_ball
    hc₀ := by norm_num [Metric.mem_ball, dist_eq_norm]
    hδ₀ := by norm_num [Metric.mem_ball, dist_eq_norm]
    ha₀ := by norm_num [Metric.mem_ball, dist_eq_norm]
    hS := by
      simpa [Complex.ofReal_div] using
        (secondCoefficient_ofReal_ball_subset_integerRange_compl
          (3 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))
    hT := by
      simpa [Complex.ofReal_div] using
        (secondCoefficient_ofReal_ball_subset_integerRange_compl
          (1 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))
  }
  let secondBox : GaussConnectionOpenBox := {
    S := Metric.ball (3 / 4 : ℂ) (1 / 8 : ℝ)
    T := Metric.ball (-(1 / 4 : ℂ)) (1 / 16 : ℝ)
    V := Metric.ball (1 / 2 : ℂ) (1 / 16 : ℝ)
    c₀ := 3 / 4
    δ₀ := -(1 / 4)
    a₀ := 1 / 2
    hSopen := Metric.isOpen_ball
    hTopen := Metric.isOpen_ball
    hVopen := Metric.isOpen_ball
    hc₀ := by norm_num [Metric.mem_ball, dist_eq_norm]
    hδ₀ := by norm_num [Metric.mem_ball, dist_eq_norm]
    ha₀ := by norm_num [Metric.mem_ball, dist_eq_norm]
    hS := by
      simpa [Complex.ofReal_div] using
        (secondCoefficient_ofReal_ball_subset_integerRange_compl
          (3 / 4) (1 / 8) (by norm_num) (by norm_num) (by norm_num))
    hT := secondCoefficient_negativeQuarter_ball_avoids_integers
  }
  have hp : (a, b, c) ∈ gaussConnectionParameterDomain := by
    change (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, c - a - b ≠ (n : ℂ)
    exact ⟨hc, hδ⟩
  exact gauss_connection_plus_of_box_coefficients hH firstBox secondBox
    (connectionPlusFirstCramer_eq_gamma_on_open_box hH)
    (connectionPlusSecondCramer_eq_gamma_on_open_box hH) hp

end DOZZ.Proofs
