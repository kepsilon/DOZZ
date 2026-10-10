/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfFullUnreflectedFormula
public import DOZZ.Statements.FourPoint.DegenerateFourPointDiagonalClassification
public import DOZZ.ShiftEquations.Strip.PhysicalHolomorphic
public import DOZZ.ShiftEquations.Gluing.Coefficient
public import DOZZ.ShiftEquations.Gluing.CoefficientAlgebra
import DOZZ.FourPoint.Crossing.Multiplier
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import Mathlib.Tactic

/-! # The first structure shift on its unreflected fusion interval

The two diagonal formulas identify the second coefficient on the supplied probability space. The
literal Gamma quotient then gives the total shift coefficient.
-/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- The first-shift seed, with no crossing or dual-shift input. -/
theorem firstStrip_shift_seed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (h₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (h₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (a : ℝ) (ha : γ / 2 + 2 * η < a) (ha2 : a < 2 / γ) :
    (structureConstant P M γ μ (a + γ / 2) α₂ α₃ : ℂ) =
      -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) a α₂ α₃ *
        (structureConstant P M γ μ (a - γ / 2) α₂ α₃ : ℂ) := by
  obtain ⟨H, hH⟩ := gauss_hypergeometric_exists
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have haQ : a < Q γ := by rw [hQ]; linarith
  have hs := (firstStrip_fusion_interval γ η α₂ α₃ hη h₂.1 h₃.1).2 a ha
  have hc : 0 < gaussParameterC γ (γ / 2) a ∧ gaussParameterC γ (γ / 2) a < 1 := by
    rw [gaussRatio_param_c (by positivity : γ / 2 ≠ 0) (by
      unfold Q; field_simp; ring)]
    have hmul := mul_lt_mul_of_pos_left ha2 (show 0 < γ / 2 by positivity)
    have he : γ / 2 * (2 / γ) = 1 := by field_simp
    rw [he] at hmul
    constructor
    · linarith only [mul_pos (half_pos hγ) (by linarith only [ha, hη.1] : (0 : ℝ) < a - γ / 2)]
    · linarith only [hmul, sq_nonneg (γ / 2)]
  have h22 := DOZZ.degenerateFourPoint_diagonal_classification hH P X M γ μ (γ / 2)
    a α₂ α₃ hγ hγ2 hμ (Or.inl rfl) haQ h₂.2 h₃.2 hs hX hM
  have hform := DOZZ.gammaHalf_full_unreflected_formula hH P X M γ μ a α₂ α₃
    hγ hγ2 hμ (by linarith [hη.1]) ha2 h₂.2 h₃.2 hs hX hM
  have hk := second_coefficient_of_classification P M hH γ μ (γ / 2) a α₂ α₃
    ((-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * a)).re) *
      structureConstant P M γ μ (a + γ / 2) α₂ α₃)
    (complex_ne_int_of_mem_unit hc.1 hc.2) h22 (by
      intro z hz
      simpa only [mul_assoc, neg_div] using hform z hz)
  have hratio := gaussCoefficientRatio_mul_eq_shiftCoeffA_half (z := a)
    (α₂ := α₂) (α₃ := α₃) hγ (ne_of_lt hc.2)
  let L := lR (-(γ ^ 2) / 4) * lR (γ * a / 2) * lR (2 + γ ^ 2 / 4 - γ * a / 2)
  have hcast : (L : ℂ) = lFun (-((γ / 2 : ℝ) : ℂ) ^ 2) *
      lFun (((γ / 2 : ℝ) : ℂ) * a) *
      lFun (2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * a) := by
    have e1 : -((γ / 2 : ℝ) : ℂ) ^ 2 = ((-(γ ^ 2) / 4 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((γ / 2 : ℝ) : ℂ) * a = ((γ * a / 2 : ℝ) : ℂ) := by push_cast; ring
    have e3 : 2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * a =
      ((2 + γ ^ 2 / 4 - γ * a / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e3, e1, e2, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR]
    simp only [L, Complex.ofReal_mul]
  rw [← hcast] at hratio
  have hunit : 0 < γ * a / 2 ∧ γ * a / 2 < 1 := by
    have := mul_lt_mul_of_pos_left ha2 hγ
    have he : γ * (2 / γ) = 2 := by field_simp
    rw [he] at this
    constructor
    · linarith only [mul_pos hγ (by linarith only [ha, hη.1, hγ] : (0 : ℝ) < a)]
    · linarith only [this]
  have hneg := lR_ne_zero_of_mem_neg (r := -(γ ^ 2) / 4)
    (by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le])
    (by linarith only [sq_pos_of_pos hγ])
  have hlast : lR (2 + γ ^ 2 / 4 - γ * a / 2) ≠ 0 := by
    have h0 : -1 < 1 - (2 + γ ^ 2 / 4 - γ * a / 2) := by
      have := hc.1
      rw [gaussRatio_param_c (by positivity : γ / 2 ≠ 0) (by unfold Q; field_simp; ring)] at this
      linarith only [this]
    have h1 : 1 - (2 + γ ^ 2 / 4 - γ * a / 2) < 0 := by linarith only [hunit.2, sq_nonneg γ]
    unfold lR
    exact div_ne_zero
      (Real.Gamma_pos_of_pos (by linarith only [hunit.2, sq_nonneg γ])).ne'
      (Real.Gamma_ne_zero (real_ne_neg_nat_of_frac (k := -1)
        (by push_cast; exact h0) (by push_cast; linarith only [h1])))
  have hL : L ≠ 0 := mul_ne_zero (mul_ne_zero hneg
    (lR_ne_zero_of_mem_unit hunit.1 hunit.2)) hlast
  rw [crossing_planarGauss_real] at hk
  have hden : lR (γ * a / 2) * lR (-(γ ^ 2) / 4) *
      lR (2 + γ ^ 2 / 4 - γ * a / 2) = L := by dsimp [L]; ring
  rw [hden] at hk
  have he : structureConstant P M γ μ (a + γ / 2) α₂ α₃ =
      -(1 / (Real.pi * μ)) *
        (gaussCoefficientRatio (gaussParameterA γ (γ / 2) a α₂ α₃)
          (gaussParameterB γ (γ / 2) a α₂ α₃) (gaussParameterC γ (γ / 2) a) * L) *
        structureConstant P M γ μ (a - γ / 2) α₂ α₃ := by
    field_simp [hL, hμ.ne', Real.pi_ne_zero] at hk ⊢
    linear_combination -hk
  exact_mod_cast (by rw [← hratio]; exact_mod_cast he)

end DOZZ.Proofs
