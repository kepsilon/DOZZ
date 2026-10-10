/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.Rho
public import DOZZ.Statements.Defs.ExtendedSeiberg3
public import DOZZ.Statements.GMC.CoulombMass
public import DOZZ.GMC.Construction.RootedCircleMassLimit
@[expose] public section
open MeasureTheory Set
open scoped Distributions ENNReal
namespace DOZZ.Proofs

/-- The real rho density is the product of the three chart factors away from its roots. -/
theorem rho_coulomb_weight (γ α₁ α₂ α₃ : ℝ) (x : ℂ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ENNReal.ofReal (normPlus x ^ (γ * (α₁ + α₂ + α₃)) /
      (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂))) =
    ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x‖)) (γ * α₁) *
      ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - 1‖)) (γ * α₂) *
      ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * α₃) := by
  have hn : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  simp only [ENNReal.rpow_eq_pow]
  rw [ENNReal.ofReal_rpow_of_pos (p := γ * α₁) (div_pos hn h0),
    ENNReal.ofReal_rpow_of_pos (p := γ * α₂) (div_pos hn h1), ENNReal.ofReal_rpow_of_pos (p := γ * α₃) hn]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hn h0).le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (div_pos hn h0).le _)
      (Real.rpow_nonneg (div_pos hn h1).le _))]
  congr 1
  rw [Real.div_rpow hn.le h0.le, Real.div_rpow hn.le h1.le]
  rw [mul_add, mul_add, Real.rpow_add hn, Real.rpow_add hn]
  ring

/-- Rho agrees with the two finite roots and one infinity-root Coulomb mass for atomless roots. -/
theorem rho_eq_coulombMass (γ α₁ α₂ α₃ : ℝ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    rho γ μ α₁ α₂ α₃ = coulombMass γ μ ![α₁, α₂] ![0, 1] α₃ := by
  have ha0 : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]; simpa only [not_not, ofPred_eq_eq_singleton] using h0
  have ha1 : ∀ᵐ x ∂μ, x ≠ 1 := by
    rw [ae_iff]; simpa only [not_not, ofPred_eq_eq_singleton] using h1
  apply lintegral_congr_ae
  filter_upwards [ha0, ha1] with x hx0 hx1
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_zero] using rho_coulomb_weight γ α₁ α₂ α₃ x hx0 hx1

/-- Every GMC version has the rho/Coulomb identity almost surely. -/
theorem gmc_rho_eq_coulombMass_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) :
    ∀ᵐ ω ∂P, rho γ (M ω) α₁ α₂ α₃ =
      coulombMass γ (M ω) ![α₁, α₂] ![0, 1] α₃ := by
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 1] with ω h0 h1
  exact rho_eq_coulombMass γ α₁ α₂ α₃ (M ω) h0 h1
/-- The three-charge domain supplies every hypothesis of the global moment theorem. -/
theorem extendedSeiberg3_coulomb_parameters (γ α₁ α₂ α₃ : ℝ)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    (Function.Injective (![0, 1] : Fin 2 → ℂ)) ∧
    (∀ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k < Q γ) ∧ α₃ < Q γ ∧
    ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ =
      -sExp γ α₁ α₂ α₃) ∧
    ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ < 4 / γ ^ 2) ∧
    (∀ k : Fin 2, (2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ <
      2 / γ * (Q γ - (![α₁, α₂] : Fin 2 → ℝ) k)) ∧
    ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ <
      2 / γ * (Q γ - α₃)) := by
  obtain ⟨h₁, h₂, h₃, hp⟩ := hα
  have he : (2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ =
      -sExp γ α₁ α₂ α₃ := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sExp]
    ring
  refine ⟨?_, ?_, h₃, he, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro k
    fin_cases k
    · exact h₁
    · exact h₂
  · rw [he]
    exact (lt_min_iff.mp hp).1
  · intro k
    rw [he]
    fin_cases k
    · exact (lt_min_iff.mp (lt_min_iff.mp hp).2).1
    · exact (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hp).2).2).1
  · rw [he]
    exact (lt_min_iff.mp (lt_min_iff.mp (lt_min_iff.mp hp).2).2).2

/-- The target rho moment is exactly the specialized global Coulomb moment. -/
theorem rho_moment_eq_coulomb_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ) :
    (∫⁻ ω, ENNReal.rpow (rho γ (M ω) α₁ α₂ α₃) (-sExp γ α₁ α₂ α₃) ∂P) =
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α₁, α₂] ![0, 1] α₃)
      ((2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ) ∂P := by
  have he : (2 * Q γ - ((∑ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k) + α₃)) / γ =
      -sExp γ α₁ α₂ α₃ := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sExp]
    ring
  rw [he]
  apply lintegral_congr_ae
  filter_upwards [gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃] with ω hω
  rw [hω]
end DOZZ.Proofs
