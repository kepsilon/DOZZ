/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RootedPairMoments

/-! Identifying the literal positive Taylor mass with the Coulomb mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The four-factor real Coulomb weight identity on positive bases. -/
theorem four_weight_eq (n a b c e₀ e₁ e₂ e₃ : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (n / a) ^ e₀ * (n / b) ^ e₁ * (n / c) ^ e₂ * n ^ e₃ =
      n ^ (e₀ + e₁ + e₂ + e₃) / (a ^ e₀ * b ^ e₁ * c ^ e₂) := by
  rw [Real.div_rpow hn.le ha.le, Real.div_rpow hn.le hb.le, Real.div_rpow hn.le hc.le,
    Real.rpow_add hn (e₀ + e₁ + e₂) e₃, Real.rpow_add hn (e₀ + e₁) e₂,
    Real.rpow_add hn e₀ e₁]
  field_simp

/-- The Coulomb weight is exactly K away from its finite roots, for every charge sign. -/
theorem gammaHalfKernel_coulombWeight (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hxz : x ≠ z) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    coulombWeight γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ x =
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) := by
  have hn : 0 < normPlus x := by unfold normPlus; positivity
  have ha : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hb : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hc : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have hbase₀ : 0 < normPlus x / ‖x - z‖ := div_pos hn ha
  have hbase₁ : 0 < normPlus x / ‖x‖ := div_pos hn hb
  have hbase₂ : 0 < normPlus x / ‖x - 1‖ := div_pos hn hc
  unfold coulombWeight
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, sub_zero]
  change ((ENNReal.ofReal (normPlus x / ‖x - z‖)) ^ (γ * (-γ / 2)) *
      ((ENNReal.ofReal (normPlus x / ‖x‖)) ^ (γ * α₁) *
      (ENNReal.ofReal (normPlus x / ‖x - 1‖)) ^ (γ * α₂))) *
      (ENNReal.ofReal (normPlus x)) ^ (γ * α₃) = _
  rw [← mul_assoc, ENNReal.ofReal_rpow_of_pos hbase₀, ENNReal.ofReal_rpow_of_pos hbase₁,
    ENNReal.ofReal_rpow_of_pos hbase₂, ENNReal.ofReal_rpow_of_pos hn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hbase₀.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hbase₀.le _)
      (Real.rpow_nonneg hbase₁.le _)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.rpow_nonneg hbase₀.le _)
      (Real.rpow_nonneg hbase₁.le _)) (Real.rpow_nonneg hbase₂.le _))]
  congr 1
  rw [four_weight_eq _ _ _ _ _ _ _ _ hn ha hb hc]
  have hexp : γ * (-γ / 2) + γ * α₁ + γ * α₂ + γ * α₃ =
      γ * (α₁ + α₂ + α₃ - γ / 2) := by ring
  have he₀ : γ * (-γ / 2) = -(γ ^ 2 / 2) := by ring
  rw [hexp, he₀, Real.rpow_neg ha.le]
  unfold gammaHalfKernel
  field_simp

/-- The prescribed root values are harmless exactly when the measure has no atom there. -/
theorem gammaHalfMass_eq_coulombMass (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (μ : Measure ℂ)
    (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ) =
      coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
  have hnz : ∀ᵐ x ∂μ, x ≠ z := by apply ae_iff.mpr; simpa using hz
  have hn0 : ∀ᵐ x ∂μ, x ≠ 0 := by apply ae_iff.mpr; simpa using h0
  have hn1 : ∀ᵐ x ∂μ, x ≠ 1 := by apply ae_iff.mpr; simpa using h1
  apply lintegral_congr_ae
  filter_upwards [hnz, hn0, hn1] with x hxz hx0 hx1
  exact (gammaHalfKernel_coulombWeight γ α₁ α₂ α₃ z x hxz hx0 hx1).symm

/-- The identity holds for every supplied GMC, at every deterministic Taylor parameter. -/
theorem gammaHalfMass_eq_coulombMass_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P, (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω) =
      coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM z,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 1] with ω hz h0 h1
  exact gammaHalfMass_eq_coulombMass γ α₁ α₂ α₃ z (M ω) hz h0 h1

end DOZZ.Proofs
