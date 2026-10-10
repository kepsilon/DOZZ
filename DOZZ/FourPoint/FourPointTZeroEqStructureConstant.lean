/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.GMC.Construction.RootedCircleMassLimit

/-! Combining coincident insertions at zero, with atoms of the GMC at both roots ruled out. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Distributions

namespace DOZZ.Proofs

/-- A deterministic positive-base Coulomb weight combines its two finite roots. -/
theorem three_weight_eq (n a b c d e : ℝ)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b) :
    (n / a) ^ c * (n / b) ^ d * n ^ e = n ^ (c + d + e) / (a ^ c * b ^ d) := by
  rw [Real.div_rpow hn.le ha.le, Real.div_rpow hn.le hb.le,
    Real.rpow_add hn (c + d) e, Real.rpow_add hn c d]
  field_simp

/-- The literal Coulomb mass at coincident zero insertions equals rho for an atomless measure. -/
theorem coulombMass_at_zero_eq_rho (γ χ α₁ α₂ α₃ : ℝ) (M : Measure ℂ)
    (h0 : M {0} = 0) (h1 : M {1} = 0) :
    coulombMass γ M ![-χ, α₁, α₂] ![0, 0, 1] α₃ = rho γ M (α₁ - χ) α₂ α₃ := by
  have hn0 : ∀ᵐ x ∂M, x ≠ 0 := by apply ae_iff.mpr; simpa using h0
  have hn1 : ∀ᵐ x ∂M, x ≠ 1 := by apply ae_iff.mpr; simpa using h1
  unfold coulombMass rho
  apply lintegral_congr_ae
  filter_upwards [hn0, hn1] with x hx0 hx1
  have hn : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hb : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have hbase : 0 < normPlus x / ‖x‖ := div_pos hn ha
  have hbase1 : 0 < normPlus x / ‖x - 1‖ := div_pos hn hb
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one, sub_zero]
  change ((ENNReal.ofReal (normPlus x / ‖x‖)) ^ (γ * -χ) *
      ((ENNReal.ofReal (normPlus x / ‖x‖)) ^ (γ * α₁) *
      (ENNReal.ofReal (normPlus x / ‖x - 1‖)) ^ (γ * α₂))) *
      (ENNReal.ofReal (normPlus x)) ^ (γ * α₃) = _
  rw [← mul_assoc, ENNReal.ofReal_rpow_of_pos hbase, ENNReal.ofReal_rpow_of_pos hbase,
    ENNReal.ofReal_rpow_of_pos hbase1, ENNReal.ofReal_rpow_of_pos hn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hbase.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hbase.le _)
      (Real.rpow_nonneg hbase.le _)),
    ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (Real.rpow_nonneg hbase.le _)
      (Real.rpow_nonneg hbase.le _)) (Real.rpow_nonneg hbase1.le _)),
    ← Real.rpow_add hbase]
  have hexp : γ * -χ + γ * α₁ = γ * (α₁ - χ) := by ring
  rw [hexp]
  congr 1
  rw [three_weight_eq _ _ _ _ _ _ hn ha hb]
  congr 2
  ring

/-- Fusing the degenerate insertion at zero changes the first three-point charge by `-χ`
([KRV, (Fundrelation1)]). -/
theorem fourPointT_zero_eq_structureConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ < α₁ + α₂ + α₃ - χ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    fourPointT P M γ μ (-χ) α₁ α₂ α₃ 0 =
      structureConstant P M γ μ (α₁ - χ) α₂ α₃ := by
  have _hDomain : 0 < μ ∧ α₁ - χ < Q γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧
      2 * Q γ < α₁ + α₂ + α₃ - χ := ⟨hμ, hα₁, hα₂, hα₃, hs⟩
  have hsExp : fourPointSExp γ (-χ) α₁ α₂ α₃ = sExp γ (α₁ - χ) α₂ α₃ := by
    unfold fourPointSExp sExp
    congr 1
    ring
  have hmass : ∀ᵐ ω ∂P,
      coulombMass γ (M ω) ![-χ, α₁, α₂] ![0, 0, 1] α₃ =
        rho γ (M ω) (α₁ - χ) α₂ α₃ := by
    filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω h0 h1
    exact coulombMass_at_zero_eq_rho γ χ α₁ α₂ α₃ (M ω) h0 h1
  unfold fourPointT structureConstant
  rw [hsExp]
  congr 2
  apply lintegral_congr_ae
  filter_upwards [hmass] with ω hω
  exact congrArg (fun m : ℝ≥0∞ => ENNReal.rpow m (-sExp γ (α₁ - χ) α₂ α₃)) hω

end DOZZ.Proofs
