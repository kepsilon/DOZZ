/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.AffineMoment
public import DOZZ.Correlations.Symmetry.InversionSwap

/-! The literal canonical rho is the two-finite-root Coulomb mass in the residue chart. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The two conventions for values at the roots agree away from those roots. -/
theorem residue_rho_coulombWeight (γ a b c : ℝ) (x : ℂ) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ENNReal.ofReal (normPlus x ^ (γ * (a + b + c)) /
      (‖x‖ ^ (γ * a) * ‖x - 1‖ ^ (γ * b))) =
      coulombWeight γ ![a, b] ![0, 1] c x := by
  have hn := normPlus_pos' x
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  unfold coulombWeight
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    sub_zero, ENNReal.rpow_eq_pow]
  rw [ENNReal.ofReal_rpow_of_pos (div_pos hn h0),
    ENNReal.ofReal_rpow_of_pos (div_pos hn h1), ENNReal.ofReal_rpow_of_pos hn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hn h0).le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (div_pos hn h0).le _)
      (Real.rpow_nonneg (div_pos hn h1).le _)), Real.div_rpow hn.le h0.le,
    Real.div_rpow hn.le h1.le]
  congr 1
  rw [show γ * (a + b + c) = γ * a + γ * b + γ * c by ring,
    Real.rpow_add hn, Real.rpow_add hn]
  ring

/-- Atomlessness removes the difference between the conventions of `DOZZ.rho` and
`DOZZ.coulombMass` at 0, 1. -/
theorem residue_rho_eq_coulombMass (γ a b c : ℝ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    rho γ μ a b c = coulombMass γ μ ![a, b] ![0, 1] c := by
  unfold rho
  rw [coulombMass_eq_lintegral_coulombWeight]
  apply lintegral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0, measure_eq_zero_iff_ae_notMem.mp h1]
    with x hx0 hx1
  exact residue_rho_coulombWeight γ a b c x hx0 hx1

/-- The canonical three-point exponent includes the infinity charge. -/
theorem residueTotalSExp_two (γ a b c : ℝ) :
    residueTotalSExp γ ![a, b] c = sExp γ a b c := by
  unfold residueTotalSExp sExp
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Move the two finite insertions from 0,1 to 3,7. Both are outside the equator and their
separation is four, so the exact local-tail domains hold. -/
theorem residue_unitVolume_finite_chart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    unitVolumeStructureConstant P M γ a b c =
      2 / γ * (4 : ℝ) ^ (-(γ * (a + b - c) * sExp γ a b c / 2)) *
        (∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![a, b] ![3, 7] c)
          (-sExp γ a b c) ∂P).toReal := by
  have ha : (4 : ℂ) ≠ 0 := by norm_num
  have hchart := residue_coulombMass_affine_moment P X hX γ hγ hγ2 M hM
    ![a, b] ![0, 1] c 4 3 ha
  have hroots : (fun k : Fin 2 => (4 : ℂ) * (![0, 1] k) + 3) = ![3, 7] := by
    ext k; fin_cases k <;> norm_num
  rw [hroots, residueTotalSExp_two] at hchart
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hchart
  norm_num only [Complex.norm_ofNat] at hchart
  have hatoms : ∀ᵐ ω ∂P, M ω {0} = 0 ∧ M ω {1} = 0 :=
    (gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 0).and
      (gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 1)
  have hrho : (∫⁻ ω, ENNReal.rpow (rho γ (M ω) a b c) (-sExp γ a b c) ∂P) =
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![a, b] ![0, 1] c) (-sExp γ a b c) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hatoms] with ω hω
    rw [residue_rho_eq_coulombMass γ a b c (M ω) hω.1 hω.2]
  have hr := congrArg ENNReal.toReal hchart
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 4) _),
    ← hrho] at hr
  unfold unitVolumeStructureConstant
  rw [hr]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
  have hfac : (4 : ℝ) ^ (γ * (a + b - c) * sExp γ a b c / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp [hfac]
  simp only [ENNReal.rpow_eq_pow]

end DOZZ.Proofs
