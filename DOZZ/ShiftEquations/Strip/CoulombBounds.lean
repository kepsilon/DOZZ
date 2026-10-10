/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ComplementMass
public import DOZZ.ShiftEquations.Strip.OriginLimit

/-! Deterministic comparison of the critical Coulomb mass and the origin singular mass. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical

namespace DOZZ.Proofs

/-- The normalized root factor on the unit disk is the singular radial weight. -/
theorem lastone_root_factor_unit (γ a : ℝ) (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - 0‖)) (γ * a) =
      ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a) := by
  simp only [ENNReal.rpow_eq_pow]
  rw [normPlus, max_eq_left hx.le, sub_zero,
    ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr hx0), ENNReal.ofReal_one, one_div,
    ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  congr 1
  ring

/-- On the unit disk the remaining finite insertion gives a fixed lower bound. -/
theorem lastone_coulombWeight_lower (γ a b c : ℝ) (hγb : 0 ≤ γ * b)
    (x : ℂ) (hx : ‖x‖ < 1) (hx0 : x ≠ 0) :
    ENNReal.ofReal (1 / 2 : ℝ) ^ (γ * b) *
      ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a) ≤
        coulombWeight γ ![a, b] ![0, 1] c x := by
  have hnp : normPlus x = 1 := max_eq_left hx.le
  have hx1 : x ≠ 1 := by intro he; simp [he] at hx
  have hs : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have hs2 : ‖x - 1‖ ≤ 2 := by
    have h := norm_sub_le x 1
    norm_num at h
    linarith
  have hratio : (1 / 2 : ℝ) ≤ normPlus x / ‖x - 1‖ := by
    rw [hnp, le_div_iff₀ hs]
    linarith
  have hfac := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hratio) hγb
  unfold coulombWeight
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ]
  rw [lastone_root_factor_unit γ a x hx hx0]
  simp only [hnp, ENNReal.rpow_eq_pow, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one]
  simpa only [hnp, ENNReal.rpow_eq_pow, mul_comm] using mul_le_mul_left hfac
    (ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a))

/-- On the half disk the second finite insertion gives a fixed upper bound. -/
theorem lastone_coulombWeight_local_upper (γ a b c : ℝ) (hγa : 0 < γ * a)
    (hγb : 0 ≤ γ * b) (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    coulombWeight γ ![a, b] ![0, 1] c x ≤
      (2 : ℝ≥0∞) ^ (γ * b) * ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a) := by
  by_cases hx0 : x = 0
  · subst x
    simp [coulombWeight, normPlus, hγa]
  have hxunit : ‖x‖ < 1 := by linarith
  have hnp : normPlus x = 1 := max_eq_left hxunit.le
  have hs : 1 / 2 ≤ ‖x - 1‖ := by
    have h := norm_sub_le x (x - 1)
    rw [sub_sub_cancel] at h
    norm_num at h
    linarith
  have hs0 : 0 < ‖x - 1‖ := by linarith
  have hratio : normPlus x / ‖x - 1‖ ≤ 2 := by
    rw [hnp, div_le_iff₀ hs0]
    linarith
  have hfac := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hratio) hγb
  unfold coulombWeight
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ]
  rw [lastone_root_factor_unit γ a x hxunit hx0]
  simp only [hnp, ENNReal.rpow_eq_pow, ENNReal.ofReal_one, ENNReal.one_rpow, mul_one]
  norm_num only [ENNReal.ofReal_ofNat] at hfac
  simpa only [hnp, ENNReal.rpow_eq_pow, mul_comm] using mul_le_mul_left hfac
    (ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a))

/-- Outside the half disk the critical insertion may be removed entirely. -/
theorem lastone_coulombWeight_exterior_upper (γ a b c : ℝ)
    (hγa : 0 ≤ γ * a) (haQ : γ * a ≤ γ * Q γ)
    (x : ℂ) (hx : 1 / 2 ≤ ‖x‖) :
    coulombWeight γ ![a, b] ![0, 1] c x ≤
      (2 : ℝ≥0∞) ^ (γ * Q γ) * coulombWeight γ ![b] ![1] c x := by
  have hr0 : 0 < ‖x‖ := by linarith
  have hratio : normPlus x / ‖x‖ ≤ 2 := by
    rw [div_le_iff₀ hr0]
    exact max_le (by linarith) (by linarith [norm_nonneg x])
  have hfac := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hratio) hγa
  norm_num only [ENNReal.ofReal_ofNat] at hfac
  have hfac' : ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - 0‖)) (γ * a) ≤
      (2 : ℝ≥0∞) ^ (γ * Q γ) := by
    rw [sub_zero]
    exact hfac.trans (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) haQ)
  rw [residue_coulombWeight_two_split]
  exact mul_le_mul' hfac' le_rfl

/-- The Coulomb mass lies between a multiple of the origin mass and that mass plus a
fixed one-root subcritical mass. Only the origin's zero atom is required. -/
theorem lastone_coulombMass_bounds (γ a b c : ℝ) (hγa : 0 < γ * a)
    (hγb : 0 ≤ γ * b) (haQ : γ * a ≤ γ * Q γ) (M : Measure ℂ) (hM0 : M {0} = 0) :
    ENNReal.ofReal (1 / 2 : ℝ) ^ (γ * b) *
        localSingularMass (fun _ : Unit => M) (fun _ => 1) 0 γ a () ≤
      coulombMass γ M ![a, b] ![0, 1] c ∧
      coulombMass γ M ![a, b] ![0, 1] c ≤
        (2 : ℝ≥0∞) ^ (γ * b) * localSingularMass (fun _ : Unit => M) (fun _ => 1) 0 γ a () +
        (2 : ℝ≥0∞) ^ (γ * Q γ) * coulombMass γ M ![b] ![1] c := by
  have hconst1 : ENNReal.ofReal (1 / 2 : ℝ) ^ (γ * b) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hγb ENNReal.ofReal_ne_top
  have hconst2 : (2 : ℝ≥0∞) ^ (γ * b) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hγb (by norm_num)
  have hconstQ : (2 : ℝ≥0∞) ^ (γ * Q γ) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hkernel : localSingularMass (fun _ : Unit => M) (fun _ => 1) 0 γ a () =
      ∫⁻ x, (if ‖x‖ < 1 then ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a) else 0) ∂M := by
    simp only [localSingularMass, Metric.mem_ball, dist_zero_right, sub_zero,
      ENNReal.ofReal_one, one_mul]
  rw [hkernel, coulombMass_eq_lintegral_coulombWeight]
  constructor
  · rw [← lintegral_const_mul' _ _ hconst1]
    apply lintegral_mono_ae
    have hne : ∀ᵐ x ∂M, x ≠ 0 := by simpa only [ae_iff, not_not, ofPred_eq_eq_singleton] using hM0
    filter_upwards [hne] with x hx0
    by_cases hx : ‖x‖ < 1
    · rw [ite_eq_left hx]
      exact lastone_coulombWeight_lower γ a b c hγb x hx hx0
    · simp only [ite_eq_right hx, mul_zero]
      exact zero_le
  · have hfirst : Measurable (fun x : ℂ => (2 : ℝ≥0∞) ^ (γ * b) *
        (if ‖x‖ < 1 then ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * a) else 0)) := by
      apply measurable_const.mul
      apply Measurable.ite (measurableSet_lt continuous_norm.measurable measurable_const)
      · exact (ENNReal.continuous_rpow_const.measurable.comp
          (ENNReal.measurable_ofReal.comp continuous_norm.measurable))
      · exact measurable_const
    rw [coulombMass_eq_lintegral_coulombWeight,
      ← lintegral_const_mul' _ _ hconst2, ← lintegral_const_mul' _ _ hconstQ,
      ← lintegral_add_left hfirst]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hx : ‖x‖ < 1 / 2
    · have hx1 : ‖x‖ < 1 := by linarith
      rw [ite_eq_left hx1]
      exact (lastone_coulombWeight_local_upper γ a b c hγa hγb x hx).trans (le_add_right le_rfl)
    · exact (lastone_coulombWeight_exterior_upper γ a b c hγa.le haQ x (le_of_not_gt hx)).trans
        (le_add_left le_rfl)

end DOZZ.Proofs
