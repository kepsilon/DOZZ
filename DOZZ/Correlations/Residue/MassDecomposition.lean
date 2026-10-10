/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.LocalWeight
public import DOZZ.Statements.Correlations.LocalSingularMass

/-! Exact local insertion and complement decomposition of the residue-chart GMC mass. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- The actual Coulomb density is the local singular density of `DOZZ.localSingularMass` on the
unit ball. Only the atomless roots themselves are excluded. -/
theorem residue_local_coulomb_integrand (γ a b c : ℝ) (z w x : ℂ)
    (hz : 2 ≤ ‖z‖) (hz8 : ‖z‖ ≤ 8) (hzw : 3 ≤ ‖z - w‖)
    (hx : x ∈ Metric.ball z 1) (hxz : x ≠ z) (hxw : x ≠ w) :
    ENNReal.ofReal (residueLocalWeight γ (a + b + c) b w x) *
      ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * a) =
        coulombWeight γ ![a, b] ![z, w] c x := by
  have hd : ‖x - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hzbound : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
    simpa only [norm_sub_rev, sub_add_cancel] using norm_add_le (z - x) x
  have hn1 : 1 ≤ ‖x‖ := by linarith only [hz, hd, hzbound]
  have hn : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hn1
  have hnp : normPlus x = ‖x‖ := max_eq_right hn1
  have hzpos : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hwpos : 0 < ‖x - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxw)
  rw [residue_localWeight_eq γ (a + b + c) b z w x hz hz8 hzw hx]
  unfold coulombWeight
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    ENNReal.rpow_eq_pow, hnp]
  rw [ENNReal.ofReal_rpow_of_pos hzpos,
    ENNReal.ofReal_rpow_of_pos (div_pos hn hzpos),
    ENNReal.ofReal_rpow_of_pos (div_pos hn hwpos), ENNReal.ofReal_rpow_of_pos hn,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hn hzpos).le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (div_pos hn hzpos).le _)
      (Real.rpow_nonneg (div_pos hn hwpos).le _)),
    ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hwpos.le _)),
    Real.div_rpow hn.le hzpos.le, Real.div_rpow hn.le hwpos.le,
    show -γ * a = -(γ * a) by ring, Real.rpow_neg hzpos.le]
  congr 1
  rw [show γ * (a + b + c) = γ * a + γ * b + γ * c by ring,
    Real.rpow_add hn, Real.rpow_add hn]
  ring

/-- Exact decomposition, including the entire noncritical root and infinity region in the
complement. Root atomlessness makes the integrand convention of `DOZZ.coulombMass` at the roots
irrelevant. -/
theorem residue_mass_decomposition (γ a b c : ℝ) (z w : ℂ)
    (hz : 2 ≤ ‖z‖) (hz8 : ‖z‖ ≤ 8) (hzw : 3 ≤ ‖z - w‖)
    (μ : Measure ℂ) (hμz : μ {z} = 0) (hμw : μ {w} = 0) :
    coulombMass γ μ ![a, b] ![z, w] c =
      (∫⁻ x, if x ∈ Metric.ball z 1 then
          ENNReal.ofReal (residueLocalWeight γ (a + b + c) b w x) *
            ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * a) else 0 ∂μ) +
      ∫⁻ x, if x ∉ Metric.ball z 1 then coulombWeight γ ![a, b] ![z, w] c x else 0 ∂μ := by
  have hF : Measurable (residueLocalWeight γ (a + b + c) b w) := by
    unfold residueLocalWeight
    fun_prop
  have hloc : Measurable (fun x : ℂ => if x ∈ Metric.ball z 1 then
      ENNReal.ofReal (residueLocalWeight γ (a + b + c) b w x) *
        ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * a) else 0) :=
    Measurable.ite Metric.isOpen_ball.measurableSet
      ((ENNReal.measurable_ofReal.comp hF).mul
        (ENNReal.continuous_rpow_const.measurable.comp (ENNReal.measurable_ofReal.comp (by fun_prop))))
      measurable_const
  rw [coulombMass_eq_lintegral_coulombWeight, ← lintegral_add_left hloc]
  apply lintegral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμz, measure_eq_zero_iff_ae_notMem.mp hμw]
    with x hxz hxw
  by_cases hx : x ∈ Metric.ball z 1
  · simp only [hx, ite_true, not_true_eq_false, ite_false, add_zero]
    exact (residue_local_coulomb_integrand γ a b c z w x hz hz8 hzw hx hxz hxw).symm
  · simp only [hx, ite_false, not_false_eq_true, ite_true, zero_add]

end DOZZ.Proofs
