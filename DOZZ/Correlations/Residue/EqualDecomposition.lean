/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.MassDecomposition

/-! Both equal critical insertion balls and their full noncritical complement. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- Exact decomposition into the two equal critical insertions and the nonsingular remainder.
The disjoint unit balls are at 3,7; their complement includes infinity. -/
theorem residue_equal_mass_decomposition {Ω : Type*} (M : Ω → Measure ℂ) (ω : Ω)
    (γ α ε : ℝ) (h3 : M ω {3} = 0) (h7 : M ω {7} = 0) :
    coulombMass γ (M ω) ![α, α] ![3, 7] ε =
      (localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
       localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω) +
      ∫⁻ x, if ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1 then
        coulombWeight γ ![α, α] ![3, 7] ε x else 0 ∂M ω := by
  have hloc (z w : ℂ) : Measurable (fun x : ℂ => if x ∈ Metric.ball z 1 then
      ENNReal.ofReal (residueLocalWeight γ (2 * α + ε) α w x) *
        ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) else 0) := by
    have hF : Measurable (residueLocalWeight γ (2 * α + ε) α w) := by
      unfold residueLocalWeight; fun_prop
    exact Measurable.ite Metric.isOpen_ball.measurableSet
      ((ENNReal.measurable_ofReal.comp hF).mul
        (ENNReal.continuous_rpow_const.measurable.comp (ENNReal.measurable_ofReal.comp (by fun_prop))))
      measurable_const
  have hdisj : Disjoint (Metric.ball (3 : ℂ) 1) (Metric.ball (7 : ℂ) 1) :=
    Metric.ball_disjoint_ball (by norm_num [dist_eq_norm] : (1 : ℝ) + 1 ≤ dist (3 : ℂ) 7)
  have hS : α + α + ε = 2 * α + ε := by ring
  unfold localSingularMass
  have hsum : Measurable (fun x : ℂ =>
      (if x ∈ Metric.ball (3 : ℂ) 1 then ENNReal.ofReal (residueLocalWeight γ (2 * α + ε) α 7 x) *
        ENNReal.rpow (ENNReal.ofReal ‖x - 3‖) (-γ * α) else 0) +
      (if x ∈ Metric.ball (7 : ℂ) 1 then ENNReal.ofReal (residueLocalWeight γ (2 * α + ε) α 3 x) *
        ENNReal.rpow (ENNReal.ofReal ‖x - 7‖) (-γ * α) else 0)) := (hloc 3 7).add (hloc 7 3)
  rw [coulombMass_eq_lintegral_coulombWeight, ← lintegral_add_left (hloc 3 7),
    ← lintegral_add_left hsum]
  apply lintegral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h3, measure_eq_zero_iff_ae_notMem.mp h7]
    with x hx3 hx7
  have hswap : coulombWeight γ ![α, α] ![3, 7] ε x = coulombWeight γ ![α, α] ![7, 3] ε x := by
    unfold coulombWeight
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  by_cases hxb3 : x ∈ Metric.ball (3 : ℂ) 1
  · have hxb7 : x ∉ Metric.ball (7 : ℂ) 1 := fun hh => Set.disjoint_left.mp hdisj hxb3 hh
    simp only [hxb3, hxb7, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
      false_and, add_zero]
    have hh := residue_local_coulomb_integrand γ α α ε 3 7 x (by norm_num) (by norm_num) (by norm_num) hxb3 hx3 hx7
    rw [hS] at hh
    exact hh.symm
  · by_cases hxb7 : x ∈ Metric.ball (7 : ℂ) 1
    · simp only [hxb3, hxb7, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
        and_false, zero_add, add_zero]
      have hh := residue_local_coulomb_integrand γ α α ε 7 3 x (by norm_num) (by norm_num) (by norm_num) hxb7 hx7 hx3
      rw [hS] at hh
      exact hswap.trans hh.symm
    · simp only [hxb3, hxb7, ite_true, ite_false, not_false_eq_true, and_self, zero_add]

end DOZZ.Proofs
