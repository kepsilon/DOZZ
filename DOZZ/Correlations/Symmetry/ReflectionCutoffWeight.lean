/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionCircleMean
public import Mathlib.Topology.UniformSpace.HeineCantor
@[expose] public section
open Filter Set
open scoped Topology
namespace DOZZ.Proofs

/-- Exponentiation of a bounded continuous real potential. -/
noncomputable def symmetryExponentialBCF (f : BoundedContinuousFunction ℂ ℝ) :
    BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨fun x => Real.exp (f x), Real.continuous_exp.comp f.continuous⟩
    (2 * Real.exp ‖f‖) (fun x y => by
      change dist (Real.exp (f x)) (Real.exp (f y)) ≤ _
      rw [Real.dist_eq]
      have hx : |Real.exp (f x)| ≤ Real.exp ‖f‖ := by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm x))
      have hy : |Real.exp (f y)| ≤ Real.exp ‖f‖ := by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr ((le_abs_self _).trans (f.norm_coe_le_norm y))
      exact (abs_sub _ _).trans (by linarith only [hx, hy]))

theorem symmetryExponentialBCF_apply (f : BoundedContinuousFunction ℂ ℝ) (x : ℂ) :
    symmetryExponentialBCF f x = Real.exp (f x) := rfl

/-- The deterministic finite-cutoff density after reflection and re-pinning. -/
noncomputable def symmetryReflectionCutoffWeight (γ r : ℝ) : BoundedContinuousFunction ℂ ℝ :=
  symmetryExponentialBCF (γ ^ 2 • symmetryCirclePotentialMean r + (4 : ℝ) • symmetryReflectionPotentialBCF)

/-- The limiting deterministic density after reflection and re-pinning. -/
noncomputable def symmetryReflectionLimitWeight (γ : ℝ) : BoundedContinuousFunction ℂ ℝ :=
  symmetryExponentialBCF ((γ ^ 2 + 4) • symmetryReflectionPotentialBCF)

theorem symmetryReflectionCutoffWeight_apply (γ r : ℝ) (x : ℂ) :
    symmetryReflectionCutoffWeight γ r x = Real.exp (γ ^ 2 * symmetryCirclePotentialMean r x +
      4 * symmetryReflectionPotential x) := by
  simp only [symmetryReflectionCutoffWeight, symmetryExponentialBCF_apply,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.smul_apply, smul_eq_mul]
  rfl

theorem symmetryReflectionLimitWeight_apply (γ : ℝ) (x : ℂ) :
    symmetryReflectionLimitWeight γ x = Real.exp ((γ ^ 2 + 4) * symmetryReflectionPotential x) := rfl

/-- The entire deterministic Wick correction converges uniformly, including at infinity. -/
theorem symmetryReflectionCutoffWeight_uniform (γ : ℝ) :
    TendstoUniformly (fun r x => symmetryReflectionCutoffWeight γ r x)
      (symmetryReflectionLimitWeight γ) atTop := by
  let B := (γ ^ 2 + 4) * Real.log 2
  have hb (r : ℝ) (x : ℂ) : |γ ^ 2 * symmetryCirclePotentialMean r x +
      4 * symmetryReflectionPotential x| ≤ B := by
    calc
      _ ≤ |γ ^ 2 * symmetryCirclePotentialMean r x| + |4 * symmetryReflectionPotential x| := abs_add_le _ _
      _ ≤ γ ^ 2 * Real.log 2 + 4 * Real.log 2 := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg γ), abs_of_pos (by norm_num : (0 : ℝ) < 4)]
        exact add_le_add (mul_le_mul_of_nonneg_left (symmetryCirclePotentialMean_bound r x) (sq_nonneg _))
          (mul_le_mul_of_nonneg_left (symmetryReflectionPotential_bound x) (by norm_num))
      _ = B := by dsimp [B]; ring
  have hv (x : ℂ) : |(γ ^ 2 + 4) * symmetryReflectionPotential x| ≤ B := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ γ ^ 2 + 4)]
    exact mul_le_mul_of_nonneg_left (symmetryReflectionPotential_bound x) (by positivity)
  have h : TendstoUniformly (fun r x => γ ^ 2 * symmetryCirclePotentialMean r x +
      4 * symmetryReflectionPotential x) (fun x => (γ ^ 2 + 4) * symmetryReflectionPotential x) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have he : Tendsto (fun r : ℝ => γ ^ 2 * (2 * Real.exp (-r))) atTop (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using
        (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul 2 |>.const_mul (γ ^ 2)
    filter_upwards [he.eventually (gt_mem_nhds hε)] with r hr x
    rw [Real.dist_eq]
    have heq : |(γ ^ 2 + 4) * symmetryReflectionPotential x -
        (γ ^ 2 * symmetryCirclePotentialMean r x + 4 * symmetryReflectionPotential x)| =
        γ ^ 2 * |symmetryCirclePotentialMean r x - symmetryReflectionPotential x| := by
      rw [show (γ ^ 2 + 4) * symmetryReflectionPotential x -
        (γ ^ 2 * symmetryCirclePotentialMean r x + 4 * symmetryReflectionPotential x) =
        -(γ ^ 2 * (symmetryCirclePotentialMean r x - symmetryReflectionPotential x)) by ring,
        abs_neg, abs_mul, abs_of_nonneg (sq_nonneg γ)]
    rw [heq, symmetryCirclePotentialMean_apply]
    exact (mul_le_mul_of_nonneg_left (symmetryReflection_circle_potential_error x r)
      (sq_nonneg γ)).trans_lt hr
  have he := UniformContinuousOn.comp_tendstoUniformly (s := Icc (-B) B) (g := Real.exp)
    (fun r x => abs_le.mp (hb r x)) (fun x => abs_le.mp (hv x))
    (isCompact_Icc.uniformContinuousOn_of_continuous Real.continuous_exp.continuousOn) h
  change TendstoUniformly (fun r x => Real.exp (γ ^ 2 * symmetryCirclePotentialMean r x +
    4 * symmetryReflectionPotential x))
    (fun x => Real.exp ((γ ^ 2 + 4) * symmetryReflectionPotential x)) atTop
  exact he
end DOZZ.Proofs
