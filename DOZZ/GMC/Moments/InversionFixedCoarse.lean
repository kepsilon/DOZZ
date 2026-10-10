/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionPotentialExtension

/-! Uniform fine-circle convergence against a fixed source circle on punctured charts. -/

@[expose] public section

open MeasureTheory Set Metric Real
open DOZZ.Proofs.CirclePotential

namespace DOZZ.Proofs

/-- The fixed source-circle potential after inversion is Lipschitz where the two target
points have a common positive lower norm bound. -/
theorem inversion_innerPot_lipschitz_on_norm_lower_bound
    (y : ℂ) (s : ℝ) {u x : ℂ} {m : ℝ} (hm : 0 < m)
    (hu : m ≤ ‖u‖) (hx : m ≤ ‖x‖) :
    |innerPot y s u⁻¹ - innerPot y s x⁻¹| ≤
      ((Real.exp s + 1) / m ^ 2) * ‖u - x‖ := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (hm.trans_le hu)
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hm.trans_le hx)
  have hlog := abs_log_max_sub_le u⁻¹ x⁻¹ y (Real.exp_pos (-s))
  have hpin := abs_log_normPlus_sub_le u⁻¹ x⁻¹
  have he : innerPot y s u⁻¹ - innerPot y s x⁻¹ =
      -(Real.log (max ‖u⁻¹ - y‖ (Real.exp (-s))) -
        Real.log (max ‖x⁻¹ - y‖ (Real.exp (-s)))) +
      (Real.log (normPlus u⁻¹) - Real.log (normPlus x⁻¹)) := by
    unfold innerPot
    ring
  have hdist : ‖u⁻¹ - x⁻¹‖ ≤ ‖u - x‖ / m ^ 2 := by
    rw [complexInv_distance_of_ne_zero hu0 hx0]
    apply div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hm)
    simpa only [pow_two] using mul_le_mul hu hx hm.le (norm_nonneg _)
  rw [he]
  calc
    _ ≤ |-(Real.log (max ‖u⁻¹ - y‖ (Real.exp (-s))) -
        Real.log (max ‖x⁻¹ - y‖ (Real.exp (-s))))| +
        |Real.log (normPlus u⁻¹) - Real.log (normPlus x⁻¹)| := abs_add_le _ _
    _ ≤ ‖u⁻¹ - x⁻¹‖ / Real.exp (-s) + ‖u⁻¹ - x⁻¹‖ := by
      rw [abs_neg]
      exact add_le_add hlog hpin
    _ = (Real.exp s + 1) * ‖u⁻¹ - x⁻¹‖ := by
      rw [Real.exp_neg, div_inv_eq_mul]
      ring
    _ ≤ (Real.exp s + 1) * (‖u - x‖ / m ^ 2) :=
      mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by ring

/-- Fine target circles approach the fixed source-circle potential with an explicit uniform
error. The source center is arbitrary; only the target chart needs a lower norm bound. -/
theorem inversion_circleAverage_fixed_source_error_le
    (y : ℂ) (s : ℝ) {x : ℂ} {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε)
    (hsmall : m + ε ≤ ‖x‖) :
    |circleAverage (fun u => innerPot y s u⁻¹) x ε - innerPot y s x⁻¹| ≤
      ((Real.exp s + 1) / m ^ 2) * ε := by
  have hx : m ≤ ‖x‖ := by linarith only [hsmall, hε]
  have hnorm : ∀ u ∈ sphere x |ε|, m ≤ ‖u‖ := by
    intro u hu
    have hux : ‖u - x‖ = ε := by
      simpa only [mem_sphere_iff_norm, abs_of_pos hε] using hu
    have ht := norm_sub_le u (u - x)
    rw [sub_sub_cancel, hux] at ht
    linarith only [ht, hsmall]
  have hU : sphere x |ε| ⊆ ({0} : Set ℂ)ᶜ := by
    intro u hu
    change u ≠ 0
    exact norm_pos_iff.mp (hm.trans_le (hnorm u hu))
  have hi : CircleIntegrable (fun u => innerPot y s u⁻¹) x ε :=
    ((continuous_innerPot y s).comp_continuousOn
      (continuousOn_inv₀.mono hU)).circleIntegrable'
  apply abs_circleAverage_sub_le hi
  intro u hu
  have ht := inversion_innerPot_lipschitz_on_norm_lower_bound y s hm (hnorm u hu) hx
  have hux : ‖u - x‖ = ε := by
    simpa only [mem_sphere_iff_norm, abs_of_pos hε] using hu
  simpa only [hux] using ht

/-- The transformed fine-circle/source-coarse covariance and the pulled-source covariance
have the same fixed-coarse limit, with error linear in the fine cutoff. -/
theorem inversion_mixed_fixed_coarse_difference_le
    (y : ℂ) (s r : ℝ) {x : ℂ} {m : ℝ} (hm : 0 < m)
    (hsmall : m + Real.exp (-r) ≤ ‖x‖) :
    |circleAverage (fun u => innerPot y s u⁻¹) x (Real.exp (-r)) -
      circleKernel x⁻¹ r y s| ≤
      ((Real.exp s + 1) / m ^ 2 + (Real.exp s + 1)) * Real.exp (-r) := by
  have ht := inversion_circleAverage_fixed_source_error_le y s hm (Real.exp_pos (-r)) hsmall
  have ho := abs_circleKernel_sub_integral_gffKernel_le x⁻¹ y r s
  rw [integral_gffKernel_circleMeasure] at ho
  calc
    _ ≤ |circleAverage (fun u => innerPot y s u⁻¹) x (Real.exp (-r)) -
        innerPot y s x⁻¹| + |innerPot y s x⁻¹ - circleKernel x⁻¹ r y s| :=
      abs_sub_le _ _ _
    _ ≤ ((Real.exp s + 1) / m ^ 2) * Real.exp (-r) +
        (Real.exp s + 1) * Real.exp (-r) := by
      rw [abs_sub_comm (innerPot y s x⁻¹)]
      exact add_le_add ht ho
    _ = _ := by ring

/-- Fixed-coarse mixed covariance convergence is uniform in both centers when the target
centers have a common positive lower norm bound. -/
theorem inversion_mixed_fixed_coarse_uniform (s : ℝ) {m η : ℝ}
    (hm : 0 < m) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ δ → ∀ x : ℂ, 2 * m ≤ ‖x‖ → ∀ y : ℂ,
      |circleAverage (fun u => innerPot y s u⁻¹) x ε -
        circleKernel x⁻¹ (Real.log (1 / ε)) y s| < η := by
  let C := (Real.exp s + 1) / m ^ 2 + (Real.exp s + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min m (η / (2 * C)), lt_min hm (by positivity), ?_⟩
  intro ε hε hεδ x hx y
  have hεm : ε ≤ m := hεδ.trans (min_le_left _ _)
  have hεη : ε ≤ η / (2 * C) := hεδ.trans (min_le_right _ _)
  have hexp : Real.exp (-Real.log (1 / ε)) = ε := by
    rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]
  have hsmall : m + Real.exp (-Real.log (1 / ε)) ≤ ‖x‖ := by
    rw [hexp]
    linarith only [hεm, hx]
  have ht := inversion_mixed_fixed_coarse_difference_le y s (Real.log (1 / ε)) hm hsmall
  rw [hexp] at ht
  have hbound : C * ε ≤ η / 2 := by
    calc
      C * ε ≤ C * (η / (2 * C)) := mul_le_mul_of_nonneg_left hεη hC.le
      _ = η / 2 := by field_simp
  exact ht.trans_lt (hbound.trans_lt (by linarith only [hη]))

end DOZZ.Proofs
