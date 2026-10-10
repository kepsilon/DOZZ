/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionAnnularTestLaw

/-! Compact annular exhaustion for finite chaos measures with no atom at zero. -/

@[expose] public section

open Filter MeasureTheory Set Metric
open scoped Topology Distributions

namespace DOZZ.Proofs

/-- A compact cutoff vanishing near zero and tending to one at every nonzero point. -/
noncomputable def gmcInversionCutoff (n : ℕ) : BoundedContinuousFunction ℂ ℝ := by
  let b : ContDiffBump (0 : ℂ) := ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let c : ContDiffBump (0 : ℂ) := ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
    by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  exact BoundedContinuousFunction.ofNormedAddCommGroup (fun x => b x * (1 - c x))
    (b.continuous.mul (continuous_const.sub c.continuous)) 1 (by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg b.nonneg (sub_nonneg.mpr c.le_one))]
      exact (mul_le_of_le_one_right b.nonneg (sub_le_self _ c.nonneg)).trans b.le_one)

/-- The exhaustion cutoffs are nonnegative and bounded by one. -/
theorem gmcInversionCutoff_bounds (n : ℕ) (x : ℂ) :
    0 ≤ gmcInversionCutoff n x ∧ gmcInversionCutoff n x ≤ 1 := by
  let b : ContDiffBump (0 : ℂ) := ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let c : ContDiffBump (0 : ℂ) := ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
    by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  change 0 ≤ b x * (1 - c x) ∧ b x * (1 - c x) ≤ 1
  exact ⟨mul_nonneg b.nonneg (sub_nonneg.mpr c.le_one),
    (mul_le_of_le_one_right b.nonneg (sub_le_self _ c.nonneg)).trans b.le_one⟩

/-- The support stays inside a closed bounded annulus. -/
theorem gmcInversionCutoff_support_bounds (n : ℕ) :
    ∀ x ∈ tsupport (gmcInversionCutoff n : ℂ → ℝ),
      1 / ((n : ℝ) + 2) ≤ ‖x‖ ∧ ‖x‖ ≤ (n : ℝ) + 2 := by
  let b : ContDiffBump (0 : ℂ) := ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let c : ContDiffBump (0 : ℂ) := ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
    by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  have hmask : tsupport (fun x : ℂ => 1 - c x) ⊆
      (ball (0 : ℂ) (1 / ((n : ℝ) + 2)))ᶜ := by
    apply closure_minimal _ isOpen_ball.isClosed_compl
    intro x hx hxball
    exact hx (by dsimp only; rw [c.one_of_mem_closedBall (ball_subset_closedBall hxball)]; simp)
  intro x hx
  change x ∈ tsupport (fun x => b x * (1 - c x)) at hx
  have hlo := hmask (tsupport_mul_subset_right hx)
  have hhi := tsupport_mul_subset_left hx
  rw [b.tsupport_eq] at hhi
  exact ⟨by simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hlo,
    by simpa only [mem_closedBall, dist_zero_right, b] using hhi⟩

/-- At each nonzero point, the annular cutoffs eventually equal one. -/
theorem gmcInversionCutoff_tendsto (x : ℂ) (hx : x ≠ 0) :
    Tendsto (fun n => gmcInversionCutoff n x) atTop (𝓝 1) := by
  let b : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let c : ℕ → ContDiffBump (0 : ℂ) := fun n =>
    ⟨1 / ((n : ℝ) + 2), 2 / ((n : ℝ) + 2), by positivity,
      by apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  have ht : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  have hb : ∀ᶠ n : ℕ in atTop, ‖x‖ ≤ (n : ℝ) + 1 := by
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop ‖x‖)] with n hn
    exact hn.trans (by linarith)
  apply Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [hb, ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))] with n hn hm
  have hb1 : b n x = 1 := (b n).one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, b] using hn)
  have hc0 : c n x = 0 := image_eq_zero_of_notMem_tsupport (by
    rw [(c n).tsupport_eq]
    simpa only [mem_closedBall, dist_zero_right, not_le, c] using hm)
  change 1 = b n x * (1 - c n x)
  rw [hb1, hc0]
  norm_num

/-- The cutoff has compact support. -/
theorem gmcInversionCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (gmcInversionCutoff n : ℂ → ℝ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2))
  intro x hx
  simpa only [mem_closedBall, dist_zero_right] using
    (gmcInversionCutoff_support_bounds n x (subset_tsupport _ hx)).2

/-- Annular truncation converges in integral for every bounded continuous test. -/
theorem inversion_cutoff_integral_tendsto (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hzero : μ {0} = 0) (f : BoundedContinuousFunction ℂ ℝ) :
    Tendsto (fun n => ∫ x, f x * gmcInversionCutoff n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  have hne : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hzero
  apply tendsto_integral_of_dominated_convergence (bound := fun _ : ℂ => ‖f‖)
  · intro n
    exact (f.continuous.mul (gmcInversionCutoff n).continuous).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs (gmcInversionCutoff n x), abs_of_nonneg (gmcInversionCutoff_bounds n x).1]
      exact (mul_le_of_le_one_right (norm_nonneg _) (gmcInversionCutoff_bounds n x).2).trans (BoundedContinuousFunction.norm_coe_le_norm f x)
  · filter_upwards [hne] with x hx
    simpa only [mul_one] using tendsto_const_nhds.mul (gmcInversionCutoff_tendsto x hx)

/-- Multiplying a bounded test by the cutoff puts it in an open bounded annulus. -/
theorem gmcInversionCutoff_test_annular (n : ℕ) (f : BoundedContinuousFunction ℂ ℝ) :
    HasCompactSupport (f * gmcInversionCutoff n : ℂ → ℝ) ∧
    tsupport (f * gmcInversionCutoff n : ℂ → ℝ) ⊆
      {x : ℂ | 1 / (2 * ((n : ℝ) + 2)) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 3} := by
  refine ⟨(gmcInversionCutoff_hasCompactSupport n).mul_left, ?_⟩
  intro x hx
  have h := gmcInversionCutoff_support_bounds n x (tsupport_mul_subset_right hx)
  constructor
  · apply lt_of_lt_of_le _ h.1
    apply one_div_lt_one_div_of_lt
    · positivity
    · linarith
  · linarith [h.2]

end DOZZ.Proofs
