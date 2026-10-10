/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.LocalWeight

/-! Uniform positive C1 families for the actual residue-chart insertion weights. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- All hypotheses of the local-tail weight class `DOZZ.UniformPositiveC1Family` are verified,
uniformly over epsilon in a compact interval. The derivative bound comes from joint smoothness on
a neighborhood. -/
theorem residue_localWeight_uniform_family (γ S α d₀ : ℝ) (hγ : 0 ≤ γ)
    (hS : 0 ≤ S) (hα : 0 ≤ α) (z w : ℂ)
    (hz : 2 ≤ ‖z‖) (hz8 : ‖z‖ ≤ 8) (hzw : 3 ≤ ‖z - w‖) :
    ∃ supBound derivBound lowerBound : ℝ,
      UniformPositiveC1Family {z}
        (fun _ => {F | ∃ ε ∈ Icc 0 d₀, F = residueLocalWeight γ (S + ε) α w})
        (1 / 2) supBound derivBound lowerBound := by
  let H : ℝ × ℂ → ℝ := fun t => ‖t.2‖ ^ (γ * (S + t.1)) / ‖t.2 - w‖ ^ (γ * α)
  let U : Set (ℝ × ℂ) := univ ×ˢ Metric.ball z 1
  have hgeo (x : ℂ) (hx : x ∈ Metric.ball z 1) : x ≠ 0 ∧ x ≠ w := by
    have hd : ‖x - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    constructor
    · intro hh; rw [hh, zero_sub, norm_neg] at hd; linarith only [hz, hd]
    · intro hh; rw [hh, norm_sub_rev] at hd; linarith only [hzw, hd]
  have hU : IsOpen U := isOpen_univ.prod Metric.isOpen_ball
  have hH : ContDiffOn ℝ 1 H U := by
    intro t ht
    exact (residue_localDensity_contDiffAt γ S α w t (hgeo t.2 ht.2).1
      (hgeo t.2 ht.2).2).contDiffWithinAt
  let K : Set (ℝ × ℂ) := Icc 0 d₀ ×ˢ Metric.closedBall z (1 / 2)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall z (1 / 2))
  have hKU : K ⊆ U := by
    intro t ht
    refine ⟨mem_univ _, ?_⟩
    have hd : dist t.2 z ≤ 1 / 2 := ht.2
    exact lt_of_le_of_lt hd (by norm_num)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn
    ((hH.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU)
  let L : ℝ := ‖z‖ ^ (γ * S) / ‖z - w‖ ^ (γ * α)
  have hL : 0 < L := div_pos
    (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 2) hz) _)
    (Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num : (0:ℝ) < 3) hzw) _)
  refine ⟨(10 : ℝ) ^ (γ * (S + d₀)), max D 0, L, by norm_num, by positivity,
    le_max_right _ _, hL, ?_⟩
  intro z' hz' F hF
  have hzz : z' = z := hz'
  subst z'
  obtain ⟨ε, hε, rfl⟩ := hF
  have heq (x : ℂ) (hx : x ∈ Metric.ball z 1) :
      residueLocalWeight γ (S + ε) α w =ᶠ[𝓝 x] fun y => H (ε, y) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
    exact residue_localWeight_eq γ (S + ε) α z w y hz hz8 hzw hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold residueLocalWeight
    fun_prop
  · intro x
    refine ⟨(residue_localWeight_pos γ (S + ε) α w x).le, ?_⟩
    rw [abs_of_pos (residue_localWeight_pos γ (S + ε) α w x)]
    exact residue_localWeight_le γ (S + ε) α (S + d₀) hγ (add_nonneg hS hε.1)
      (add_le_add le_rfl hε.2) hα w x
  · rw [residue_localWeight_eq γ (S + ε) α z w z hz hz8 hzw (Metric.mem_ball_self (by norm_num))]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le (by linarith only [hz])
        (mul_le_mul_of_nonneg_left (by linarith only [hε.1] : S ≤ S + ε) hγ))
      (Real.rpow_nonneg (norm_nonneg _) _)
  · have hball : Metric.ball z (2 * (1 / 2 : ℝ)) = Metric.ball z 1 := by norm_num
    rw [hball]
    intro x hx
    have hh : ContDiffAt ℝ 1 (fun y : ℂ => H (ε, y)) x :=
      (residue_localDensity_contDiffAt γ S α w (ε, x) (hgeo x hx).1 (hgeo x hx).2).comp x
        (contDiffAt_const.prodMk contDiffAt_id)
    exact (hh.congr_of_eventuallyEq (heq x hx)).contDiffWithinAt
  · intro x hx
    have hxball : x ∈ Metric.ball z 1 :=
      lt_of_le_of_lt (show dist x z ≤ (1 / 2 : ℝ) from hx) (by norm_num : (1 / 2 : ℝ) < 1)
    have hh : DifferentiableAt ℝ H (ε, x) := (residue_localDensity_contDiffAt γ S α w (ε, x)
      (hgeo x hxball).1 (hgeo x hxball).2).differentiableAt one_ne_zero
    have hder : HasFDerivAt (fun y : ℂ => H (ε, y))
        ((fderiv ℝ H (ε, x)).comp (ContinuousLinearMap.inr ℝ ℝ ℂ)) x := by
      simpa only [Function.comp_def] using hh.hasFDerivAt.comp x (hasFDerivAt_prodMk_right ε x)
    rw [(heq x hxball).fderiv_eq, hder.fderiv]
    calc _ ≤ ‖fderiv ℝ H (ε, x)‖ * ‖ContinuousLinearMap.inr ℝ ℝ ℂ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ H (ε, x)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one ℝ ℝ ℂ)
      _ ≤ max D 0 := (hD (ε, x) ⟨hε, hx⟩).trans (le_max_left _ _)

end DOZZ.Proofs
