/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.MomentRange
public import DOZZ.Statements.GMC.WeightedGmcBallMoment
public import DOZZ.GMC.Moments.WeightedLocalSubunit
public import DOZZ.GMC.Moments.WeightedExponent

/-! # Elementary bounds for weighted local masses

A weighted local mass dominates a fixed multiple of the mass of an off-center subdisk, so it
inherits the divergence of unweighted moments at and above `4/γ²`. For nonpositive charges the
weight is bounded on the disk and the unweighted moment range gives finiteness below `4/γ²`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem offcenter_ball_subset (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4) ⊆ Metric.ball z r := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx ⊢
  have hc : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc ‖x - z‖ = ‖(x - (z + ((r / 2 : ℝ) : ℂ))) + ((r / 2 : ℝ) : ℂ)‖ := by congr 1; ring
    _ ≤ ‖x - (z + ((r / 2 : ℝ) : ℂ))‖ + ‖((r / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
    _ < r := by rw [hc]; linarith

theorem offcenter_dist_bounds (z : ℂ) {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) :
    r / 4 ≤ ‖x - z‖ ∧ ‖x - z‖ ≤ 3 * r / 4 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hc : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : x - z = (x - (z + ((r / 2 : ℝ) : ℂ))) + ((r / 2 : ℝ) : ℂ) := by ring
  constructor
  · have h2 : ((r / 2 : ℝ) : ℂ) = (x - z) - (x - (z + ((r / 2 : ℝ) : ℂ))) := by ring
    have h3 := norm_sub_le (x - z) (x - (z + ((r / 2 : ℝ) : ℂ)))
    rw [← h2, hc] at h3
    linarith
  · rw [h1]
    linarith [norm_add_le (x - (z + ((r / 2 : ℝ) : ℂ))) ((r / 2 : ℝ) : ℂ)]

/-- The weight of a weighted local mass is bounded below on the off-center subdisk. -/
theorem weightedGmcBallMass_ge_offcenter (μ : Measure ℂ) (γ α : ℝ) (z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
        (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) *
        μ (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) ≤
      weightedGmcBallMass γ μ α z r := by
  set B : Set ℂ := Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4) with hB
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  unfold weightedGmcBallMass
  calc min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
          (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) * μ B
      = ∫⁻ _x in B, min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
          (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) ∂μ := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ x in B, ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) ∂μ := by
        apply setLIntegral_mono' hBm
        intro x hx
        obtain ⟨h1, h2⟩ := offcenter_dist_bounds z hr hx
        rcases le_or_gt 0 (-γ * α) with hs | hs
        · refine (min_le_left _ _).trans ?_
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal h1) hs
        · refine (min_le_right _ _).trans ?_
          exact ennreal_rpow_antitone_of_nonpos (ENNReal.ofReal_le_ofReal h2) hs.le
    _ ≤ ∫⁻ x in Metric.ball z r, ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) ∂μ :=
        lintegral_mono_set (offcenter_ball_subset z hr)

/-- At and above `4/γ²` every positive-order weighted local moment diverges. -/
theorem weightedGmcBallMoment_eq_top_of_bulk
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : ℝ) (z : ℂ) (r : ℝ) (hr : 0 < r) (p : ℝ) (hp : 4 / γ ^ 2 ≤ p) :
    weightedGmcBallMoment P M γ α z r p = ⊤ := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  set c : ℝ≥0∞ := min (ENNReal.rpow (ENNReal.ofReal (r / 4)) (-γ * α))
    (ENNReal.rpow (ENNReal.ofReal (3 * r / 4)) (-γ * α)) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    refine (lt_min ?_ ?_).ne'
    · exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (by positivity)) ENNReal.ofReal_ne_top
  have hctop : c ≠ ⊤ := by
    rw [hc]
    exact ne_top_of_le_ne_top (ENNReal.rpow_ne_top_of_ne_zero
      (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top) (min_le_left _ _)
  have htop := gmc_ball_moment_eq_top_of_critical_le P X hX γ hγ hγ2 M hM
    (z + ((r / 2 : ℝ) : ℂ)) (r / 4) (by positivity) p hp
  have hmeas : AEMeasurable (fun ω => M ω (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) ^ p) P :=
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet).pow_const _
  apply top_unique
  calc ⊤ = c ^ p * gmcMassMoment P M (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4)) p := by
        rw [htop, ENNReal.mul_top (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hctop).ne']
    _ = ∫⁻ ω, (c * M ω (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4))) ^ p ∂P := by
        rw [lintegral_congr (fun ω => ENNReal.mul_rpow_of_nonneg c
          (M ω (Metric.ball (z + ((r / 2 : ℝ) : ℂ)) (r / 4))) hp0.le),
          lintegral_const_mul'' _ hmeas]
        rfl
    _ ≤ weightedGmcBallMoment P M γ α z r p := by
        apply lintegral_mono
        intro ω
        exact ENNReal.rpow_le_rpow (weightedGmcBallMass_ge_offcenter (M ω) γ α z hr) hp0.le

/-- For nonpositive charges the weighted local moment is finite below `4/γ²`. -/
theorem weightedGmcBallMoment_lt_top_of_nonpos_charge
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : ℝ) (hα : α ≤ 0) (z : ℂ) (r : ℝ) (p : ℝ) (hp0 : 0 < p)
    (hp : p < 4 / γ ^ 2) :
    weightedGmcBallMoment P M γ α z r p < ⊤ := by
  have hs : 0 ≤ -γ * α := by nlinarith
  set c : ℝ≥0∞ := ENNReal.rpow (ENNReal.ofReal r) (-γ * α) with hc
  have hctop : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hs ENNReal.ofReal_ne_top
  have hbound : ∀ ω, weightedGmcBallMass γ (M ω) α z r ≤ c * M ω (Metric.ball z r) := by
    intro ω
    unfold weightedGmcBallMass
    calc ∫⁻ x in Metric.ball z r, ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) ∂M ω
        ≤ ∫⁻ _x in Metric.ball z r, c ∂M ω := by
          apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
          intro x hx
          rw [Metric.mem_ball, dist_eq_norm] at hx
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx.le) hs
      _ = c * M ω (Metric.ball z r) := setLIntegral_const _ _
  have hmeas : AEMeasurable (fun ω => M ω (Metric.ball z r) ^ p) P :=
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet).pow_const _
  have hfin := gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM (Metric.ball z r)
    Metric.isBounded_ball p hp0.le hp
  calc weightedGmcBallMoment P M γ α z r p
      ≤ ∫⁻ ω, (c * M ω (Metric.ball z r)) ^ p ∂P := by
        apply lintegral_mono
        intro ω
        exact ENNReal.rpow_le_rpow (hbound ω) hp0.le
    _ = c ^ p * gmcMassMoment P M (Metric.ball z r) p := by
        rw [lintegral_congr (fun ω => ENNReal.mul_rpow_of_nonneg c (M ω (Metric.ball z r))
          hp0.le), lintegral_const_mul'' _ hmeas]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0.le hctop) hfin

end DOZZ.Proofs
