/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedScale
public import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency

/-! # Divergence of weighted moments at the insertion threshold, at the chart center

At the center `0` of the logarithmic chart the weighted local moment obeys the exact scaling law
`gmc_weighted_ball_moment_scale`. If the scaling exponent is nonpositive, the moment on the
half-radius disk dominates the moment on the full disk, whereas the monotonicity of the weighted
mass in the radius gives the reverse inequality. The two are compatible only if the moment is
infinite: a small disk inside the annulus `{R / 2 < |x| < R}` has almost surely positive mass, and
the weight there is bounded below, so the weighted mass of the full disk almost surely exceeds
that of the half-radius disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Points of the disk of radius `R / 4` about `3R / 4` lie in the annulus `R / 2 < |x| < R`. -/
theorem centerInsertion_annulus_norm_bounds {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : x ∈ Metric.ball (((3 * R / 4 : ℝ)) : ℂ) (R / 4)) :
    R / 2 < ‖x‖ ∧ ‖x‖ < R := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hc : ‖(((3 * R / 4 : ℝ)) : ℂ)‖ = 3 * R / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖x‖ ≤ ‖x - (((3 * R / 4 : ℝ)) : ℂ)‖ + ‖(((3 * R / 4 : ℝ)) : ℂ)‖ := by
    simpa using norm_add_le (x - (((3 * R / 4 : ℝ)) : ℂ)) (((3 * R / 4 : ℝ)) : ℂ)
  have h2 : ‖(((3 * R / 4 : ℝ)) : ℂ)‖ ≤ ‖x - (((3 * R / 4 : ℝ)) : ℂ)‖ + ‖x‖ := by
    have := norm_sub_le x (x - (((3 * R / 4 : ℝ)) : ℂ))
    rw [sub_sub_cancel] at this
    linarith
  rw [hc] at h1 h2
  constructor <;> linarith

/-- The weighted mass of the half-radius disk plus the weighted mass of a disk inside the annulus,
the latter against the lower bound `R ^ (-γα)` of the weight, is at most the weighted mass of the
full disk. -/
theorem centerInsertion_mass_add_le (μ : Measure ℂ) (γ α : ℝ) (hγα : 0 < γ * α) {R : ℝ}
    (hR : 0 < R) :
    weightedGmcBallMass γ μ α 0 ((1 / 2) * R) +
        ENNReal.rpow (ENNReal.ofReal R) (-γ * α) *
          μ (Metric.ball (((3 * R / 4 : ℝ)) : ℂ) (R / 4)) ≤
      weightedGmcBallMass γ μ α 0 R := by
  set B : Set ℂ := Metric.ball (((3 * R / 4 : ℝ)) : ℂ) (R / 4) with hB
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hdisj : Disjoint (Metric.ball (0 : ℂ) ((1 / 2) * R)) B := by
    rw [Set.disjoint_left]
    intro x hx hxB
    rw [Metric.mem_ball, dist_zero_right] at hx
    have := (centerInsertion_annulus_norm_bounds hR hxB).1
    linarith
  have hsub : Metric.ball (0 : ℂ) ((1 / 2) * R) ∪ B ⊆ Metric.ball (0 : ℂ) R := by
    refine Set.union_subset (Metric.ball_subset_ball (by linarith)) ?_
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact (centerInsertion_annulus_norm_bounds hR hx).2
  have hs : -γ * α ≤ 0 := by
    rw [neg_mul]
    exact neg_nonpos.mpr hγα.le
  unfold weightedGmcBallMass
  calc ∫⁻ x in Metric.ball (0 : ℂ) ((1 / 2) * R),
          ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * α) ∂μ +
          ENNReal.rpow (ENNReal.ofReal R) (-γ * α) * μ B
      ≤ ∫⁻ x in Metric.ball (0 : ℂ) ((1 / 2) * R),
          ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * α) ∂μ +
          ∫⁻ x in B, ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * α) ∂μ := by
        gcongr
        calc ENNReal.rpow (ENNReal.ofReal R) (-γ * α) * μ B
            = ∫⁻ _x in B, ENNReal.rpow (ENNReal.ofReal R) (-γ * α) ∂μ :=
              (setLIntegral_const _ _).symm
          _ ≤ ∫⁻ x in B, ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * α) ∂μ := by
              apply setLIntegral_mono' hBm
              intro x hx
              rw [sub_zero]
              exact ennreal_rpow_antitone_of_nonpos
                (ENNReal.ofReal_le_ofReal (centerInsertion_annulus_norm_bounds hR hx).2.le) hs
    _ = ∫⁻ x in Metric.ball (0 : ℂ) ((1 / 2) * R) ∪ B,
          ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * α) ∂μ :=
        (lintegral_union hBm hdisj).symm
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) R, ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * α) ∂μ :=
        lintegral_mono_set hsub

/-- The weighted mass about the center is monotone in the radius. -/
theorem centerInsertion_mass_mono (μ : Measure ℂ) (γ α : ℝ) {r s : ℝ} (h : r ≤ s) :
    weightedGmcBallMass γ μ α 0 r ≤ weightedGmcBallMass γ μ α 0 s :=
  lintegral_mono_set (Metric.ball_subset_ball h)

/-- At and below the insertion threshold the weighted moment about the chart center diverges. -/
theorem weightedGmcBallMoment_center_eq_top_of_insertion
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : ℝ) (hα : 0 < α) (p : ℝ) (hp : 0 < p)
    (he : (2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 ≤ 0)
    (R : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    weightedGmcBallMoment P M γ α 0 R p = ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  by_contra hne
  have hI : weightedGmcBallMoment P M γ α 0 R p < ⊤ := lt_top_iff_ne_top.mpr hne
  -- scaling by `1 / 2` with a nonpositive exponent can only increase the moment
  have hscale := gmc_weighted_ball_moment_scale P X hX γ M hM α (c := 1 / 2) (R := R)
    (by norm_num) (by norm_num) hR hR1 p
  have hone : (1 : ℝ) ≤ (1 / 2 : ℝ) ^
      ((2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) he
  have hge : weightedGmcBallMoment P M γ α 0 R p ≤
      weightedGmcBallMoment P M γ α 0 ((1 / 2) * R) p := by
    rw [hscale]
    calc weightedGmcBallMoment P M γ α 0 R p = 1 * weightedGmcBallMoment P M γ α 0 R p :=
          (one_mul _).symm
      _ ≤ _ := by gcongr; exact ENNReal.one_le_ofReal.mpr hone
  -- monotonicity in the radius gives the reverse inequality
  have hle : weightedGmcBallMoment P M γ α 0 ((1 / 2) * R) p ≤
      weightedGmcBallMoment P M γ α 0 R p :=
    lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (centerInsertion_mass_mono (M ω) γ α (by linarith)) hp.le
  have hIhalf : weightedGmcBallMoment P M γ α 0 ((1 / 2) * R) p < ⊤ := lt_of_le_of_lt hle hI
  -- the half-radius mass is almost surely finite
  have hWhalf := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM α 0 ((1 / 2) * R)
  have hWfull := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM α 0 R
  have hfin : ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) α 0 ((1 / 2) * R) < ⊤ := by
    filter_upwards [ae_lt_top' (hWhalf.pow_const p) hIhalf.ne] with ω hω
    by_contra hcon
    have htop : weightedGmcBallMass γ (M ω) α 0 ((1 / 2) * R) = ⊤ := not_lt_top_iff.mp hcon
    rw [htop, ENNReal.top_rpow_of_pos hp] at hω
    exact lt_irrefl _ hω
  -- the annulus ball has almost surely positive mass
  have hpos := gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM (((3 * R / 4 : ℝ)) : ℂ) (R / 4)
    (by positivity)
  have hc0 : 0 < ENNReal.rpow (ENNReal.ofReal R) (-γ * α) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hR) ENNReal.ofReal_ne_top
  have hlt : ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) α 0 ((1 / 2) * R) ^ p <
      weightedGmcBallMass γ (M ω) α 0 R ^ p := by
    filter_upwards [hfin, hpos] with ω hω1 hω2
    exact ENNReal.rpow_lt_rpow (lt_of_lt_of_le
      (ENNReal.lt_add_right hω1.ne (mul_ne_zero hc0.ne' hω2.ne'))
      (centerInsertion_mass_add_le (M ω) γ α (mul_pos hγ hα) hR)) hp
  have hstrict : weightedGmcBallMoment P M γ α 0 ((1 / 2) * R) p <
      weightedGmcBallMoment P M γ α 0 R p :=
    lintegral_strict_mono (NeZero.ne P) (hWfull.pow_const p) hIhalf.ne hlt
  exact absurd hge (not_le.mpr hstrict)

end DOZZ.Proofs
