/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneHolomorphic
public import DOZZ.Hypergeom.ODE.SeriesEquation
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Convex.PathConnected

/-! Agreement of path-independent Gauss continuations with the ordinary series. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

/-- The selected continuation at `1/2` has its prescribed ordinary-series initial value. -/
theorem gaussCutPlaneContinuationState_midpoint_eq_seriesState
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint =
      ordinaryHypergeometricState a b c (1 / 2 : ℂ) := by
  obtain ⟨r, M, hr, _, hM, D, hcenter, hbound, hseries⟩ :=
    exists_gauss_ordinary_seed_disk a b c hc
  let y := ordinaryHypergeometricState a b c (1 / 2 : ℂ)
  have hcenter' : D.center = (gaussCutPlaneMidpoint : ℂ) := by
    simpa [gaussCutPlaneMidpoint] using hcenter
  have hinitial : D.initial = y := by
    calc
      D.initial = D.solution D.center := D.solution_center.symm
      _ = D.solution (gaussCutPlaneMidpoint : ℂ) := by rw [hcenter']
      _ = y := hseries _ (Metric.mem_ball_self hr)
  let Q₀ := constant_path_continuation_lift
    (gaussCutPlaneMidpoint : ℂ) r M hr hM D hcenter' hbound hinitial
  have hrefl : ∀ t ∈ Icc (0 : ℝ) 1,
      gaussCutPlanePathFunction (Path.refl gaussCutPlaneMidpoint) t =
        (gaussCutPlaneMidpoint : ℂ) := by
    intro t ht
    change ((Path.refl gaussCutPlaneMidpoint)
      (Set.projIcc 0 1 zero_le_one t) : ℂ) = _
    rfl
  let Q := path_continuation_lift_congr Q₀ hrefl
  let A := gaussCutPlaneCanonicalContinuationLift a b c gaussCutPlaneMidpoint
  have hendpoint := gauss_cut_plane_path_lifts_endpoint_eq a b c
    (gaussCutPlaneCanonicalPath gaussCutPlaneMidpoint)
    (Path.refl gaussCutPlaneMidpoint) y A Q
  change (gaussCutPlaneCanonicalContinuationLift a b c gaussCutPlaneMidpoint).value 1 = y
  calc
    (gaussCutPlaneCanonicalContinuationLift a b c gaussCutPlaneMidpoint).value 1 =
        A.value 1 := rfl
    _ = Q.value 1 := hendpoint
    _ = y := rfl

/-- Near `1/2`, the cut-plane endpoint's scalar component is the ordinary Gauss series. -/
theorem gaussCutPlaneScalarState_eq_ordinary_eventually
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    gaussCutPlaneScalarState a b c =ᶠ[𝓝 (gaussCutPlaneMidpoint : ℂ)]
      ordinaryHypergeometric a b c := by
  obtain ⟨r₀, M₀, hr₀, _, hM₀, D₀, hD₀center, hD₀bound, hD₀series⟩ :=
    exists_gauss_ordinary_seed_disk a b c hc
  obtain ⟨R, δ, hR, hδ, hδR, D, hDcenter, hlocal⟩ :=
    gaussCutPlaneContinuationState_locally_eq_picard a b c gaussCutPlaneMidpoint
  have hcenter : (gaussCutPlaneMidpoint : ℂ) = (1 / 2 : ℂ) := by
    rfl
  have hD₀center' : D₀.center = (gaussCutPlaneMidpoint : ℂ) := by
    calc
      D₀.center = (1 / 2 : ℂ) := hD₀center
      _ = (gaussCutPlaneMidpoint : ℂ) := hcenter.symm
  let y := ordinaryHypergeometricState a b c (1 / 2 : ℂ)
  have hstateMid :
      gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint = y := by
    exact gaussCutPlaneContinuationState_midpoint_eq_seriesState a b c hc
  have hDmid : D.solution (gaussCutPlaneMidpoint : ℂ) = y := by
    calc
      D.solution (gaussCutPlaneMidpoint : ℂ) =
          gaussCutPlaneContinuationState a b c gaussCutPlaneMidpoint := by
            symm
            exact hlocal gaussCutPlaneMidpoint (by simp [dist_self, hδ])
      _ = y := hstateMid
  have hD₀mid : D₀.solution (gaussCutPlaneMidpoint : ℂ) = y := by
    have hmidball : (gaussCutPlaneMidpoint : ℂ) ∈
        Metric.ball (1 / 2 : ℂ) r₀ := by
      rw [hcenter]
      exact Metric.mem_ball_self hr₀
    calc
      D₀.solution (gaussCutPlaneMidpoint : ℂ) =
          ordinaryHypergeometricState a b c (1 / 2 : ℂ) := by
            exact hD₀series (gaussCutPlaneMidpoint : ℂ) hmidball
      _ = y := rfl
  let H : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ := gaussSystemOperator a b c
  have hbaseRegular : (gaussCutPlaneMidpoint : ℂ) ∈ gaussRegularPlane :=
    gaussCutPlane_subset_regularPlane gaussCutPlaneMidpoint.property
  obtain ⟨rU, MU, hrU, hMU, hlocalU⟩ :=
    exists_uniform_holomorphic_disks_on_compact
      isCompact_singleton (fun z : ℂ => z) continuousOn_id
      gaussRegularPlane gaussRegularPlane_isOpen H
      (gaussSystemOperator_differentiableOn a b c)
      (by rintro z rfl; exact hbaseRegular)
  have hlocalUbase := hlocalU (gaussCutPlaneMidpoint : ℂ) (by simp)
  let ρ := min δ (min r₀ rU)
  have hρ : 0 < ρ := lt_min hδ (lt_min hr₀ hrU)
  have hρδ : ρ ≤ δ := min_le_left _ _
  have hρr₀ : ρ ≤ r₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρrU : ρ ≤ rU := le_trans (min_le_right _ _) (min_le_right _ _)
  have hρR : ρ ≤ R := by linarith [hρδ, hδR]
  have hballD : Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ ⊆ Metric.ball D.center R := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    rw [hDcenter]
    exact lt_of_lt_of_le hz hρR
  have hballD₀ : Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ ⊆
      Metric.ball D₀.center r₀ := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    rw [hD₀center']
    exact lt_of_lt_of_le hz hρr₀
  have hboundρ : ∀ z ∈ Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ,
      ‖H z‖ ≤ MU := by
    intro z hz
    exact hlocalUbase.2 z (Metric.ball_subset_ball hρrU hz)
  have hDunique : ∀ z ∈ Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ,
      D.solution z = D₀.solution z := by
    intro z hz
    exact holomorphic_linear_system_solution_unique_of_eq_at
      (gaussCutPlaneMidpoint : ℂ) ρ MU H hMU hboundρ
      (fun u hu => D.derivative u (hballD hu))
      (fun u hu => D₀.derivative u (hballD₀ hu))
      (Metric.mem_ball_self hρ) hz (hDmid.trans hD₀mid.symm)
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (gaussCutPlane_isOpen.mem_nhds gaussCutPlaneMidpoint.property)
  let σ := min ρ ε
  have hσ : 0 < σ := lt_min hρ hε
  have hσρ : σ ≤ ρ := min_le_left _ _
  have hσε : σ ≤ ε := min_le_right _ _
  have hnear : gaussCutPlaneScalarState a b c =ᶠ[𝓝 (gaussCutPlaneMidpoint : ℂ)]
      ordinaryHypergeometric a b c := by
    filter_upwards [Metric.ball_mem_nhds (gaussCutPlaneMidpoint : ℂ) hσ]
      with z hz
    have hzcut : z ∈ gaussCutPlane :=
      hεball (Metric.ball_subset_ball hσε hz)
    let w : gaussCutPlane := ⟨z, hzcut⟩
    have hzδ : dist (w : ℂ) (gaussCutPlaneMidpoint : ℂ) < δ := by
      exact lt_of_lt_of_le (Metric.mem_ball.mp hz) (le_trans hσρ hρδ)
    have hstate := hlocal w hzδ
    have hzρ : z ∈ Metric.ball (gaussCutPlaneMidpoint : ℂ) ρ :=
      Metric.ball_subset_ball hσρ hz
    have hpatch := hDunique z hzρ
    have hzseed : z ∈ Metric.ball (1 / 2 : ℂ) r₀ := by
      simpa [hD₀center] using hballD₀ hzρ
    dsimp [gaussCutPlaneScalarState]
    rw [dite_eq_left hzcut]
    calc
      (gaussCutPlaneContinuationState a b c w).1 = (D.solution z).1 :=
        congrArg Prod.fst hstate
      _ = (D₀.solution z).1 := congrArg Prod.fst hpatch
      _ = (ordinaryHypergeometricState a b c z).1 := congrArg Prod.fst (hD₀series z hzseed)
      _ = ordinaryHypergeometric a b c z := rfl
  exact hnear

/-- On the cut plane, the endpoint continuation recovers the ordinary series throughout the unit
disk. -/
theorem gaussCutPlaneScalarState_eq_ordinary_on_unitDisk
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ))
    {z : ℂ} (hz : z ∈ gaussCutPlane) (hznorm : ‖z‖ < 1) :
    gaussCutPlaneScalarState a b c z = ordinaryHypergeometric a b c z := by
  let V := gaussCutPlane ∩ Metric.ball (0 : ℂ) 1
  have hbaseBall : (gaussCutPlaneMidpoint : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    change dist (1 / 2 : ℂ) 0 < 1
    norm_num [dist_eq_norm]
  have hballStar : StarConvex ℝ (gaussCutPlaneMidpoint : ℂ)
      (Metric.ball (0 : ℂ) 1) :=
    (convex_ball (0 : ℂ) 1).starConvex hbaseBall
  have hVstar : StarConvex ℝ (gaussCutPlaneMidpoint : ℂ) V :=
    gaussCutPlane_starConvex.inter hballStar
  have hbaseV : (gaussCutPlaneMidpoint : ℂ) ∈ V :=
    ⟨gaussCutPlaneMidpoint.property, hbaseBall⟩
  have hVpre : IsPreconnected V :=
    (hVstar.isPathConnected hbaseV).isConnected.isPreconnected
  have hFanalytic : AnalyticOnNhd ℂ (gaussCutPlaneScalarState a b c) gaussCutPlane :=
    (gaussCutPlaneScalarState_differentiableOn a b c).analyticOnNhd gaussCutPlane_isOpen
  have hseriesAnalytic : AnalyticOnNhd ℂ (ordinaryHypergeometric a b c)
      (Metric.ball (0 : ℂ) 1) :=
    ordinaryHypergeometric_analyticOnNhd_unitDisk a b c hc
  have hFanalyticV : AnalyticOnNhd ℂ (gaussCutPlaneScalarState a b c) V :=
    fun w hw => hFanalytic w hw.1
  have hseriesAnalyticV : AnalyticOnNhd ℂ (ordinaryHypergeometric a b c) V :=
    fun w hw => hseriesAnalytic w hw.2
  have hidentity : EqOn (gaussCutPlaneScalarState a b c)
      (ordinaryHypergeometric a b c) V :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hFanalyticV hseriesAnalyticV hVpre hbaseV
      (gaussCutPlaneScalarState_eq_ordinary_eventually a b c hc)
  have hznorm' : z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hznorm
  exact hidentity ⟨hz, hznorm'⟩

end DOZZ.Proofs
