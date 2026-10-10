/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.CutPlaneTopology
public import DOZZ.Hypergeom.ODE.DiskContinuation
public import DOZZ.Hypergeom.ODE.SeriesEquation
public import DOZZ.Hypergeom.ODE.UniformCompactDisks

/-! The ordinary Gauss series supplies initial data and a Picard seed disk at `z = 1/2`. -/

@[expose] public section

open Polynomial Set

namespace DOZZ.Proofs

/-- The state `(f, f')` of the ordinary Gauss series. -/
noncomputable def ordinaryHypergeometricState (a b c : ℂ) (z : ℂ) : ℂ × ℂ :=
  (ordinaryHypergeometric a b c z, deriv (ordinaryHypergeometric a b c) z)

private theorem ordinaryHypergeometric_state_hasDerivAt (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometricState a b c)
      (deriv (ordinaryHypergeometric a b c) z,
        deriv (deriv (ordinaryHypergeometric a b c)) z) z := by
  let p : FormalMultilinearSeries ℂ ℂ ℂ := ordinaryHypergeometricSeries ℂ a b c
  have hpPos : 0 < p.radius := ordinaryHypergeometricSeries_radius_pos a b c hc
  have hpLe : (1 : ENNReal) ≤ p.radius := ordinaryHypergeometricSeries_one_le_radius a b c hc
  have hsum : ordinaryHypergeometric a b c = p.sum := by
    funext z
    rw [ordinaryHypergeometric_eq_tsum]
    exact (ordinaryHypergeometric_sum_eq a b c z).symm
  have hseries : HasFPowerSeriesOnBall (ordinaryHypergeometric a b c) p 0 1 := by
    rw [hsum]
    exact p.hasFPowerSeriesOnBall hpPos |>.mono (by norm_num) hpLe
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hz
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hznorm)
  have hfAnalytic := hseries.analyticAt_of_mem hzball
  have hfirst : HasDerivAt (ordinaryHypergeometric a b c)
      (deriv (ordinaryHypergeometric a b c) z) z :=
    hfAnalytic.differentiableAt.hasDerivAt
  let evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hfprimeComp := evalOne.comp_hasFPowerSeriesOnBall hseries.fderiv
  have hfprime_eq : (fun w => evalOne (fderiv ℂ (ordinaryHypergeometric a b c) w)) =
      deriv (ordinaryHypergeometric a b c) := by
    funext w
    exact fderiv_apply_one_eq_deriv
  have hfprime : HasFPowerSeriesOnBall (deriv (ordinaryHypergeometric a b c))
      (evalOne.compFormalMultilinearSeries p.derivSeries) 0 1 := by
    convert hfprimeComp using 1
    exact hfprime_eq
  have hsecond : HasDerivAt (deriv (ordinaryHypergeometric a b c))
      (deriv (deriv (ordinaryHypergeometric a b c)) z) z :=
    hfprime.analyticAt_of_mem hzball |>.differentiableAt.hasDerivAt
  exact hfirst.prodMk hsecond

/-- On the punctured unit disk, the ordinary-series state solves the explicit first-order system. -/
theorem ordinaryHypergeometricState_solves_gaussSystem_on_unitDisk
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometricState a b c)
      (gaussSystemOperator a b c z (ordinaryHypergeometricState a b c z)) z := by
  have hpair := ordinaryHypergeometric_state_hasDerivAt a b c hc hz
  have hsys := ordinaryHypergeometric_state_solves_gaussSystem a b c hc hz0 hz
  exact hpair.congr_deriv (by simpa [ordinaryHypergeometricState] using hsys.symm)

/-- A uniform local Picard disk at `1/2` agrees with the ordinary-series state. This is the
regular-domain initial patch for path continuation from the origin series germ. -/
theorem exists_gauss_ordinary_seed_disk (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∃ r M : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 ≤ M ∧
      ∃ D : HolomorphicDiskSolution (gaussSystemOperator a b c) r,
        D.center = (1 / 2 : ℂ) ∧
        (∀ z ∈ Metric.ball (1 / 2 : ℂ) r,
          ‖gaussSystemOperator a b c z‖ ≤ M) ∧
        ∀ z ∈ Metric.ball (1 / 2 : ℂ) r,
          D.solution z = ordinaryHypergeometricState a b c z := by
  let c₀ : ℂ := 1 / 2
  let H : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ := gaussSystemOperator a b c
  have hc₀ : c₀ ∈ gaussRegularPlane := by
    constructor <;> norm_num [c₀]
  obtain ⟨r₀, M, hr₀, hM, hlocal⟩ :=
    exists_uniform_holomorphic_disks_on_compact
      isCompact_singleton (fun z : ℂ => z) continuousOn_id
      gaussRegularPlane gaussRegularPlane_isOpen H
      (gaussSystemOperator_differentiableOn a b c)
      (by rintro z rfl; exact hc₀)
  have hlocal₀ := hlocal c₀ (by simp)
  let r : ℝ := min r₀ (1 / 4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₀' : r ≤ r₀ := by dsimp [r]; exact min_le_left _ _
  have hrquarter : r ≤ 1 / 4 := by dsimp [r]; exact min_le_right _ _
  have hH : DifferentiableOn ℂ H (Metric.ball c₀ r) :=
    hlocal₀.1.mono (Metric.ball_subset_ball hr₀')
  have hbound : ∀ z ∈ Metric.ball c₀ r, ‖H z‖ ≤ M := by
    intro z hz
    exact hlocal₀.2 z (Metric.ball_subset_ball hr₀' hz)
  let D := holomorphicDiskSolutionOfBound c₀ r M H hH
    (ordinaryHypergeometricState a b c c₀) hM hbound
  have hseriesNorm (z : ℂ) (hz : z ∈ Metric.ball c₀ r) : ‖z‖ < 1 := by
    have hdist : dist z c₀ < r := Metric.mem_ball.mp hz
    have hdistNorm : ‖z - c₀‖ < r := by simpa [dist_eq_norm] using hdist
    have htriangle : ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := by
      calc
        ‖z‖ = ‖(z - c₀) + c₀‖ := by congr 1; abel
        _ ≤ ‖z - c₀‖ + ‖c₀‖ := norm_add_le _ _
    have hc₀norm : ‖c₀‖ = (1 / 2 : ℝ) := by norm_num [c₀]
    calc
      ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := htriangle
      _ < r + 1 / 2 := add_lt_add_of_lt_of_le hdistNorm (le_of_eq hc₀norm)
      _ ≤ 1 / 4 + 1 / 2 := by nlinarith [hrquarter]
      _ < 1 := by norm_num
  have hregular (z : ℂ) (hz : z ∈ Metric.ball c₀ r) : z ≠ 0 := by
    intro hz0
    subst z
    have hdist : dist (0 : ℂ) c₀ < r := Metric.mem_ball.mp hz
    have hc₀dist : dist (0 : ℂ) c₀ = (1 / 2 : ℝ) := by norm_num [c₀, dist_eq_norm]
    rw [hc₀dist] at hdist
    linarith [hrquarter]
  refine ⟨r, M, hr, hrquarter, hM, D, rfl, hbound, ?_⟩
  intro z hz
  apply holomorphic_linear_system_solution_unique_of_eq_at
    c₀ r M H hM hbound
    (fun w hw => D.derivative w hw)
    (fun w hw => ordinaryHypergeometricState_solves_gaussSystem_on_unitDisk
      a b c hc (hregular w hw) (hseriesNorm w hw))
    (Metric.mem_ball_self hr) hz ?_
  change D.solution D.center = ordinaryHypergeometricState a b c c₀
  rw [D.solution_center]
  rfl


/-- A uniform local Picard disk at `-1/2` agrees with the ordinary-series state. This is the
regular-domain initial patch for path continuation from the origin series germ. -/
theorem exists_gauss_ordinary_seed_disk_negative (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∃ r M : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 ≤ M ∧
      ∃ D : HolomorphicDiskSolution (gaussSystemOperator a b c) r,
        D.center = (-1 / 2 : ℂ) ∧
        (∀ z ∈ Metric.ball (-1 / 2 : ℂ) r,
          ‖gaussSystemOperator a b c z‖ ≤ M) ∧
        ∀ z ∈ Metric.ball (-1 / 2 : ℂ) r,
          D.solution z = ordinaryHypergeometricState a b c z := by
  let c₀ : ℂ := -1 / 2
  let H : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ := gaussSystemOperator a b c
  have hc₀ : c₀ ∈ gaussRegularPlane := by
    constructor <;> norm_num [c₀]
  obtain ⟨r₀, M, hr₀, hM, hlocal⟩ :=
    exists_uniform_holomorphic_disks_on_compact
      isCompact_singleton (fun z : ℂ => z) continuousOn_id
      gaussRegularPlane gaussRegularPlane_isOpen H
      (gaussSystemOperator_differentiableOn a b c)
      (by rintro z rfl; exact hc₀)
  have hlocal₀ := hlocal c₀ (by simp)
  let r : ℝ := min r₀ (1 / 4)
  have hr : 0 < r := by dsimp [r]; positivity
  have hr₀' : r ≤ r₀ := by dsimp [r]; exact min_le_left _ _
  have hrquarter : r ≤ 1 / 4 := by dsimp [r]; exact min_le_right _ _
  have hH : DifferentiableOn ℂ H (Metric.ball c₀ r) :=
    hlocal₀.1.mono (Metric.ball_subset_ball hr₀')
  have hbound : ∀ z ∈ Metric.ball c₀ r, ‖H z‖ ≤ M := by
    intro z hz
    exact hlocal₀.2 z (Metric.ball_subset_ball hr₀' hz)
  let D := holomorphicDiskSolutionOfBound c₀ r M H hH
    (ordinaryHypergeometricState a b c c₀) hM hbound
  have hseriesNorm (z : ℂ) (hz : z ∈ Metric.ball c₀ r) : ‖z‖ < 1 := by
    have hdist : dist z c₀ < r := Metric.mem_ball.mp hz
    have hdistNorm : ‖z - c₀‖ < r := by simpa [dist_eq_norm] using hdist
    have htriangle : ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := by
      calc
        ‖z‖ = ‖(z - c₀) + c₀‖ := by congr 1; abel
        _ ≤ ‖z - c₀‖ + ‖c₀‖ := norm_add_le _ _
    have hc₀norm : ‖c₀‖ = (1 / 2 : ℝ) := by norm_num [c₀]
    calc
      ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := htriangle
      _ < r + 1 / 2 := add_lt_add_of_lt_of_le hdistNorm (le_of_eq hc₀norm)
      _ ≤ 1 / 4 + 1 / 2 := by nlinarith [hrquarter]
      _ < 1 := by norm_num
  have hregular (z : ℂ) (hz : z ∈ Metric.ball c₀ r) : z ≠ 0 := by
    intro hz0
    subst z
    have hdist : dist (0 : ℂ) c₀ < r := Metric.mem_ball.mp hz
    have hc₀dist : dist (0 : ℂ) c₀ = (1 / 2 : ℝ) := by norm_num [c₀, dist_eq_norm]
    rw [hc₀dist] at hdist
    linarith [hrquarter]
  refine ⟨r, M, hr, hrquarter, hM, D, rfl, hbound, ?_⟩
  intro z hz
  apply holomorphic_linear_system_solution_unique_of_eq_at
    c₀ r M H hM hbound
    (fun w hw => D.derivative w hw)
    (fun w hw => ordinaryHypergeometricState_solves_gaussSystem_on_unitDisk
      a b c hc (hregular w hw) (hseriesNorm w hw))
    (Metric.mem_ball_self hr) hz ?_
  change D.solution D.center = ordinaryHypergeometricState a b c c₀
  rw [D.solution_center]
  rfl

end DOZZ.Proofs
