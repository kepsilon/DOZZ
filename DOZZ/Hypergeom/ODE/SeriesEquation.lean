/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesRecurrence
public import DOZZ.Hypergeom.ODE.GaussSystem
public import DOZZ.Hypergeom.Series
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! The ordinary Gauss series satisfies its scalar equation on the unit disk. -/

@[expose] public section

open Polynomial FormalMultilinearSeries

namespace DOZZ.Proofs

/-- The ordinary Gauss power series, viewed as a formal multilinear series. -/
noncomputable def gaussSeriesAtZero (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ a b c

/-- The scalar power series for the derivative of the ordinary Gauss series. -/
noncomputable def gaussFirstDerivativeSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
    (gaussSeriesAtZero a b c).derivSeries

/-- The power series for `z` times the derivative of the ordinary Gauss series. -/
noncomputable def gaussZFirstDerivativeSeries (a b c : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  (gaussSeriesAtZero a b c).derivSeries.unshift 0

/-- The series for `(1-z)` times the derivative, formed by subtraction. -/
noncomputable def gaussOneSubZDerivativeSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  gaussFirstDerivativeSeries a b c - gaussZFirstDerivativeSeries a b c

/-- The power series for `z` times the derivative of `(1-z)f'`. -/
noncomputable def gaussZOneSubZDerivativeDerivativeSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  (gaussOneSubZDerivativeSeries a b c).derivSeries.unshift 0

/-- Formal series for the Gauss differential residual written using the Euler derivative. -/
noncomputable def gaussEquationResidualSeries (a b c : ℂ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  gaussZOneSubZDerivativeDerivativeSeries a b c -
    (a + b) • gaussZFirstDerivativeSeries a b c +
    c • gaussFirstDerivativeSeries a b c -
    (a * b) • gaussSeriesAtZero a b c

private theorem gaussSeriesCoeff_eq (a b c : ℂ) (n : ℕ) :
    (gaussSeriesAtZero a b c).coeff n = ordinaryHypergeometricCoefficient a b c n := by
  change ordinaryHypergeometricSeries ℂ a b c n (fun _ => (1 : ℂ)) = _
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp [ordinaryHypergeometricCoefficient]

private theorem gaussFirstDerivativeSeries_coeff (a b c : ℂ) (n : ℕ) :
    (gaussFirstDerivativeSeries a b c).coeff n =
      (n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
  change ((gaussSeriesAtZero a b c).derivSeries.coeff n) 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  have hp : (gaussSeriesAtZero a b c).coeff (n + 1) =
      ordinaryHypergeometricCoefficient a b c (n + 1) := gaussSeriesCoeff_eq a b c (n + 1)
  rw [hp]
  simp only [nsmul_eq_mul, Nat.cast_succ]

private theorem gaussZFirstDerivativeSeries_coeff_zero (a b c : ℂ) :
    (gaussZFirstDerivativeSeries a b c).coeff 0 = 0 := by
  change ((gaussSeriesAtZero a b c).derivSeries.unshift 0) 0 (fun _ => (1 : ℂ)) = 0
  simp only [FormalMultilinearSeries.unshift]
  simp

private theorem gaussZFirstDerivativeSeries_coeff_succ (a b c : ℂ) (n : ℕ) :
    (gaussZFirstDerivativeSeries a b c).coeff (n + 1) =
      (n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
  change ((gaussSeriesAtZero a b c).derivSeries.coeff n) 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  have hp : (gaussSeriesAtZero a b c).coeff (n + 1) =
      ordinaryHypergeometricCoefficient a b c (n + 1) := gaussSeriesCoeff_eq a b c (n + 1)
  rw [hp]
  simp only [nsmul_eq_mul, Nat.cast_succ]

private theorem gaussZFirstDerivativeSeries_coeff (a b c : ℂ) (n : ℕ) :
    (gaussZFirstDerivativeSeries a b c).coeff n =
      (n : ℂ) * ordinaryHypergeometricCoefficient a b c n := by
  cases n with
  | zero => simp [gaussZFirstDerivativeSeries_coeff_zero]
  | succ n => simpa [Nat.cast_succ] using gaussZFirstDerivativeSeries_coeff_succ a b c n

private theorem gaussOneSubZDerivativeSeries_coeff (a b c : ℂ) (n : ℕ) :
    (gaussOneSubZDerivativeSeries a b c).coeff n =
      ((n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) -
        (n : ℂ) * ordinaryHypergeometricCoefficient a b c n) := by
  change (gaussFirstDerivativeSeries a b c).coeff n -
    (gaussZFirstDerivativeSeries a b c).coeff n = _
  rw [gaussFirstDerivativeSeries_coeff, gaussZFirstDerivativeSeries_coeff]

private theorem gaussZOneSubZDerivativeDerivativeSeries_coeff (a b c : ℂ) (n : ℕ) :
  (gaussZOneSubZDerivativeDerivativeSeries a b c).coeff n =
      (n : ℂ) * (gaussOneSubZDerivativeSeries a b c).coeff n := by
  cases n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul]
      change ((gaussOneSubZDerivativeSeries a b c).derivSeries.unshift 0)
        0 (fun _ => (1 : ℂ)) = 0
      simp only [FormalMultilinearSeries.unshift]
      simp
  | succ n =>
      change ((gaussOneSubZDerivativeSeries a b c).derivSeries.coeff n) 1 = _
      rw [FormalMultilinearSeries.derivSeries_coeff_one]
      simp only [nsmul_eq_mul, Nat.cast_succ]

private theorem gaussSeriesCoeff_add' {p q : FormalMultilinearSeries ℂ ℂ ℂ} (n : ℕ) :
    (p + q).coeff n = p.coeff n + q.coeff n := rfl

private theorem gaussSeriesCoeff_sub' {p q : FormalMultilinearSeries ℂ ℂ ℂ} (n : ℕ) :
    (p - q).coeff n = p.coeff n - q.coeff n := rfl

private theorem gaussSeriesCoeff_smul' (x : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (n : ℕ) : (x • p).coeff n = x • p.coeff n := rfl

private theorem gaussEquationResidualSeries_coeff (a b c : ℂ) (n : ℕ) :
    (gaussEquationResidualSeries a b c).coeff n =
      ((n + 1 : ℂ) * ((n : ℂ) + c) * ordinaryHypergeometricCoefficient a b c (n + 1) -
        ((n : ℂ) + a) * ((n : ℂ) + b) * ordinaryHypergeometricCoefficient a b c n) := by
  rw [gaussEquationResidualSeries, gaussSeriesCoeff_sub', gaussSeriesCoeff_add',
    gaussSeriesCoeff_sub', gaussSeriesCoeff_smul', gaussSeriesCoeff_smul',
    gaussSeriesCoeff_smul', gaussZOneSubZDerivativeDerivativeSeries_coeff,
    gaussOneSubZDerivativeSeries_coeff, gaussZFirstDerivativeSeries_coeff,
    gaussFirstDerivativeSeries_coeff, gaussSeriesCoeff_eq]
  simp only [smul_eq_mul]
  ring

private theorem gaussEquationResidualSeries_eq_zero (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) : gaussEquationResidualSeries a b c = 0 := by
  apply FormalMultilinearSeries.ext
  intro n
  apply FormalMultilinearSeries.coeff_eq_zero.mp
  rw [gaussEquationResidualSeries_coeff]
  exact sub_eq_zero.mpr (ordinaryHypergeometricCoefficient_gauss_recurrence a b c n hc)

private theorem hasFPowerSeriesOnBall_ordinaryHypergeometric (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    HasFPowerSeriesOnBall (ordinaryHypergeometric a b c)
      (gaussSeriesAtZero a b c) 0 1 := by
  let p := gaussSeriesAtZero a b c
  have hpos : 0 < p.radius :=
    ordinaryHypergeometricSeries_radius_pos a b c hc
  have hle : (1 : ENNReal) ≤ p.radius := by
    exact ordinaryHypergeometricSeries_one_le_radius a b c hc
  have hsum : ordinaryHypergeometric a b c = p.sum := by
    funext z
    rw [ordinaryHypergeometric_eq_tsum]
    exact (ordinaryHypergeometric_sum_eq a b c z).symm
  rw [hsum]
  exact p.hasFPowerSeriesOnBall hpos |>.mono (by norm_num) hle

/-- The ordinary Gauss series is analytic throughout its open unit disk when its denominator
parameter avoids nonpositive integers. -/
theorem ordinaryHypergeometric_analyticOnNhd_unitDisk (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (ordinaryHypergeometric a b c) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hzNorm : ‖z‖ < 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hz
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hzNorm
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hznorm)
  exact (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c hc).analyticAt_of_mem hzball

private theorem fderiv_apply_eq_mul_deriv (f : ℂ → ℂ) (z : ℂ) :
    (fderiv ℂ f z) z = z * deriv f z := by
  calc
    (fderiv ℂ f z) z = (fderiv ℂ f z) (z • (1 : ℂ)) := by simp
    _ = z • (fderiv ℂ f z) 1 := by rw [ContinuousLinearMap.map_smul]
    _ = z * deriv f z := by rw [fderiv_apply_one_eq_deriv]; simp [smul_eq_mul]

/-- On the open unit disk, the ordinary series solves the scalar Gauss equation. This is
the origin seed for the first-order continuation system; it includes terminating numerator cases. -/
theorem ordinaryHypergeometric_gaussEquation_on_unitDisk (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ z : ℂ, ‖z‖ < 1 →
      gaussHolomorphicOperator a b c (ordinaryHypergeometric a b c) z = 0 := by
  let f : ℂ → ℂ := ordinaryHypergeometric a b c
  let g : ℂ → ℂ := fun z => deriv f z - z * deriv f z
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric a b c hc
  have hdf := hf.fderiv
  let evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hfprimeComp := evalOne.comp_hasFPowerSeriesOnBall hdf
  have hfprime_eq : (fun z => evalOne (fderiv ℂ f z)) = deriv f := by
    funext z
    exact fderiv_apply_one_eq_deriv
  have hfprime : HasFPowerSeriesOnBall (deriv f)
      (evalOne.compFormalMultilinearSeries (gaussSeriesAtZero a b c).derivSeries) 0 1 := by
    convert hfprimeComp using 1
    exact hfprime_eq
  have hzf : HasFPowerSeriesOnBall (fun z => z * deriv f z)
      (gaussZFirstDerivativeSeries a b c) 0 1 := by
    have h := hdf.unshift (z := (0 : ℂ))
    have heq : (fun z => (0 : ℂ) + (fderiv ℂ f z) (z - 0)) =
        (fun z => z * deriv f z) := by
      funext z
      simp only [zero_add, sub_zero]
      exact fderiv_apply_eq_mul_deriv f z
    have heqOn : Set.EqOn (fun z => (0 : ℂ) + (fderiv ℂ f z) (z - 0))
        (fun z => z * deriv f z) (Metric.eball (0 : ℂ) 1) := fun z _ => congrFun heq z
    simpa [gaussZFirstDerivativeSeries] using h.congr heqOn
  have hg := hfprime.sub hzf
  have hzg : HasFPowerSeriesOnBall (fun z =>
      z * deriv g z) (gaussZOneSubZDerivativeDerivativeSeries a b c) 0 1 := by
    have h := hg.fderiv |>.unshift (z := (0 : ℂ))
    have heq : (fun z => (0 : ℂ) + (fderiv ℂ g z) (z - 0)) =
        (fun z => z * deriv g z) := by
      funext z
      simp only [zero_add, sub_zero]
      exact fderiv_apply_eq_mul_deriv g z
    have heqOn : Set.EqOn (fun z => (0 : ℂ) + (fderiv ℂ g z) (z - 0))
        (fun z => z * deriv g z) (Metric.eball (0 : ℂ) 1) := fun z _ => congrFun heq z
    simpa [gaussZOneSubZDerivativeDerivativeSeries, gaussOneSubZDerivativeSeries,
      gaussFirstDerivativeSeries] using h.congr heqOn
  have hresidual : HasFPowerSeriesOnBall
      (fun z => z * deriv g z - (a + b) • (z * deriv f z) +
        c • deriv f z - (a * b) • f z)
      (gaussEquationResidualSeries a b c) 0 1 := by
    convert (hzg.sub (hzf.const_smul (c := a + b))).add
        (hfprime.const_smul (c := c)) |>.sub (hf.const_smul (c := a * b)) using 1
    rfl
  have hcoeff0 := gaussEquationResidualSeries_eq_zero a b c hc
  intro z hz
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hz
  have hzball : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hznorm)
  have hsum := hresidual.sum hzball
  rw [hcoeff0] at hsum
  have hres : z * deriv g z - (a + b) • (z * deriv f z) +
      c • deriv f z - (a * b) • f z = 0 := by
    simpa [FormalMultilinearSeries.sum] using hsum
  have hfAnalytic := hf.analyticAt_of_mem hzball
  have hfprimeAnalytic := hfprime.analyticAt_of_mem hzball
  have hfprimeDiff : DifferentiableAt ℂ (deriv f) z :=
    hfprimeAnalytic.differentiableAt
  have hprod : HasDerivAt (fun w : ℂ => w * deriv f w)
      (deriv f z + z * deriv (deriv f) z) z := by
    have hprodRaw := (hasDerivAt_id z).mul hfprimeDiff.hasDerivAt
    have hfun : (fun w : ℂ => w * deriv f w) = (fun w : ℂ => w) * deriv f := by
      funext w
      rfl
    simpa only [one_mul, id_def] using
      hprodRaw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => congrFun hfun w)
  have hgdiff : DifferentiableAt ℂ g z := by
    apply DifferentiableAt.sub hfprimeDiff
      (hprod.differentiableAt)
  have hgderiv : deriv g z =
      deriv (deriv f) z - (deriv f z + z * deriv (deriv f) z) := by
    change deriv (deriv f - fun w => w * deriv f w) z = _
    rw [deriv_sub hfprimeDiff hprod.differentiableAt, hprod.deriv]
  have hsystem : gaussHolomorphicOperator a b c f z =
      z * deriv g z - (a + b) * (z * deriv f z) +
        c * deriv f z - (a * b) * f z := by
    rw [hgderiv]
    simp only [gaussHolomorphicOperator]
    ring
  rw [hsystem]
  simpa [smul_eq_mul] using hres

/-- Away from the singular origin, the ordinary-series state `(f, f')` solves the explicit
first-order Gauss system. -/
theorem ordinaryHypergeometric_state_solves_gaussSystem (a b c : ℂ)
    (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    gaussSystemOperator a b c z
        (ordinaryHypergeometric a b c z, deriv (ordinaryHypergeometric a b c) z) =
      (deriv (ordinaryHypergeometric a b c) z,
        deriv (deriv (ordinaryHypergeometric a b c)) z) := by
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hz
  have hsystem :=
    (gaussHolomorphicOperator_eq_zero_iff_system_residual_eq_zero a b c
      (ordinaryHypergeometric a b c) hz0 hz1).mp
      (ordinaryHypergeometric_gaussEquation_on_unitDisk a b c hc z hz)
  rw [gaussSystemOperator_apply, hsystem]

end DOZZ.Proofs
