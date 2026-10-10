/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesEquation
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! Spatial differentiation of the ordinary Gauss series, with its parameter shift. -/

@[expose] public section

open Polynomial FormalMultilinearSeries

namespace DOZZ.Proofs

private theorem ordinaryHypergeometricCoefficient_derivative_shift (a b c : ℂ) (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1)) =
      (a * b / c) * ordinaryHypergeometricCoefficient (a + 1) (b + 1) (c + 1) n := by
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hcShift : ∀ k : ℕ, c + 1 ≠ -(k : ℂ) := by
    intro k h
    apply hc (k + 1)
    have h' : c = -((k + 1 : ℕ) : ℂ) := by
      push_cast at h ⊢
      linear_combination h
    exact h'
  have hcp1 : (ascPochhammer ℂ n).eval (c + 1) ≠ 0 :=
    ordinaryHypergeometric_pochhammer_denominator_ne_zero n hcShift
  have hfact : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ n
  have hfact0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hshift (x : ℂ) :
      (ascPochhammer ℂ (n + 1)).eval x =
        x * (ascPochhammer ℂ n).eval (x + 1) := by
    rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X]
    have heval : ((ascPochhammer ℂ n).comp (X + 1)).eval x =
        (ascPochhammer ℂ n).eval (x + 1) := by
      simp
    exact congrArg (fun y : ℂ => x * y) heval
  simp only [ordinaryHypergeometricCoefficient]
  rw [hfact, hshift a, hshift b, hshift c]
  field_simp [hc0, hcp1, hfact0]

private theorem ordinaryHypergeometricSeries_coeff' (a b c : ℂ) (n : ℕ) :
    (ordinaryHypergeometricSeries ℂ a b c).coeff n =
      ordinaryHypergeometricCoefficient a b c n := by
  change ordinaryHypergeometricSeries ℂ a b c n (fun _ => (1 : ℂ)) = _
  rw [ordinaryHypergeometricSeries_apply_eq]
  simp [ordinaryHypergeometricCoefficient]

private theorem gaussFirstDerivativeSeries_coeff' (a b c : ℂ) (n : ℕ) :
    (gaussFirstDerivativeSeries a b c).coeff n =
      (n + 1 : ℂ) * ordinaryHypergeometricCoefficient a b c (n + 1) := by
  change ((gaussSeriesAtZero a b c).derivSeries.coeff n) 1 = _
  rw [FormalMultilinearSeries.derivSeries_coeff_one]
  have hcoeff : (gaussSeriesAtZero a b c).coeff (n + 1) =
      ordinaryHypergeometricCoefficient a b c (n + 1) := by
    change ordinaryHypergeometricSeries ℂ a b c (n + 1) (fun _ => (1 : ℂ)) = _
    rw [ordinaryHypergeometricSeries_apply_eq]
    simp [ordinaryHypergeometricCoefficient]
  rw [hcoeff]
  simp only [nsmul_eq_mul, Nat.cast_succ]

private theorem formalSeries_coeff_smul' (x : ℂ) (p : FormalMultilinearSeries ℂ ℂ ℂ)
    (n : ℕ) : (x • p).coeff n = x • p.coeff n := rfl

private theorem ordinaryHypergeometricSeries_derivSeries_eq (a b c : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    gaussFirstDerivativeSeries a b c =
      (a * b / c) • ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1) := by
  apply FormalMultilinearSeries.ext
  intro n
  apply ContinuousMultilinearMap.ext_ring
  change (gaussFirstDerivativeSeries a b c).coeff n =
    ((a * b / c) • ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1)).coeff n
  rw [formalSeries_coeff_smul', gaussFirstDerivativeSeries_coeff',
    ordinaryHypergeometricSeries_coeff']
  simp only [smul_eq_mul]
  rw [ordinaryHypergeometricCoefficient_derivative_shift a b c n hc]

/-- At every point of the open unit disk, the spatial derivative is the shifted Gauss series. -/
theorem ordinaryHypergeometric_hasDerivAt_unitDisk (a b c z : ℂ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    HasDerivAt (ordinaryHypergeometric a b c)
      (a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z) z := by
  let S := ordinaryHypergeometricSeries ℂ a b c
  have hrad := ordinaryHypergeometricSeries_one_le_radius a b c hc
  have hznorm : ‖z‖₊ < 1 := by exact_mod_cast hz
  have hz' : z ∈ Metric.eball (0 : ℂ) 1 := by
    simpa [Metric.mem_eball, edist_eq_enorm_sub, enorm_eq_nnnorm, dist_zero_right] using
      (ENNReal.coe_lt_coe.mpr hznorm)
  have hpos : 0 < S.radius := ordinaryHypergeometricSeries_radius_pos a b c hc
  have hle : (1 : ENNReal) ≤ S.radius := by exact_mod_cast hrad
  have hpower : HasFPowerSeriesOnBall (ordinaryHypergeometric a b c) S 0 1 := by
    have hsum : ordinaryHypergeometric a b c = S.sum := rfl
    rw [hsum]
    exact S.hasFPowerSeriesOnBall hpos |>.mono (by norm_num) hle
  have hdf := hpower.fderiv
  let evalOne : (ℂ →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ 1
  have hprimeComp := evalOne.comp_hasFPowerSeriesOnBall hdf
  have hprimeEq : (fun w => evalOne (fderiv ℂ (ordinaryHypergeometric a b c) w)) =
      deriv (ordinaryHypergeometric a b c) := by
    funext w
    exact fderiv_apply_one_eq_deriv
  have hprimeFun : HasFPowerSeriesOnBall
      (fun w => evalOne (fderiv ℂ (ordinaryHypergeometric a b c) w))
      (evalOne.compFormalMultilinearSeries S.derivSeries) 0 1 := hprimeComp
  rw [hprimeEq] at hprimeFun
  have hprime : HasFPowerSeriesOnBall (deriv (ordinaryHypergeometric a b c))
      (gaussFirstDerivativeSeries a b c) 0 1 := by
    simpa [gaussFirstDerivativeSeries, gaussSeriesAtZero, S] using hprimeFun
  have hseriesEq := ordinaryHypergeometricSeries_derivSeries_eq a b c hc
  have hderivValue : deriv (ordinaryHypergeometric a b c) z =
      a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
    calc
      deriv (ordinaryHypergeometric a b c) z =
          (gaussFirstDerivativeSeries a b c).sum z := by simpa using hprime.sum hz'
      _ = ((a * b / c) •
          ordinaryHypergeometricSeries ℂ (a + 1) (b + 1) (c + 1)).sum z := by
        rw [hseriesEq]
      _ = a * b / c * ordinaryHypergeometric (a + 1) (b + 1) (c + 1) z := by
        rw [← FormalMultilinearSeries.const_smul_sum_apply]
        simp only [smul_eq_mul]
        rfl
  have hAt : DifferentiableAt ℂ (ordinaryHypergeometric a b c) z :=
    hpower.analyticAt_of_mem hz' |>.differentiableAt
  have hresult := hAt.hasDerivAt
  rw [hderivValue] at hresult
  exact hresult

end DOZZ.Proofs
