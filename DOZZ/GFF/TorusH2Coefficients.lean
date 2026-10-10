/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.LocalFourierEstimates
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# DOZZ.GFF.TorusH2Coefficients

The concrete torus H² coefficient sequence of a compactly supported test is square summable.
Parseval is applied to the test and its two second coordinate derivatives; the derivative
Fourier multipliers provide the two quadratic frequency weights.
-/

@[expose] public section

open MeasureTheory
open Set Metric
open scoped InnerProductSpace Topology lp

namespace DOZZ

private noncomputable def unitBoxSecondDerivativeTest (L : ℝ) (f : TestFn) (v : ℂ) : TestFn :=
  unitBoxDirectionalDerivativeTest L (unitBoxDirectionalDerivativeTest L f v) v

private theorem one_le_fourierWeightConstant :
    1 ≤ (2 * Real.pi) ^ 4 := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have h : 1 ≤ 2 * Real.pi := by nlinarith
  nlinarith [sq_nonneg (2 * Real.pi - 1)]

private theorem weighted_complex_coeff_le_derivative_sum
    (k : Fin 2 → ℤ) (c : ℂ) :
    torusSobolevWeight k ^ 2 * ‖c‖ ^ 2 ≤
      3 * (‖c‖ ^ 2 + (k 0 : ℝ) ^ 4 * ‖c‖ ^ 2 +
        (k 1 : ℝ) ^ 4 * ‖c‖ ^ 2) := by
  have h0 : 0 ≤ (k 0 : ℝ) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ (k 1 : ℝ) ^ 2 := sq_nonneg _
  have hc : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
  rw [torusSobolevWeight]
  nlinarith [sq_nonneg ((k 0 : ℝ) ^ 2 - (k 1 : ℝ) ^ 2),
    sq_nonneg (1 - (k 0 : ℝ) ^ 2), sq_nonneg (1 - (k 1 : ℝ) ^ 2)]

/-- The weighted complex Fourier coefficients of a test supported strictly inside the box are
square summable. -/
theorem summable_torusH2_weightedFourierCoeff
    (L R : ℝ) (hL : 0 < L) (hRbox : R + 2 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) :
    Summable (fun k : Fin 2 → ℤ =>
      torusSobolevWeight k ^ 2 *
        ‖UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k‖ ^ 2) := by
  let c : (Fin 2 → ℤ) → ℂ := fun k =>
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k
  let d0 : TestFn := unitBoxSecondDerivativeTest L f 1
  let d1 : TestFn := unitBoxSecondDerivativeTest L f Complex.I
  let c0 : (Fin 2 → ℤ) → ℂ := fun k =>
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L d0) k
  let c1 : (Fin 2 → ℤ) → ℂ := fun k =>
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L d1) k
  have hinner0 (k : Fin 2 → ℤ) :
      (innerSL ℝ) (unitTorusFourierFrequency k) (1 : ℂ) = (k 0 : ℝ) := by
    rw [unitTorusFourierFrequency_innerSL]
    simp
  have hinner1 (k : Fin 2 → ℤ) :
      (innerSL ℝ) (unitTorusFourierFrequency k) Complex.I = (k 1 : ℝ) := by
    rw [unitTorusFourierFrequency_innerSL]
    simp
  have hcoeff0 (k : Fin 2 → ℤ) :
      c0 k = ((2 * Real.pi * Complex.I * (k 0 : ℝ)) ^ 2) * c k := by
    have hh := torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
      L R hL hRbox f hf 1 k
    rw [hinner0] at hh
    simpa [c0, d0, unitBoxSecondDerivativeTest, c] using hh
  have hcoeff1 (k : Fin 2 → ℤ) :
      c1 k = ((2 * Real.pi * Complex.I * (k 1 : ℝ)) ^ 2) * c k := by
    have hh := torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
      L R hL hRbox f hf Complex.I k
    rw [hinner1] at hh
    simpa [c1, d1, unitBoxSecondDerivativeTest, c] using hh
  have hbase : Summable (fun k : Fin 2 → ℤ => ‖c k‖ ^ 2) := by
    exact (UnitAddTorus.hasSum_sq_mFourierCoeff (torusPeriodizationLp L f)).summable
  have hderiv0 : Summable (fun k : Fin 2 → ℤ => ‖c0 k‖ ^ 2) := by
    exact (UnitAddTorus.hasSum_sq_mFourierCoeff (torusPeriodizationLp L d0)).summable
  have hderiv1 : Summable (fun k : Fin 2 → ℤ => ‖c1 k‖ ^ 2) := by
    exact (UnitAddTorus.hasSum_sq_mFourierCoeff (torusPeriodizationLp L d1)).summable
  have hfreq0 : Summable (fun k : Fin 2 → ℤ =>
      (k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (f := fun k => ‖c0 k‖ ^ 2)
      (g := fun k => (k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2)
      (fun k => mul_nonneg (by positivity) (sq_nonneg _)) (fun k => ?_) hderiv0
    · rw [hcoeff0 k]
      have hk4 : |(k 0 : ℝ)| ^ 4 = (k 0 : ℝ) ^ 4 := by
        calc
          |(k 0 : ℝ)| ^ 4 = |(k 0 : ℝ) ^ 4| := by rw [← abs_pow]
          _ = (k 0 : ℝ) ^ 4 := abs_of_nonneg (by positivity)
      have hnormAbs :
          ‖((2 * Real.pi * Complex.I * (k 0 : ℝ)) ^ 2) * c k‖ ^ 2 =
            (2 * Real.pi) ^ 4 * |(k 0 : ℝ)| ^ 4 * ‖c k‖ ^ 2 := by
        simp [Complex.norm_I]
        ring
      have hnorm : ‖((2 * Real.pi * Complex.I * (k 0 : ℝ)) ^ 2) * c k‖ ^ 2 =
          (2 * Real.pi) ^ 4 * (k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2 := by
        rw [hnormAbs, hk4]
      calc
        (k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2 =
            1 * ((k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2) := by ring
        _ ≤ (2 * Real.pi) ^ 4 * ((k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2) :=
          mul_le_mul_of_nonneg_right one_le_fourierWeightConstant
            (mul_nonneg (by positivity) (sq_nonneg _))
        _ = ‖((2 * Real.pi * Complex.I * (k 0 : ℝ)) ^ 2) * c k‖ ^ 2 := by
          rw [hnorm]
          ring
  have hfreq1 : Summable (fun k : Fin 2 → ℤ =>
      (k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2) := by
    refine Summable.of_nonneg_of_le
      (f := fun k => ‖c1 k‖ ^ 2)
      (g := fun k => (k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2)
      (fun k => mul_nonneg (by positivity) (sq_nonneg _)) (fun k => ?_) hderiv1
    · rw [hcoeff1 k]
      have hk4 : |(k 1 : ℝ)| ^ 4 = (k 1 : ℝ) ^ 4 := by
        calc
          |(k 1 : ℝ)| ^ 4 = |(k 1 : ℝ) ^ 4| := by rw [← abs_pow]
          _ = (k 1 : ℝ) ^ 4 := abs_of_nonneg (by positivity)
      have hnormAbs :
          ‖((2 * Real.pi * Complex.I * (k 1 : ℝ)) ^ 2) * c k‖ ^ 2 =
            (2 * Real.pi) ^ 4 * |(k 1 : ℝ)| ^ 4 * ‖c k‖ ^ 2 := by
        simp [Complex.norm_I]
        ring
      have hnorm : ‖((2 * Real.pi * Complex.I * (k 1 : ℝ)) ^ 2) * c k‖ ^ 2 =
          (2 * Real.pi) ^ 4 * (k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2 := by
        rw [hnormAbs, hk4]
      calc
        (k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2 =
            1 * ((k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2) := by ring
        _ ≤ (2 * Real.pi) ^ 4 * ((k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2) :=
          mul_le_mul_of_nonneg_right one_le_fourierWeightConstant
            (mul_nonneg (by positivity) (sq_nonneg _))
        _ = ‖((2 * Real.pi * Complex.I * (k 1 : ℝ)) ^ 2) * c k‖ ^ 2 := by
          rw [hnorm]
          ring
  refine Summable.of_nonneg_of_le
    (f := fun k => 3 * (‖c k‖ ^ 2 + (k 0 : ℝ) ^ 4 * ‖c k‖ ^ 2 +
      (k 1 : ℝ) ^ 4 * ‖c k‖ ^ 2))
    (g := fun k => torusSobolevWeight k ^ 2 * ‖c k‖ ^ 2)
    (fun k => mul_nonneg (by positivity) (sq_nonneg _))
    (fun k => weighted_complex_coeff_le_derivative_sum k (c k)) ?_
  simpa [add_assoc] using (hbase.add (hfreq0.add hfreq1)).mul_left 3


end DOZZ

end
