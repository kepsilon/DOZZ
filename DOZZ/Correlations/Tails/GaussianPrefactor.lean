/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterRegression
public import DOZZ.GFFStructure.HarmonicMoments
public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient

/-! Exact lognormal prefactor moments for the one-insertion tail. The exponent after the
off-center Gaussian integration is the position exponent of `DOZZ.oneInsertionTailCoefficient`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The power moment of a centered Gaussian Wick exponential with a positive amplitude. -/
theorem gaussian_wick_power_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : Ω → ℝ)
    (hU : HasGaussianLaw U P) (hmean : (∫ ω, U ω ∂P) = 0)
    (γ K p : ℝ) (hK : 0 < K) :
    (∫ ω, (K * Real.exp (γ * U ω - γ ^ 2 * variance U P / 2)) ^ p ∂P) =
      K ^ p * Real.exp (γ ^ 2 * variance U P * (p ^ 2 - p) / 2) := by
  have heq : (fun ω =>
      (K * Real.exp (γ * U ω - γ ^ 2 * variance U P / 2)) ^ p) =
      fun ω => (K ^ p * Real.exp (-p * γ ^ 2 * variance U P / 2)) *
        Real.exp ((p * γ) * U ω) := by
    funext ω
    rw [Real.mul_rpow hK.le (Real.exp_pos _).le, ← Real.exp_mul]
    rw [show (γ * U ω - γ ^ 2 * variance U P / 2) * p =
      -p * γ ^ 2 * variance U P / 2 + (p * γ) * U ω by ring, Real.exp_add]
    ring
  rw [heq, integral_const_mul, gaussian_centered_mgf P U hU hmean (p * γ)]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The exponent of the lognormal moment and plane background simplifies to the
simpletail position exponent, using the source value of Q. -/
theorem prefactor_exponent (γ α : ℝ) (hγ : γ ≠ 0) :
    -4 * reflectionExponent γ α +
        γ ^ 2 * ((reflectionExponent γ α) ^ 2 - reflectionExponent γ α) =
      -4 * α * (Q γ - α) := by
  unfold reflectionExponent Q
  field_simp
  ring

/-- The exact coefficient contributed by the Gaussian origin and the plane density.
This isolates the Gaussian integration step of the one-insertion tail argument, without assuming
a tail estimate. -/
theorem offCenter_prefactor_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (N : Ω → ℝ)
    (hN : HasGaussianLaw N P) (hmean : (∫ ω, N ω ∂P) = 0)
    (γ α Fz : ℝ) (hγ : γ ≠ 0) (hFz : 0 < Fz)
    (z : ℂ) (hz : z ≠ 0) (hvar : variance N P = 2 * Real.log ‖z‖) :
    (∫ ω, ((Fz * ‖z‖ ^ (-4 : ℝ)) *
      Real.exp (γ * N ω - γ ^ 2 * variance N P / 2)) ^
        (reflectionExponent γ α) ∂P) =
      ‖z‖ ^ (-4 * α * (Q γ - α)) * Fz ^ (reflectionExponent γ α) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hK : 0 < Fz * ‖z‖ ^ (-4 : ℝ) :=
    mul_pos hFz (Real.rpow_pos_of_pos hn _)
  let p := reflectionExponent γ α
  rw [gaussian_wick_power_moment P N hN hmean γ
    (Fz * ‖z‖ ^ (-4 : ℝ)) p hK, hvar,
    Real.mul_rpow hFz.le (Real.rpow_pos_of_pos hn _).le, ← Real.rpow_mul hn.le]
  rw [Real.rpow_def_of_pos hn, Real.rpow_def_of_pos hn]
  rw [mul_assoc, ← Real.exp_add]
  have he : Real.log ‖z‖ * (-4 * p) + γ ^ 2 * (2 * Real.log ‖z‖) * (p ^ 2 - p) / 2 =
      Real.log ‖z‖ * (-4 * α * (Q γ - α)) := by
    calc
      _ = Real.log ‖z‖ * (-4 * p + γ ^ 2 * (p ^ 2 - p)) := by ring
      _ = _ := by rw [prefactor_exponent γ α hγ]
  rw [he, mul_comm]


end DOZZ.Proofs
