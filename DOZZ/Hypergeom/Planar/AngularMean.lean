/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Angular means for the first- and second-order Taylor counterterms. -/

@[expose] public section

open MeasureTheory intervalIntegral

namespace DOZZ.Proofs

/-- The real first Fourier mode has zero mean over a full turn. -/
theorem planar_taylor_linear_trig_mean (z : ℂ) :
    ∫ θ in (-Real.pi)..Real.pi, z.re * Real.cos θ + z.im * Real.sin θ = 0 := by
  have hcos : ∫ θ in (-Real.pi)..Real.pi, Real.cos θ = 0 := by
    calc
      ∫ θ in (-Real.pi)..Real.pi, Real.cos θ =
          Real.sin Real.pi - Real.sin (-Real.pi) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun θ _ => Real.hasDerivAt_sin θ) Real.continuousOn_cos.intervalIntegrable
      _ = 0 := by simp
  have hsin : ∫ θ in (-Real.pi)..Real.pi, Real.sin θ = 0 := by
    calc
      ∫ θ in (-Real.pi)..Real.pi, Real.sin θ =
          -Real.cos Real.pi - (-Real.cos (-Real.pi)) :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun θ _ => by simpa using (Real.hasDerivAt_cos θ).neg)
          (by simp)
      _ = 0 := by simp
  calc
    ∫ θ in (-Real.pi)..Real.pi, z.re * Real.cos θ + z.im * Real.sin θ =
        z.re * (∫ θ in (-Real.pi)..Real.pi, Real.cos θ) +
          z.im * (∫ θ in (-Real.pi)..Real.pi, Real.sin θ) := by
            rw [intervalIntegral.integral_add
              (Real.continuousOn_cos.intervalIntegrable.const_mul z.re)
              (Real.continuousOn_sin.intervalIntegrable.const_mul z.im),
              intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ = 0 := by rw [hcos, hsin]; ring


/-- The square of the first Fourier mode has mean `π ‖z‖²` over one full turn. -/
theorem planar_taylor_linear_angular_sq_mean (z : ℂ) :
    ∫ θ in (-Real.pi)..Real.pi,
      (z * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).re ^ 2 =
        Real.pi * ‖z‖ ^ 2 := by
  have hexp (θ : ℝ) : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) =
      (Real.cos θ : ℂ) - Real.sin θ * Complex.I := by
    rw [Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.ofReal_neg, Real.cos_neg, Real.sin_neg]
    ring
  have hfun : (fun θ : ℝ =>
      (z * Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)).re ^ 2) =
      fun θ => (z.re * Real.cos θ + z.im * Real.sin θ) ^ 2 := by
    funext θ
    rw [hexp]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, zero_sub, add_zero]
    ring
  have hcos : ∫ θ in (-Real.pi)..Real.pi, Real.cos θ ^ 2 = Real.pi := by
    rw [integral_cos_sq]
    simp
  have hsin : ∫ θ in (-Real.pi)..Real.pi, Real.sin θ ^ 2 = Real.pi := by
    rw [integral_sin_sq]
    simp
  have hcross : ∫ θ in (-Real.pi)..Real.pi, Real.sin θ * Real.cos θ = 0 := by
    rw [integral_sin_mul_cos₁]
    simp
  rw [hfun]
  calc
    ∫ θ in (-Real.pi)..Real.pi, (z.re * Real.cos θ + z.im * Real.sin θ) ^ 2 =
        z.re ^ 2 * (∫ θ in (-Real.pi)..Real.pi, Real.cos θ ^ 2) +
          ((2 * z.re * z.im) * (∫ θ in (-Real.pi)..Real.pi,
            Real.sin θ * Real.cos θ) +
            z.im ^ 2 * (∫ θ in (-Real.pi)..Real.pi, Real.sin θ ^ 2)) := by
            have hi1 : IntervalIntegrable
                (fun θ : ℝ => z.re ^ 2 * Real.cos θ ^ 2) volume (-Real.pi) Real.pi :=
              (Real.continuousOn_cos.pow 2).const_mul _ |>.intervalIntegrable
            have hi2 : IntervalIntegrable
                (fun θ : ℝ => (2 * z.re * z.im) * (Real.sin θ * Real.cos θ))
                volume (-Real.pi) Real.pi :=
              (Real.continuousOn_sin.mul Real.continuousOn_cos).const_mul _ |>.intervalIntegrable
            have hi3 : IntervalIntegrable
                (fun θ : ℝ => z.im ^ 2 * Real.sin θ ^ 2) volume (-Real.pi) Real.pi :=
              (Real.continuousOn_sin.pow 2).const_mul _ |>.intervalIntegrable
            calc
              _ = ∫ θ in (-Real.pi)..Real.pi,
                    z.re ^ 2 * Real.cos θ ^ 2 +
                      ((2 * z.re * z.im) * (Real.sin θ * Real.cos θ) +
                        z.im ^ 2 * Real.sin θ ^ 2) := by
                        apply intervalIntegral.integral_congr
                        intro θ hθ
                        ring
              _ = (z.re ^ 2 * (∫ θ in (-Real.pi)..Real.pi, Real.cos θ ^ 2)) +
                    ((2 * z.re * z.im) *
                      (∫ θ in (-Real.pi)..Real.pi, Real.sin θ * Real.cos θ) +
                      z.im ^ 2 * (∫ θ in (-Real.pi)..Real.pi, Real.sin θ ^ 2)) := by
                        rw [intervalIntegral.integral_add hi1 (hi2.add hi3),
                          intervalIntegral.integral_add hi2 hi3,
                          intervalIntegral.integral_const_mul,
                          intervalIntegral.integral_const_mul,
                          intervalIntegral.integral_const_mul]
    _ = Real.pi * ‖z‖ ^ 2 := by
      rw [hcos, hsin, hcross]
      simp [Complex.sq_norm, Complex.normSq_apply]
      ring


end DOZZ.Proofs
