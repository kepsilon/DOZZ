/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.PicardIterates
public import DOZZ.Hypergeom.ODE.SegmentIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Factorial bounds for the local holomorphic Picard summands. -/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace DOZZ.Proofs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The `n`th normalized Picard summand is bounded by the exponential-series majorant.
The factor `‖y‖` allows arbitrary initial vectors; for a fundamental-matrix column it is one.
-/
theorem holomorphicPicardIterates_norm_le (c : ℂ) (r M : ℝ)
    (H : ℂ → E →L[ℂ] E) (hH : DifferentiableOn ℂ H (Metric.ball c r)) (y : E)
    (hM : 0 ≤ M) (hHbound : ∀ z ∈ Metric.ball c r, ‖H z‖ ≤ M) :
    ∀ n : ℕ, ∀ z ∈ Metric.ball c r,
      ‖(holomorphicPicardIterates c r H hH y n).1 z‖ ≤
        ‖y‖ * (M * ‖z - c‖) ^ n / (n.factorial : ℝ) := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  intro n
  induction n with
  | zero =>
      intro z hz
      simp [holomorphicPicardIterates]
  | succ n ih =>
      intro z hz
      have hd : ‖z - c‖ < r := by simpa [dist_eq_norm] using (Metric.mem_ball.mp hz)
      have hc : c ∈ Metric.ball c r := Metric.mem_ball_self (lt_of_le_of_lt (norm_nonneg _) hd)
      have hseg : MapsTo (AffineMap.lineMap c z) (Icc (0 : ℝ) 1) (Metric.ball c r) :=
        (convex_ball c r).mapsTo_lineMap hc hz
      let integrand : ℂ → E := fun w => H w ((holomorphicPicardIterates c r H hH y n).1 w)
      have hintegrand : DifferentiableOn ℂ integrand (Metric.ball c r) :=
        hH.clm_apply (holomorphicPicardIterates c r H hH y n).2
      have hterm : (holomorphicPicardIterates c r H hH y (n + 1)).1 z =
          ∫ t in (0 : ℝ)..1,
            (z - c) • integrand (AffineMap.lineMap c z t) := by
        have hprimitive := normalizedDiskPrimitive_sub_center_eq_segmentIntegral
          (y := (0 : E)) hintegrand hz
        simpa [holomorphicPicardIterates, integrand] using hprimitive
      let d : ℝ := ‖z - c‖
      let C : ℝ := ‖y‖ * (M * d) ^ (n + 1) / (n.factorial : ℝ)
      have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
          ‖(z - c) • integrand (AffineMap.lineMap c z t)‖ ≤ C * t ^ n := by
        intro t ht
        let w : ℂ := AffineMap.lineMap c z t
        have hw : w ∈ Metric.ball c r := hseg ht
        have hdelta : w - c = t • (z - c) := by
          dsimp [w]
          rw [AffineMap.lineMap_apply_module']
          abel
        have hnormDelta : ‖w - c‖ = t * d := by
          rw [hdelta, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        have hprev := ih w hw
        have hprev' : ‖(holomorphicPicardIterates c r H hH y n).1 w‖ ≤
            ‖y‖ * (M * (t * d)) ^ n / (n.factorial : ℝ) := by
          simpa [hnormDelta] using hprev
        have hOp := (H w).le_opNorm ((holomorphicPicardIterates c r H hH y n).1 w)
        have hHnorm : ‖H w‖ ≤ M := hHbound w hw
        have hpow : (M * (t * d)) ^ n = t ^ n * (M * d) ^ n := by
          rw [show M * (t * d) = t * (M * d) by ring, mul_pow]
        dsimp [integrand, C, d]
        rw [norm_smul]
        calc
          ‖z - c‖ * ‖H w ((holomorphicPicardIterates c r H hH y n).1 w)‖ ≤
              ‖z - c‖ * (M * ‖(holomorphicPicardIterates c r H hH y n).1 w‖) :=
            mul_le_mul_of_nonneg_left
              (hOp.trans (mul_le_mul_of_nonneg_right hHnorm (norm_nonneg _))) (norm_nonneg _)
          _ ≤ ‖z - c‖ * (M *
              (‖y‖ * (M * (t * ‖z - c‖)) ^ n / (n.factorial : ℝ))) := by
            gcongr
          _ = ‖y‖ * (M * ‖z - c‖) ^ (n + 1) / (n.factorial : ℝ) * t ^ n := by
            rw [hpow]
            ring
      have hsourceCont : ContinuousOn
          (fun t : ℝ => (z - c) • integrand (AffineMap.lineMap c z t)) (Icc 0 1) := by
        exact continuousOn_const.smul
          (hintegrand.continuousOn.comp AffineMap.lineMap_continuous.continuousOn hseg)
      have hnormInt : IntervalIntegrable
          (fun t : ℝ => ‖(z - c) • integrand (AffineMap.lineMap c z t)‖) volume 0 1 :=
        hsourceCont.norm.intervalIntegrable_of_Icc zero_le_one
      have hmajorCont : ContinuousOn (fun t : ℝ => C * t ^ n) (Icc 0 1) := by fun_prop
      have hmajorInt : IntervalIntegrable (fun t : ℝ => C * t ^ n) volume 0 1 :=
        hmajorCont.intervalIntegrable_of_Icc zero_le_one
      have hmono := intervalIntegral.integral_mono_on
        (hab := (by norm_num : (0 : ℝ) ≤ 1)) (hf := hnormInt) (hg := hmajorInt) hpoint
      have hnorm := intervalIntegral.norm_integral_le_integral_norm
        (μ := volume) (f := fun t : ℝ => (z - c) • integrand (AffineMap.lineMap c z t))
        (by norm_num : (0 : ℝ) ≤ 1)
      have hintegral :
          ‖∫ t in (0 : ℝ)..1, (z - c) • integrand (AffineMap.lineMap c z t)‖ ≤
            C / (n + 1) := by
        calc
          _ ≤ ∫ t in (0 : ℝ)..1,
                ‖(z - c) • integrand (AffineMap.lineMap c z t)‖ := hnorm
          _ ≤ ∫ t in (0 : ℝ)..1, C * t ^ n := hmono
          _ = C / (n + 1) := by
                rw [intervalIntegral.integral_const_mul, integral_pow]
                norm_num
                rfl
      rw [hterm]
      dsimp [C, d] at hintegral ⊢
      have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      calc
        ‖∫ t in (0 : ℝ)..1, (z - c) • integrand (AffineMap.lineMap c z t)‖ ≤
            ‖y‖ * (M * ‖z - c‖) ^ (n + 1) / (n.factorial : ℝ) / (n + 1) := hintegral
        _ = ‖y‖ * (M * ‖z - c‖) ^ (n + 1) / ((n + 1).factorial : ℝ) := by
          rw [Nat.factorial_succ, Nat.cast_mul]
          field_simp [hn]
          push_cast
          ring

end DOZZ.Proofs
