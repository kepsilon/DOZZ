/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.Beta
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # The signed Pareto coefficient in the inner cluster

The maximum density contributes `a` times this convergent integral. This reuses the planar beta
integral (`beta_negative_power_integral`) at exponent `a + 1`, rather than a new endpoint-series
calculation.
-/

public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- The full signed integral from the independent exponential maximum. -/
theorem reflected_pareto_integral (p a : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) :
    IntegrableOn (fun w : ℝ => ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) (Ioi 0) ∧
      (∫ w : ℝ in Ioi 0, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) =
        Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p := by
  have h := beta_negative_power_integral p (a + 1) hp (by linarith only [ha])
    (by linarith only [ha₁])
  simpa only [show -(a + 1) = -a - 1 by ring,
    show 1 - (a + 1) = -a by ring,
    show p + (a + 1) - 1 = p + a by ring] using h

/-- The normalization multiplying the reflection moment in the inner limit. -/
theorem reflected_pareto_density_integral (p a : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) :
    (∫ w : ℝ in Ioi 0, a * (((1 + w) ^ (-p) - 1) * w ^ (-a - 1))) =
      a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p := by
  rw [integral_const_mul, (reflected_pareto_integral p a hp ha ha₁).2]
  ring

/-- The omitted small Pareto values have a first-order bound, valid on the entire half-line. -/
theorem reflected_negative_power_increment (p v : ℝ) (hp : 0 < p) (hv : 0 ≤ v) :
    |(1 + v) ^ (-p) - 1| ≤ p * v := by
  have hd : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => (1 + y) ^ (-p))
        ((-p) * (1 + x) ^ (-p - 1)) x := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    have hh := (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -p)
      (Or.inl (by linarith only [hx0]))).comp x ((hasDerivAt_id x).const_add 1)
    simpa only [Function.comp_def, mul_one] using hh
  have hb : ∀ x ∈ Ici (0 : ℝ), ‖deriv (fun y : ℝ => (1 + y) ^ (-p)) x‖ ≤ p := by
    intro x hx
    have hx0 : 0 ≤ x := hx
    rw [(hd x hx).deriv, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hp,
      abs_of_nonneg (Real.rpow_nonneg (by linarith only [hx0]) _)]
    exact mul_le_of_le_one_right hp.le
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith only [hx0])
        (by linarith only [hp]))
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun x hx => (hd x hx).differentiableAt) hb (convex_Ici (0 : ℝ))
    (show (0 : ℝ) ∈ Ici 0 from le_rfl) (show v ∈ Ici 0 from hv)
  simpa only [add_zero, Real.one_rpow, sub_zero, Real.norm_eq_abs, abs_of_nonneg hv]
    using hm

/-- The lower-cutoff Pareto error is bounded by its explicit integrable power primitive. -/
theorem reflected_pareto_lower_cut_bound (p a ε : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) (hε : 0 ≤ ε) :
    |∫ w : ℝ in Ioc 0 ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)| ≤
      p * ε ^ (1 - a) / (1 - a) := by
  have hf := (reflected_pareto_integral p a hp ha ha₁).1.mono_set
    (show Ioc 0 ε ⊆ Ioi (0 : ℝ) from fun _ hw => hw.1)
  have hi : IntegrableOn (fun w : ℝ => w ^ (-a)) (Ioc 0 ε) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε)
      (by linarith only [ha₁] : -1 < -a)).1
  have hg : IntegrableOn (fun w : ℝ => p * w ^ (-a)) (Ioc 0 ε) := hi.const_mul p
  have hb : ∀ᵐ w ∂(volume.restrict (Ioc 0 ε)),
      ‖((1 + w) ^ (-p) - 1) * w ^ (-a - 1)‖ ≤ p * w ^ (-a) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    have hwpos : 0 < w := hw.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hwpos _)]
    calc
      |(1 + w) ^ (-p) - 1| * w ^ (-a - 1) ≤ (p * w) * w ^ (-a - 1) :=
        mul_le_mul_of_nonneg_right (reflected_negative_power_increment p w hp hwpos.le)
          (Real.rpow_nonneg hwpos.le _)
      _ = p * w ^ (-a) := by
        have he : w * w ^ (-a - 1) = w ^ (-a) := by
          calc
            w * w ^ (-a - 1) = w ^ (1 : ℝ) * w ^ (-a - 1) := by rw [Real.rpow_one]
            _ = w ^ (1 + (-a - 1)) := (Real.rpow_add hwpos _ _).symm
            _ = w ^ (-a) := by congr 1; ring
        rw [mul_assoc, he]
  have hint : (∫ w : ℝ in Ioc 0 ε, p * w ^ (-a)) = p * ε ^ (1 - a) / (1 - a) := by
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hε,
      integral_rpow (Or.inl (by linarith only [ha₁] : -1 < -a))]
    rw [show -a + 1 = 1 - a by ring, Real.zero_rpow (by linarith only [ha₁] : 1 - a ≠ 0), sub_zero]
    ring
  calc
    _ = ‖∫ w : ℝ in Ioc 0 ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∫ w : ℝ in Ioc 0 ε, ‖((1 + w) ^ (-p) - 1) * w ^ (-a - 1)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℝ in Ioc 0 ε, p * w ^ (-a) := integral_mono_ae hf.norm hg hb
    _ = _ := hint

/-- Truncating the Pareto integral at ε changes its full coefficient by an explicit small error. -/
theorem reflected_pareto_tail_coefficient_bound (p a ε : ℝ) (hp : 0 < p)
    (ha : 0 < a) (ha₁ : a < 1) (hε : 0 ≤ ε) :
    |(∫ w : ℝ in Ioi ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p| ≤
        p * ε ^ (1 - a) / (1 - a) := by
  obtain ⟨hf, hfull⟩ := reflected_pareto_integral p a hp ha ha₁
  have hid := intervalIntegral.integral_Ioi_sub_Ioi hf hε
  rw [intervalIntegral.integral_of_le hε] at hid
  have he : (∫ w : ℝ in Ioi ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p =
      -(∫ w : ℝ in Ioc 0 ε, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) := by
    rw [← hfull, ← hid]
    ring
  rw [he, abs_neg]
  exact reflected_pareto_lower_cut_bound p a ε hp ha ha₁ hε

/-- The Pareto expansion has an explicit first-order error after restoring the mass scale. -/
theorem reflected_pareto_scaled_error (p a A x : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) (hA : 0 < A) (hx : 0 < x) :
    |a * A ^ (-p) * x ^ a *
        (∫ w : ℝ in Ioi x, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) * A ^ (-p) * x ^ a| ≤
        (a * p / (1 - a)) * A ^ (-p) * x := by
  have hcoef : 0 ≤ a * A ^ (-p) * x ^ a :=
    mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg hA.le _)) (Real.rpow_nonneg hx.le _)
  have he : a * A ^ (-p) * x ^ a *
        (∫ w : ℝ in Ioi x, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
      (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) * A ^ (-p) * x ^ a =
      (a * A ^ (-p) * x ^ a) *
        ((∫ w : ℝ in Ioi x, ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)) -
          Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) := by ring
  rw [he, abs_mul, abs_of_nonneg hcoef]
  calc
    _ ≤ (a * A ^ (-p) * x ^ a) * (p * x ^ (1 - a) / (1 - a)) :=
      mul_le_mul_of_nonneg_left (reflected_pareto_tail_coefficient_bound p a x hp ha ha₁ hx.le)
        hcoef
    _ = (a * p / (1 - a)) * A ^ (-p) * x := by
      have hpow : x ^ a * x ^ (1 - a) = x := by
        rw [← Real.rpow_add hx, add_sub_cancel, Real.rpow_one]
      calc
        _ = (a * p / (1 - a)) * A ^ (-p) * (x ^ a * x ^ (1 - a)) := by ring
        _ = _ := by rw [hpow]

end DOZZ.Proofs
