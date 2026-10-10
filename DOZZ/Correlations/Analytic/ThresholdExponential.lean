/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ComplementExponential

/-! Choosing the shrinking threshold and absorbing the imaginary Gaussian growth. -/

@[expose] public section
namespace DOZZ.Proofs

/-- The Markov/Hölder term has the precise residual exponential rate. -/
theorem threshold_ratio_power (C rate τ m h r : ℝ) (hC : 0 ≤ C) :
    (C * Real.exp (-rate * r) / Real.exp (-τ * r) ^ m) ^ h =
      C ^ h * Real.exp (-((rate - τ * m) * h) * r) := by
  have he : C * Real.exp (-rate * r) / Real.exp (-τ * r) ^ m =
      C * Real.exp (-(rate - τ * m) * r) := by
    rw [← Real.exp_mul, mul_div_assoc, ← Real.exp_sub]
    congr 1
    ring_nf
  rw [he, Real.mul_rpow hC (Real.exp_nonneg _), ← Real.exp_mul]
  congr 1
  ring_nf

/-- Both threshold terms decay at the smaller of their two positive rates. -/
theorem threshold_exponential_bound (D B C rate τ m h r : ℝ)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C) (hr : 0 ≤ r) :
    Real.exp (-τ * r) * D +
      B * (C * Real.exp (-rate * r) / Real.exp (-τ * r) ^ m) ^ h ≤
      (D + B * C ^ h) * Real.exp (-(min τ ((rate - τ * m) * h)) * r) := by
  rw [threshold_ratio_power C rate τ m h r hC]
  have h1 : Real.exp (-τ * r) ≤ Real.exp (-(min τ ((rate - τ * m) * h)) * r) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_left τ ((rate - τ * m) * h)) hr
    linarith
  have h2 : Real.exp (-((rate - τ * m) * h) * r) ≤
      Real.exp (-(min τ ((rate - τ * m) * h)) * r) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (min_le_right τ ((rate - τ * m) * h)) hr
    linarith
  calc
    _ ≤ Real.exp (-(min τ ((rate - τ * m) * h)) * r) * D +
        B * (C ^ h * Real.exp (-(min τ ((rate - τ * m) * h)) * r)) :=
      add_le_add (mul_le_mul_of_nonneg_right h1 hD)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hC _)) hB)
    _ = _ := by ring

/-- On a sufficiently thin imaginary neighborhood, the deterministic Gaussian growth loses
at most half of the positive spatial cutoff decay rate. -/
theorem imaginary_decay_absorption (K E d κ r : ℝ)
    (hK : 0 ≤ K)
    (hthin : E * d ≤ κ / 2) (hr : 0 ≤ r) :
    Real.exp (E * (r + 2) * d) * (K * Real.exp (-κ * r)) ≤
      (K * Real.exp κ) * Real.exp (-(κ / 2) * r) := by
  have he : E * (r + 2) * d - κ * r ≤ κ - κ / 2 * r := by
    have := mul_le_mul_of_nonneg_right hthin (show 0 ≤ r + 2 by linarith)
    nlinarith
  calc
    _ = K * Real.exp (E * (r + 2) * d - κ * r) := by
      rw [Real.exp_sub, show -κ * r = -(κ * r) by ring, Real.exp_neg]
      ring_nf
    _ ≤ K * Real.exp (κ - κ / 2 * r) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hK
    _ = _ := by
      rw [Real.exp_sub]
      have heq : -(κ / 2) * r = -(κ / 2 * r) := by ring
      rw [heq, Real.exp_neg]
      ring_nf

end DOZZ.Proofs
