/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionExponent
import Mathlib.Tactic

/-! # Exact radial likelihood identities for the inner reflected increment

The powers of the radial likelihood identify two Gaussian tilts: `2ν` for the leading term, and
`γ` for the first-order error.
-/

public section

namespace DOZZ.Proofs

/-- The reflected exponent is strictly between zero and one on the reflected charge window. -/
theorem reflected_exponent_mem_Ioo (γ α : ℝ) (hγ : 0 < γ)
    (hα : α < Q γ) (hreflect : Q γ - α < γ / 2) :
    reflectionExponent γ α ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold reflectionExponent
  constructor
  · exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hα)) hγ
  · rw [div_lt_one hγ]
    linarith only [hreflect]

/-- The leading reflection power is exactly a Cameron–Martin likelihood at shift `2ν`. -/
theorem reflected_radial_tilt_identity (γ ν B t h : ℝ) (hγ : γ ≠ 0) :
    Real.exp (γ * B - γ * ν * (t + h) - γ ^ 2 / 2 * t) ^ (2 * ν / γ) =
      Real.exp (-(γ * ν) * t) * Real.exp (2 * ν * B - 2 * ν ^ 2 * (t + h)) := by
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- The first-order error is exactly the `γ` likelihood times a deterministic scale. -/
theorem reflected_radial_first_order_tilt_identity (γ ν B t h : ℝ) :
    Real.exp (γ * B - γ * ν * (t + h) - γ ^ 2 / 2 * t) =
      Real.exp (-γ * ν * (t + h) + γ ^ 2 / 2 * h) *
        Real.exp (γ * B - γ ^ 2 / 2 * (t + h)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The scale `exp(-κt)` is the literal norm power when `t=-log r`. -/
theorem reflected_log_radius_power (κ r : ℝ) (hr : 0 < r) :
    Real.exp (-κ * (-Real.log r)) = r ^ κ := by
  rw [Real.rpow_def_of_pos hr]
  congr 1
  ring

end DOZZ.Proofs
