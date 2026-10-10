/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorScale
public import DOZZ.Hypergeom.Planar.TaylorTail

/-! Rotation and scaling give the integral of the corrected Taylor kernel at every center. -/

@[expose] public section

open MeasureTheory

namespace DOZZ.Proofs

/-- The parent Taylor integral is homogeneous of degree `2 + k - β`, including at the zero
center. -/
theorem planarTaylorRemainder_integral_scale_norm (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ,
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) =
        ‖z‖ ^ (2 + k - β) *
          (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
  intro z
  have hα : 0 < 2 + k - β := by linarith
  by_cases hz : z = 0
  · subst z
    have hzero : DOZZ.planarTaylorRemainder k β 0 = fun _ : ℂ => (0 : ℝ) := by
      funext u
      simp [DOZZ.planarTaylorRemainder]
    rw [hzero]
    simp [Real.zero_rpow, hα.ne']
  · let r : ℝ := ‖z‖
    let ξ : ℂ := z / (r : ℂ)
    have hr : 0 < r := by dsimp [r]; exact norm_pos_iff.mpr hz
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hξ : ‖ξ‖ = 1 := by
      dsimp [ξ]
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      dsimp [r]
      exact div_self (norm_ne_zero_iff.mpr hz)
    have hξr : ξ * (r : ℂ) = z := by
      dsimp [ξ]
      field_simp [hrC]
    have hscale := planarTaylorRemainder_integral_scale k β hk hβ ξ hξ r hr z hξr
    simpa [r] using hscale

end DOZZ.Proofs
