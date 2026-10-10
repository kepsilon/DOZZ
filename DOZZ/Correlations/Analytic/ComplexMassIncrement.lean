/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Charge
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.MeanValue

/-! The small-annulus derivative estimate for complex mass powers. -/

@[expose] public section
open Set
namespace DOZZ.Proofs

/-- Adding a nonnegative annular mass changes a complex power by at most its size times a
sum of endpoint derivative powers. Both signs of the real exponent are covered. -/
theorem cpow_mass_increment_le (Z Y : ℝ) (hZ : 0 < Z) (hY : 0 ≤ Y) (p : ℂ) :
    ‖((Z + Y : ℝ) : ℂ) ^ p - (Z : ℂ) ^ p‖ ≤
      ‖p‖ * (Z ^ (p.re - 1) + (Z + Y) ^ (p.re - 1)) * Y := by
  let F : ℝ → ℂ := fun x => (x : ℂ) ^ p
  let D : ℝ → ℂ := fun x => p * (x : ℂ) ^ (p - 1)
  have hd (x : ℝ) (hx : x ∈ Icc Z (Z + Y)) : HasDerivAt F (D x) x := by
    have hp : 0 < x := hZ.trans_le hx.1
    exact (Complex.hasStrictDerivAt_cpow_const
      (Complex.ofReal_mem_slitPlane.mpr hp)).hasDerivAt.comp_ofReal
  have hb (x : ℝ) (hx : x ∈ Ico Z (Z + Y)) :
      ‖D x‖ ≤ ‖p‖ * (Z ^ (p.re - 1) + (Z + Y) ^ (p.re - 1)) := by
    have hp : 0 < x := hZ.trans_le hx.1
    dsimp [D]
    rw [norm_mul, norm_cpow_positive x hp, Complex.sub_re, Complex.one_re]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg p)
    rcases le_or_gt 0 (p.re - 1) with he | he
    · have h := Real.rpow_le_rpow hp.le hx.2.le he
      exact h.trans (le_add_of_nonneg_left (Real.rpow_nonneg hZ.le _))
    · have h := Real.rpow_le_rpow_of_nonpos hZ hx.1 he.le
      exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg (by linarith : 0 ≤ Z + Y) _))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x hx => (hd x hx).hasDerivWithinAt) hb (Z + Y)
    (show Z + Y ∈ Icc Z (Z + Y) from ⟨by linarith, le_rfl⟩)
  simpa only [F, add_sub_cancel_left] using h

end DOZZ.Proofs
