/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The complement of the nonnegative real axis is a simply connected regular domain for the
Gauss system. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The slit plane obtained by removing the nonnegative real axis. -/
def gaussNegativeCutPlane : Set ℂ := {z | z.im ≠ 0 ∨ z.re < 0}

/-- The negative cut plane is open. -/
theorem gaussNegativeCutPlane_isOpen : IsOpen gaussNegativeCutPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 0})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

/-- The negative cut plane avoids the two singularities of the Gauss system. -/
theorem gaussNegativeCutPlane_subset_regularPlane :
    gaussNegativeCutPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  change z.im ≠ 0 ∨ z.re < 0 at hz
  rcases hz with him | hnegative
  · constructor
    · intro h
      apply him
      rw [h]
      simp
    · intro h
      apply him
      rw [h]
      simp
  · constructor
    · intro h
      have hre : z.re = 0 := by rw [h]; simp
      linarith
    · intro h
      have hre : z.re = 1 := by rw [h]; simp
      linarith

/-- The negative cut plane is star-convex about `-1/2`. -/
theorem gaussNegativeCutPlane_starConvex :
    StarConvex ℝ (-1 / 2 : ℂ) gaussNegativeCutPlane := by
  intro z hz s t hs ht hst
  change z.im ≠ 0 ∨ z.re < 0 at hz
  change (s • (-1 / 2 : ℂ) + t • z).im ≠ 0 ∨
    (s • (-1 / 2 : ℂ) + t • z).re < 0
  rcases hz with him | hreal
  · by_cases ht0 : t = 0
    · right
      have hs1 : s = 1 := by linarith
      rw [ht0, hs1]
      norm_num
    · left
      have himag : (s • (-1 / 2 : ℂ) + t • z).im = t * z.im := by
        simp [Complex.add_im]
      rw [himag]
      have htpos : 0 < t := by
        by_contra hnot
        have htneg : t ≤ 0 := le_of_not_gt hnot
        exact ht0 (le_antisymm htneg ht)
      exact mul_ne_zero htpos.ne' him
  · right
    have hrealpart : (s • (-1 / 2 : ℂ) + t • z).re = -(s / 2) + t * z.re := by
      simp [Complex.add_re]
      ring
    rw [hrealpart]
    by_cases ht0 : t = 0
    · have hs1 : s = 1 := by linarith
      rw [ht0, hs1]
      norm_num
    · have htpos : 0 < t := by
        by_contra hnot
        have htneg : t ≤ 0 := le_of_not_gt hnot
        exact ht0 (le_antisymm htneg ht)
      have hsecond : t * z.re < 0 := mul_neg_of_pos_of_neg htpos hreal
      have hfirst : -(s / 2) ≤ 0 := neg_nonpos.mpr (div_nonneg hs (by norm_num))
      linarith

/-- Contractibility of the negative cut plane. -/
instance gaussNegativeCutPlane_contractible : ContractibleSpace gaussNegativeCutPlane := by
  apply gaussNegativeCutPlane_starConvex.contractibleSpace
  exact ⟨(-1 / 2 : ℂ), by norm_num [gaussNegativeCutPlane]⟩


end DOZZ.Proofs
