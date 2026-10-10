/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! The principal Gauss cut plane is contractible, hence simply connected. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The principal Gauss cut plane is an open subset of the regular plane. -/
theorem gaussCutPlane_isOpen : IsOpen gaussCutPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | 0 < z.re ∧ z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    ((isOpen_Ioo.preimage Complex.continuous_re))

/-- Every point of the principal cut plane avoids the two singularities of the Gauss system. -/
theorem gaussCutPlane_subset_regularPlane : gaussCutPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  rcases hz with him | ⟨hz0, hz1⟩
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

/-- The principal Gauss cut plane is star-convex about its midpoint. -/
theorem gaussCutPlane_starConvex :
    StarConvex ℝ (1 / 2 : ℂ) gaussCutPlane := by
  intro z hz s t hs ht hst
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
  change (s • (1 / 2 : ℂ) + t • z).im ≠ 0 ∨
    (0 < (s • (1 / 2 : ℂ) + t • z).re ∧
      (s • (1 / 2 : ℂ) + t • z).re < 1)
  rcases hz with him | ⟨hz0, hz1⟩
  · by_cases ht0 : t = 0
    · right
      have hs1 : s = 1 := by linarith
      rw [ht0, hs1]
      norm_num
    · left
      have himag : (s • (1 / 2 : ℂ) + t • z).im = t * z.im := by
        simp [Complex.add_im]
      rw [himag]
      have htpos : 0 < t := by
        by_contra hnot
        have htneg : t ≤ 0 := le_of_not_gt hnot
        exact ht0 (le_antisymm htneg ht)
      exact mul_ne_zero htpos.ne' him
  · right
    have hreal : (s • (1 / 2 : ℂ) + t • z).re = s / 2 + t * z.re := by
      simp [Complex.add_re]
      ring
    rw [hreal]
    constructor
    · by_cases hs0 : s = 0
      · have ht1 : t = 1 := by linarith
        rw [hs0, ht1]
        simpa using hz0
      · have hspos : 0 < s := by
          by_contra hnot
          have hsneg : s ≤ 0 := le_of_not_gt hnot
          exact hs0 (le_antisymm hsneg hs)
        have hfirst : 0 < s / 2 := by positivity
        have hsecond : 0 ≤ t * z.re := mul_nonneg ht hz0.le
        linarith
    · by_cases ht0 : t = 0
      · have hs1 : s = 1 := by linarith
        rw [ht0, hs1]
        norm_num
      · have htpos : 0 < t := by
          by_contra hnot
          have htneg : t ≤ 0 := le_of_not_gt hnot
          exact ht0 (le_antisymm htneg ht)
        have hfirst : s / 2 ≤ s := by linarith [hs]
        have hsecond : t * z.re < t := by
          have hmul := mul_lt_mul_of_pos_left hz1 htpos
          simpa using hmul
        calc
          s / 2 + t * z.re < s + t := by linarith
          _ = 1 := hst

/-- Contractibility of the principal Gauss cut plane as a subtype. -/
instance gaussCutPlane_contractible : ContractibleSpace gaussCutPlane := by
  apply gaussCutPlane_starConvex.contractibleSpace
  exact ⟨(1 / 2 : ℂ), by norm_num [gaussCutPlane]⟩


end DOZZ.Proofs
