/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliAllocation

/-! Allocation to two nested retained masses and a separated fixed mass. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Three-factor allocation is valid at zero orders and at extended endpoints. -/
theorem three_negative_order_allocation (I A B D : ℝ≥0∞) (a b s : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) (hA : A ≤ I) (hB : B ≤ I) (hD : D ≤ I) :
    I ^ (-(a + b + s)) ≤ A ^ (-a) * B ^ (-b) * D ^ (-s) := by
  have hfirst := negative_order_allocation I I D (a + b) s (add_nonneg ha hb) hs le_rfl hD
  exact hfirst.trans (mul_le_mul' (negative_order_allocation I A B a b ha hb hA hB) le_rfl)

/-- Deterministic lower kernel bounds can be pulled through the joint three-mass estimate. -/
theorem three_retained_moment_allocation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (I A B D : Ω → ℝ≥0∞)
    (hAfinite : ∀ ω, A ω ≠ ⊤) (hBfinite : ∀ ω, B ω ≠ ⊤) (hDfinite : ∀ ω, D ω ≠ ⊤)
    (wA wB wD a b s : ℝ) (hwA : 0 < wA) (hwB : 0 < wB) (hwD : 0 < wD)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s)
    (hA : ∀ ω, ENNReal.ofReal wA * A ω ≤ I ω)
    (hB : ∀ ω, ENNReal.ofReal wB * B ω ≤ I ω)
    (hD : ∀ ω, ENNReal.ofReal wD * D ω ≤ I ω) :
    (∫⁻ ω, I ω ^ (-(a + b + s)) ∂P) ≤
      ENNReal.ofReal (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) *
        ∫⁻ ω, A ω ^ (-a) * B ω ^ (-b) * D ω ^ (-s) ∂P := by
  have hpoint (ω : Ω) : I ω ^ (-(a + b + s)) ≤
      ENNReal.ofReal (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) *
        (A ω ^ (-a) * B ω ^ (-b) * D ω ^ (-s)) := by
    have hh := three_negative_order_allocation (I ω)
      (ENNReal.ofReal wA * A ω) (ENNReal.ofReal wB * B ω) (ENNReal.ofReal wD * D ω)
      a b s ha hb hs (hA ω) (hB ω) (hD ω)
    rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hAfinite ω),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hBfinite ω),
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hDfinite ω),
      ENNReal.ofReal_rpow_of_pos hwA, ENNReal.ofReal_rpow_of_pos hwB,
      ENNReal.ofReal_rpow_of_pos hwD] at hh
    convert hh using 1
    rw [ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos hwA _) (Real.rpow_pos_of_pos hwB _)).le,
      ENNReal.ofReal_mul (Real.rpow_pos_of_pos hwA _).le]
    ac_rfl
  exact (lintegral_mono hpoint).trans_eq (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)

end DOZZ.Proofs
