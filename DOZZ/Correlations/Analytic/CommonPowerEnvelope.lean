/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ComplexMassIncrement

/-! Common lower- and upper-mass envelopes for varying complex powers. -/

@[expose] public section
namespace DOZZ.Proofs

/-- On a positive mass interval, every exponent between a nonpositive lower endpoint and a
nonnegative upper endpoint is controlled by the corresponding endpoint masses. -/
theorem rpow_between_mass_envelope (L x U lo p hi : ℝ)
    (hL : 0 < L) (hLx : L ≤ x) (hxU : x ≤ U)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hlop : lo ≤ p) (hphi : p ≤ hi) :
    x ^ p ≤ L ^ lo + U ^ hi := by
  have hx : 0 < x := hL.trans_le hLx
  have hU : 0 < U := hx.trans_le hxU
  rcases le_total x 1 with hx1 | hx1
  · have hp : x ^ p ≤ x ^ lo := Real.rpow_le_rpow_of_exponent_ge hx hx1 hlop
    have hm : x ^ lo ≤ L ^ lo := Real.rpow_le_rpow_of_nonpos hL hLx hlo
    exact (hp.trans hm).trans (le_add_of_nonneg_right (Real.rpow_nonneg hU.le _))
  · have hp : x ^ p ≤ x ^ hi := Real.rpow_le_rpow_of_exponent_le hx1 hphi
    have hm : x ^ hi ≤ U ^ hi := Real.rpow_le_rpow hx.le hxU hhi
    exact (hp.trans hm).trans (le_add_of_nonneg_left (Real.rpow_nonneg hL.le _))

/-- A single mass envelope controls both the derivative and the absolute value bounds of a
complex-power increment, uniformly over the given exponent range. -/
theorem cpow_common_envelope (L Z Y U lo hi : ℝ) (p : ℂ)
    (hL : 0 < L) (hLZ : L ≤ Z) (hY : 0 ≤ Y) (hZU : Z + Y ≤ U)
    (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hlop : lo ≤ p.re - 1) (hphi : p.re ≤ hi) :
    ‖((Z + Y : ℝ) : ℂ) ^ p - (Z : ℂ) ^ p‖ ≤
      (2 * ‖p‖ * (L ^ lo + U ^ hi)) * Y ∧
    ‖((Z + Y : ℝ) : ℂ) ^ p - (Z : ℂ) ^ p‖ ≤ 2 * (L ^ lo + U ^ hi) := by
  have hZ : 0 < Z := hL.trans_le hLZ
  have hZY : 0 < Z + Y := add_pos_of_pos_of_nonneg hZ hY
  have hZU' : Z ≤ U := (le_add_of_nonneg_right hY).trans hZU
  have hLZY : L ≤ Z + Y := hLZ.trans (le_add_of_nonneg_right hY)
  have hzder := rpow_between_mass_envelope L Z U lo (p.re - 1) hi
    hL hLZ hZU' hlo hhi hlop (by linarith)
  have hzyder := rpow_between_mass_envelope L (Z + Y) U lo (p.re - 1) hi
    hL hLZY hZU hlo hhi hlop (by linarith)
  have hz := rpow_between_mass_envelope L Z U lo p.re hi
    hL hLZ hZU' hlo hhi (by linarith) hphi
  have hzy := rpow_between_mass_envelope L (Z + Y) U lo p.re hi
    hL hLZY hZU hlo hhi (by linarith) hphi
  constructor
  · apply (cpow_mass_increment_le Z Y hZ hY p).trans
    apply mul_le_mul_of_nonneg_right _ hY
    have := mul_le_mul_of_nonneg_left (add_le_add hzder hzyder) (norm_nonneg p)
    nlinarith
  · calc
      _ ≤ ‖((Z + Y : ℝ) : ℂ) ^ p‖ + ‖(Z : ℂ) ^ p‖ := norm_sub_le _ _
      _ = (Z + Y) ^ p.re + Z ^ p.re := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hZY, Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      _ ≤ _ := by linarith

end DOZZ.Proofs
