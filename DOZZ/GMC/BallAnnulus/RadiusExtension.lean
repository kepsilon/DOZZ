/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.BallAnnulus.CompactSmall

/-! Extending a sharp small-radius estimate over a bounded radius interval. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Uniform positive lower and finite upper bounds on coarse radii extend a sharp
small-radius bound to the full interval up to one. -/
theorem gmc_twoSided_radius_extend
    {S : Type*} (f : S → ℝ → ℝ≥0∞) (ξ a : ℝ) (ha : 0 < a)
    (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hsmall : ∀ z r, 0 < r → r ≤ a →
      ENNReal.ofReal (C₀⁻¹ * r ^ ξ) ≤ f z r ∧ f z r ≤ ENNReal.ofReal (C₀ * r ^ ξ))
    (l u : ℝ) (hl : 0 < l) (hu : 0 ≤ u)
    (hlarge : ∀ z r, a ≤ r → r ≤ 1 → ENNReal.ofReal l ≤ f z r ∧ f z r ≤ ENNReal.ofReal u) :
    ∃ C : ℝ, 0 < C ∧ ∀ z r, 0 < r → r ≤ 1 →
      ENNReal.ofReal (C⁻¹ * r ^ ξ) ≤ f z r ∧ f z r ≤ ENNReal.ofReal (C * r ^ ξ) := by
  let d := a ^ |ξ|
  let D := a ^ (-|ξ|)
  have hd : 0 < d := Real.rpow_pos_of_pos ha _
  have hD : 0 < D := Real.rpow_pos_of_pos ha _
  let C := C₀ + u/d + D/l + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC₀ : C₀ ≤ C := by dsimp [C]; linarith [div_nonneg hu hd.le, (div_pos hD hl).le]
  have huC : u/d ≤ C := by dsimp [C]; linarith [div_nonneg hu hd.le, (div_pos hD hl).le]
  have hDC : D/l ≤ C := by dsimp [C]; linarith [div_nonneg hu hd.le]
  refine ⟨C, hC, ?_⟩
  intro z r hr hr1
  by_cases hra : r ≤ a
  · obtain ⟨hlo, hup⟩ := hsmall z r hr hra
    exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      ((inv_le_inv₀ hC hC₀).mpr hCC₀) (Real.rpow_nonneg hr.le _))).trans hlo,
      hup.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCC₀
        (Real.rpow_nonneg hr.le _)))⟩
  · have har := (le_of_not_ge hra)
    have hrd : d ≤ r ^ ξ :=
      (Real.rpow_le_rpow ha.le har (abs_nonneg ξ)).trans
        (Real.rpow_le_rpow_of_exponent_ge hr hr1 (le_abs_self ξ))
    have hrD : r ^ ξ ≤ D :=
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (neg_abs_le ξ)).trans
        (Real.rpow_le_rpow_of_nonpos ha har (neg_nonpos.mpr (abs_nonneg ξ)))
    obtain ⟨hlo, hup⟩ := hlarge z r har hr1
    constructor
    · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hlo
      have hDl : D ≤ C*l := (div_le_iff₀ hl).mp hDC
      have hh : r ^ ξ / C ≤ l := (div_le_iff₀ hC).mpr (by nlinarith only [hrD, hDl])
      simpa only [div_eq_mul_inv, mul_comm] using hh
    · apply hup.trans (ENNReal.ofReal_le_ofReal ?_)
      have huc : u ≤ C*d := (div_le_iff₀ hd).mp huC
      exact huc.trans (mul_le_mul_of_nonneg_left hrd hC.le)

end DOZZ.Proofs
end
