/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.ConnectionDet
public import DOZZ.FourPoint.Crossing.ConnectionRatio
import Mathlib.Tactic

/-! # Crossing from the two diagonal coefficients

This is finite matrix algebra on the source's physical Gauss intervals. The
hypotheses describe two diagonal quadratic forms related by the literal connection
matrix; the conclusion identifies their zero-channel and one-channel coefficients.
-/

public section
namespace DOZZ.Proofs

/-- The zero-channel first coefficient is the exact l-ratio times the
one-channel second coefficient. -/
theorem crossing_diagonal_coefficient_extraction (a b c d₀ d₁ E : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hb1 : b < 1)
    (hc : 0 < c) (hc1 : c < 1)
    (hδ : 0 < c - a - b) (hδ1 : c - a - b < 1)
    (hcn : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδn : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hcross :
      let u := Real.Gamma c * Real.Gamma (c - a - b) *
        (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
      let v := Real.Gamma c * Real.Gamma (a + b - c) *
        (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
      let w := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
        (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
      let x := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
        (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
      d₀ * u * v + d₁ * w * x = 0)
    (hE : E =
      d₀ * (Real.Gamma c * Real.Gamma (a + b - c) *
        (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹) ^ 2 +
      d₁ * (Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
        (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹) ^ 2) :
    d₀ = (lR a * lR b / (lR c * lR (a + b - c))) * E := by
  let u := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v := Real.Gamma c * Real.Gamma (a + b - c) *
    (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  have hw : w ≠ 0 := by
    dsimp [w]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero
      (Real.Gamma_pos_of_pos (by linarith only [hc1])).ne'
      (Real.Gamma_pos_of_pos hδ).ne')
      (inv_ne_zero (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'))
      (inv_ne_zero (Real.Gamma_pos_of_pos (sub_pos.mpr hb1)).ne')
  have hΓneg : Real.Gamma (a + b - c) ≠ 0 := Real.Gamma_ne_zero
    (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith only [hδ1])
      (by push_cast; linarith only [hδ]))
  have hv : v ≠ 0 := by
    dsimp [v]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (Real.Gamma_pos_of_pos hc).ne' hΓneg)
      (inv_ne_zero (Real.Gamma_pos_of_pos ha).ne'))
      (inv_ne_zero (Real.Gamma_pos_of_pos hb).ne')
  have hdet : u * x - v * w = (c - 1) / (c - a - b) :=
    crossing_connection_det_real a b c hcn hδn
  have hdet0 : u * x - v * w ≠ 0 := by
    rw [hdet]
    exact div_ne_zero (by linarith only [hc1]) hδ.ne'
  have hex := dual_connection_first_seed_scalar d₀ d₁ u v w x hcross hw hv hdet0
  change E = d₀ * v ^ 2 + d₁ * x ^ 2 at hE
  rw [← hE, hdet] at hex
  have hratio := crossing_connection_first_ratio a b c ha ha1 hb hb1 hc hc1 hδ hδ1
  change -w / (v * ((c - 1) / (c - a - b))) = _ at hratio
  rw [hratio] at hex
  exact hex

end DOZZ.Proofs
