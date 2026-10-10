/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q

/-! Algebra behind the weighted local-moment threshold and annular summability exponent. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The weighted radial scaling exponent factors into the positive charge factor and the
insertion-slack factor. -/
theorem weightedGmcMomentExponent_factorization (γ α p : ℝ) :
    γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 =
      (γ * p / 2) * (2 * (Q γ - α) - γ * p) := by
  unfold Q
  field_simp

/-- For a positive moment order, the weighted annular exponent is positive exactly below the
insertion threshold `2 (Q - α) / γ`. -/
theorem weightedGmcMomentExponent_pos_iff
    {γ α p : ℝ} (hγ : 0 < γ) (hp : 0 < p) :
    0 < γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 ↔
      p < 2 * (Q γ - α) / γ := by
  rw [weightedGmcMomentExponent_factorization]
  have hscale : 0 < γ * p / 2 := by positivity
  rw [mul_pos_iff_of_pos_left hscale]
  rw [lt_div_iff₀ hγ]
  constructor <;> intro h <;> nlinarith

end DOZZ.Proofs
