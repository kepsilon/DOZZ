/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Q
import Mathlib.Tactic

/-! # The full reflected charge window

Algebraic bounds for the window. No upper bound `ξ < 1/2` is used.
-/

public section

namespace DOZZ.Proofs

/-- The slack inequalities force the power case in the outer radial integral. -/
theorem reflected_window_bounds (γ α ξ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < Q γ) (hreflect : Q γ - α < γ / 2)
    (hslack : γ * (Q γ - α) < ξ)
    (hfreeze : γ * (Q γ - α) <
      (1 - ξ) * (γ * (Q γ - α) + (α + γ / 2 - Q γ) ^ 2 / 2)) :
    0 < γ * (Q γ - α) ∧ γ * (Q γ - α) < 1 / 2 ∧
      γ * (Q γ - α) + (α + γ / 2 - Q γ) ^ 2 / 2 < 1 := by
  let ν := Q γ - α
  let κ := γ * ν
  let δ := (γ / 2 - ν) ^ 2 / 2
  have hν : 0 < ν := sub_pos.mpr hα
  have hνb : ν < γ / 2 := hreflect
  have hκ : 0 < κ := mul_pos hγ hν
  have hδ : 0 ≤ δ := div_nonneg (sq_nonneg _) (by norm_num)
  have hδ₂ : δ < 1 / 2 := by
    dsimp only [δ]
    have hb : 0 < γ / 2 - ν := sub_pos.mpr hνb
    have hb₂ : γ / 2 - ν < 1 := by linarith only [hγ₂, hν]
    nlinarith only [hb, hb₂]
  have he : (α + γ / 2 - Q γ) ^ 2 / 2 = δ := by
    dsimp only [δ, ν]
    ring
  rw [he] at hfreeze
  change κ < (1 - ξ) * (κ + δ) at hfreeze
  change κ < ξ at hslack
  have hsum : 0 < κ + δ := add_pos_of_pos_of_nonneg hκ hδ
  have hstrict : κ < (1 - κ) * (κ + δ) :=
    hfreeze.trans (mul_lt_mul_of_pos_right (by linarith only [hslack]) hsum)
  have hκ₂ : κ < 1 / 2 := by
    by_contra hn
    have hk : 1 / 2 ≤ κ := le_of_not_gt hn
    have hx : 0 ≤ (κ - 1 / 2) * (κ + 1 / 2 + δ) :=
      mul_nonneg (sub_nonneg.mpr hk) (by linarith only [hκ, hδ])
    nlinarith only [hstrict, hδ₂, hx]
  refine ⟨hκ, hκ₂, ?_⟩
  rw [he]
  change κ + δ < 1
  linarith only [hκ₂, hδ₂]

/-- The limiting reflected triple has strict ordinary Seiberg charge bounds. -/
theorem reflected_triple_seiberg (γ α₁ α₂ α₃ : ℝ)
    (hreflect : Q γ - α₁ < γ / 2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) (hα₁ : α₁ < Q γ) :
    2 * Q γ - α₁ - γ / 2 < Q γ ∧ α₂ < Q γ ∧ α₃ < Q γ ∧
      2 * Q γ < (2 * Q γ - α₁ - γ / 2) + α₂ + α₃ := by
  refine ⟨?_, hα₂, hα₃, ?_⟩
  · linarith only [hreflect]
  · linarith only [hs, hα₁]

/-- The reflected charge changes the zero-mode order by the reflection exponent. -/
theorem reflected_zero_mode_order (γ α₁ α₂ α₃ : ℝ) :
    ((2 * Q γ - α₁ - γ / 2) + α₂ + α₃ - 2 * Q γ) / γ =
      (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ +
        2 * (Q γ - α₁) / γ := by
  ring

end DOZZ.Proofs
