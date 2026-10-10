/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Basic

/-! A finite grid of commuting local continuation squares has path-independent boundary transfer
between its fixed endpoints. -/

@[expose] public section

namespace DOZZ.Proofs

variable {E : Type*}

/-- Apply `n` horizontal continuation steps, beginning at column `i` on row `j`. -/
def finiteGridHorizontal (right : ℕ → ℕ → E → E) (i j : ℕ) : ℕ → E → E
  | 0, y => y
  | n + 1, y => right (i + n) j (finiteGridHorizontal right i j n y)

/-- Apply `m` vertical continuation steps, beginning at column `i` and row `j`. -/
def finiteGridVertical (up : ℕ → ℕ → E → E) (i j : ℕ) : ℕ → E → E
  | 0, y => y
  | m + 1, y => up i (j + m) (finiteGridVertical up i j m y)

theorem finiteGridVertical_after_horizontal_edge
    (right up : ℕ → ℕ → E → E)
    (hsquare : ∀ i j y, up (i + 1) j (right i j y) = right i (j + 1) (up i j y))
    (i j m : ℕ) (y : E) :
    finiteGridVertical up (i + 1) j m (right i j y) =
      right i (j + m) (finiteGridVertical up i j m y) := by
  induction m with
  | zero => simp [finiteGridVertical]
  | succ m ih =>
      simp only [finiteGridVertical]
      rw [ih]
      exact hsquare i (j + m) (finiteGridVertical up i j m y)

theorem finiteGrid_rectangle_transfer
    (right up : ℕ → ℕ → E → E)
    (hsquare : ∀ i j y, up (i + 1) j (right i j y) = right i (j + 1) (up i j y))
    (i j n m : ℕ) (y : E) :
    finiteGridVertical up (i + n) j m (finiteGridHorizontal right i j n y) =
      finiteGridHorizontal right i (j + m) n (finiteGridVertical up i j m y) := by
  induction n with
  | zero => simp [finiteGridHorizontal]
  | succ n ih =>
      simp only [finiteGridHorizontal]
      have hindex : i + (n + 1) = (i + n) + 1 := by omega
      rw [hindex]
      rw [finiteGridVertical_after_horizontal_edge right up hsquare (i + n) j m
        (finiteGridHorizontal right i j n y)]
      rw [ih]


end DOZZ.Proofs
