/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.FiniteGridTransfer

/-! The finite grid transfer theorem with square identities required only on the cells of the
finite rectangle. -/

@[expose] public section

namespace DOZZ.Proofs

theorem finiteGridVertical_after_horizontal_edge_of_bounded_squares
    {E : Type*} (N : ℕ) (right up : ℕ → ℕ → E → E)
    (hsquare : ∀ i < N, ∀ j < N, ∀ y,
      up (i + 1) j (right i j y) = right i (j + 1) (up i j y))
    (i j m : ℕ) (hi : i < N) (hm : j + m ≤ N) (y : E) :
    finiteGridVertical up (i + 1) j m (right i j y) =
      right i (j + m) (finiteGridVertical up i j m y) := by
  induction m with
  | zero => simp [finiteGridVertical]
  | succ m ih =>
      have hrow : j + m < N := by omega
      simp only [finiteGridVertical]
      rw [ih (by omega)]
      exact hsquare i hi (j + m) hrow _

theorem finiteGrid_rectangle_transfer_of_bounded_squares
    {E : Type*} (N : ℕ) (right up : ℕ → ℕ → E → E)
    (hsquare : ∀ i < N, ∀ j < N, ∀ y,
      up (i + 1) j (right i j y) = right i (j + 1) (up i j y))
    (i j n m : ℕ) (hi : i + n ≤ N) (hj : j + m ≤ N) (y : E) :
    finiteGridVertical up (i + n) j m (finiteGridHorizontal right i j n y) =
      finiteGridHorizontal right i (j + m) n (finiteGridVertical up i j m y) := by
  induction n with
  | zero => simp [finiteGridHorizontal]
  | succ n ih =>
      have hcol : i + n < N := by omega
      simp only [finiteGridHorizontal]
      have hindex : i + (n + 1) = (i + n) + 1 := by omega
      rw [hindex]
      rw [finiteGridVertical_after_horizontal_edge_of_bounded_squares
        N right up hsquare (i + n) j m hcol hj _]
      rw [ih (by omega)]

theorem finiteGridVertical_eq_self_of_bounded_edges
    {E : Type*} (N c : ℕ) (up : ℕ → ℕ → E → E)
    (hedge : ∀ j < N, ∀ y, up c j y = y) (y : E) :
    finiteGridVertical up c 0 N y = y := by
  induction N with
  | zero => simp [finiteGridVertical]
  | succ N ih =>
      simp only [finiteGridVertical, Nat.zero_add]
      rw [ih (fun j hj => hedge j (by omega))]
      exact hedge N (by omega) y

theorem finiteGrid_boundary_transfer_eq_of_bounded_squares
    {E : Type*} (N : ℕ) (right up : ℕ → ℕ → E → E)
    (hsquare : ∀ i < N, ∀ j < N, ∀ y,
      up (i + 1) j (right i j y) = right i (j + 1) (up i j y))
    (hleft : ∀ j < N, ∀ y, up 0 j y = y)
    (hright : ∀ j < N, ∀ y, up N j y = y)
    (y : E) :
    finiteGridHorizontal right 0 0 N y = finiteGridHorizontal right 0 N N y := by
  have hrect := finiteGrid_rectangle_transfer_of_bounded_squares
    N right up hsquare 0 0 N N (by omega) (by omega) y
  have hleftV := finiteGridVertical_eq_self_of_bounded_edges N 0 up hleft y
  have hrightV := finiteGridVertical_eq_self_of_bounded_edges N N up hright
    (finiteGridHorizontal right 0 0 N y)
  simp only [Nat.zero_add] at hrect
  rw [hrightV, hleftV] at hrect
  exact hrect

end DOZZ.Proofs
