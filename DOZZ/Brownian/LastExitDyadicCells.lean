/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.LastExitAvoidance
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Deterministic dyadic cells for the last-exit shift

The last-exit dyadic approximation uses a random last-exit time only to select a cell. Within
each cell its right endpoint is a deterministic mesh point. This module records that partition
and the endpoint identity needed when applying the deterministic-time avoidance formula cell by
cell.
-/

@[expose] public section

open Set
open Function
open scoped NNReal

namespace DOZZ.Proofs

/-- The half-open dyadic cell indexed by the integer part of `2^n L`. -/
def dyadicLastExitCell (n k : ℕ) : Set ℝ≥0 :=
  {L | Nat.floor ((L : ℝ) * (2 : ℝ) ^ n) = k}

/-- The floor-indexed definition is exactly the usual left-closed, right-open dyadic interval. -/
theorem mem_dyadicLastExitCell_iff_interval (n k : ℕ) (L : ℝ≥0) :
    L ∈ dyadicLastExitCell n k ↔
      ((k : ℝ) / (2 : ℝ) ^ n) ≤ (L : ℝ) ∧
        (L : ℝ) < ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n := by
  change Nat.floor ((L : ℝ) * (2 : ℝ) ^ n) = k ↔ _
  have ha : 0 < (2 : ℝ) ^ n := by positivity
  have harg : 0 ≤ (L : ℝ) * (2 : ℝ) ^ n := by positivity
  rw [Nat.floor_eq_iff harg]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · rw [div_le_iff₀ ha]
      exact hlo
    · rw [lt_div_iff₀ ha]
      push_cast at hhi ⊢
      exact hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · rw [div_le_iff₀ ha] at hlo
      exact hlo
    · rw [lt_div_iff₀ ha] at hhi
      push_cast at hhi ⊢
      exact hhi





/-- On a fixed dyadic cell the random last-exit ceiling is one deterministic mesh endpoint. -/
theorem dyadicLastExitCeilingTime_eq_of_mem_cell
    (n k : ℕ) (L : ℝ≥0) (hL : L ∈ dyadicLastExitCell n k) :
    dyadicLastExitCeilingTime n L =
      ⟨((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n, by positivity⟩ := by
  apply Subtype.ext
  simp only [dyadicLastExitCeilingTime, dyadicLastExitCell, Set.mem_ofPred_eq] at hL ⊢
  rw [hL]

/-- A last-exit dyadic cell is determined by deterministic-time visit information: the path
visits the level at or after the left endpoint, and has no visit at or after the right endpoint.
The last exit is never used as a Markov time. -/
theorem negativeLastExitTime_mem_Ico_iff_deterministic_visits
    (p : BrownianPath) (c : ℝ) (a b : ℝ≥0)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    negativeLastExitTime p c ∈ Set.Ico a b ↔
      (∃ u : ℝ≥0, a ≤ u ∧ p u = -c) ∧
        ∀ u : ℝ≥0, b ≤ u → p u ≠ -c := by
  let A : Set ℝ≥0 := {u | p u = -c}
  have hlast : p (negativeLastExitTime p c) = -c :=
    negativeLastExitTime_mem_of_nonempty_bddAbove p c hnonempty hbounded
  constructor
  · intro h
    have hleft : a ≤ negativeLastExitTime p c := h.1
    have hright : negativeLastExitTime p c < b := h.2
    refine ⟨⟨negativeLastExitTime p c, hleft, hlast⟩, ?_⟩
    intro u hu hhit
    have huL : u ≤ negativeLastExitTime p c := le_csSup hbounded hhit
    exact (not_le_of_gt hright) (le_trans hu huL)
  · rintro ⟨⟨u, hau, hhit⟩, havoid⟩
    constructor
    · exact hau.trans (le_csSup hbounded hhit)
    · by_contra hnot
      have hbL : b ≤ negativeLastExitTime p c := le_of_not_gt hnot
      exact havoid (negativeLastExitTime p c) hbL hlast

end DOZZ.Proofs

end
