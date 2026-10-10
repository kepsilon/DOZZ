/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeLastExitTime
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.Basic

/-!
# Deterministic-time characterization of a last exit

The last-exit distribution is obtained by asking whether the future visits the level after a
deterministic time. This order-theoretic lemma isolates that event identity; probabilistic
conditioning is then applied at the deterministic time, never at the last exit itself.
-/

@[expose] public section

open Set
open Filter Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- If the set of visits to `-c` is bounded, the last-exit time is at most `t` exactly when the
path does not visit `-c` at any later time. -/
theorem negativeLastExitTime_le_iff_no_future_visit
    (p : BrownianPath) (c : ℝ) (t : ℝ≥0)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    negativeLastExitTime p c ≤ t ↔ ∀ u : ℝ≥0, t < u → p u ≠ -c := by
  rw [negativeLastExitTime]
  let A : Set ℝ≥0 := {u | p u = -c}
  by_cases hA : A.Nonempty
  · constructor
    · intro hlast u htu hu
      have hu_le : u ≤ sSup A := le_csSup hbounded hu
      exact (not_lt_of_ge (hu_le.trans hlast)) htu
    · intro havoid
      apply csSup_le hA
      intro u hu
      by_contra hnot
      exact havoid u (lt_of_not_ge hnot) hu
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    constructor
    · intro _ u _ hu
      exact hA ⟨u, hu⟩
    · intro _
      simp [A, hAempty]

/-- A finite last exit of a continuous path is attained. The hit set is closed, so its supremum
belongs to the set whenever it is nonempty and bounded above. -/
theorem negativeLastExitTime_mem_of_nonempty_bddAbove
    (p : BrownianPath) (c : ℝ)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    p (negativeLastExitTime p c) = -c := by
  let A : Set ℝ≥0 := {u | p u = -c}
  have hclosed : IsClosed A := isClosed_singleton.preimage p.continuous
  have hmem : sSup A ∈ A := hclosed.csSup_mem hnonempty hbounded
  exact hmem

/-- Right endpoint of the dyadic mesh cell strictly containing a nonnegative last-exit time.
The strict upper endpoint convention avoids any ambiguity when the last exit itself is dyadic. -/
noncomputable def dyadicLastExitCeilingTime (n : ℕ) (L : ℝ≥0) : ℝ≥0 :=
  ⟨((Nat.floor ((L : ℝ) * (2 : ℝ) ^ n) + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n, by positivity⟩

/-- The deterministic dyadic ceiling lies strictly after `L` and less than one mesh width
after it. Thus it converges to `L`; each ceiling is a deterministic time on its corresponding
mesh cell. -/
theorem dyadicLastExitCeilingTime_bounds (n : ℕ) (L : ℝ≥0) :
    (L : ℝ) < (dyadicLastExitCeilingTime n L : ℝ) ∧
      (dyadicLastExitCeilingTime n L : ℝ) ≤ (L : ℝ) + 1 / (2 : ℝ) ^ n := by
  let a : ℝ := (2 : ℝ) ^ n
  have ha : 0 < a := by positivity
  have hfloor_le : (Nat.floor ((L : ℝ) * a) : ℝ) ≤ (L : ℝ) * a :=
    Nat.floor_le (by positivity)
  have hlt : (L : ℝ) * a < (Nat.floor ((L : ℝ) * a) : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one ((L : ℝ) * a)
  constructor
  · change (L : ℝ) <
      ((Nat.floor ((L : ℝ) * a) + 1 : ℕ) : ℝ) / a
    push_cast
    rw [lt_div_iff₀ ha]
    exact hlt
  · change ((Nat.floor ((L : ℝ) * a) + 1 : ℕ) : ℝ) / a ≤
      (L : ℝ) + 1 / a
    rw [div_le_iff₀ ha]
    push_cast
    rw [show ((L : ℝ) + 1 / a) * a = (L : ℝ) * a + 1 by
      field_simp [ha.ne']]
    linarith

/-- The deterministic dyadic ceiling times converge to the given nonnegative time. -/
theorem dyadicLastExitCeilingTime_coe_tendsto (L : ℝ≥0) :
    Tendsto (fun n : ℕ => (dyadicLastExitCeilingTime n L : ℝ)) atTop (𝓝 (L : ℝ)) := by
  have hmesh : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [one_div_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  have hupper : Tendsto (fun n : ℕ => (L : ℝ) + 1 / (2 : ℝ) ^ n)
      atTop (𝓝 (L : ℝ)) := by
    simpa using tendsto_const_nhds.add hmesh
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun n => (dyadicLastExitCeilingTime_bounds n L).1.le)
    (fun n => (dyadicLastExitCeilingTime_bounds n L).2)

/-- Evaluating a continuous path at the deterministic dyadic ceilings of its finite last exit
converges to the barrier value at the last exit. -/
theorem continuousPath_dyadicLastExitCeiling_eval_tendsto
    (p : BrownianPath) (c : ℝ)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    Tendsto
      (fun n : ℕ => p (dyadicLastExitCeilingTime n (negativeLastExitTime p c)))
      atTop (𝓝 (-c)) := by
  let L : ℝ≥0 := negativeLastExitTime p c
  have hlast : p L = -c := negativeLastExitTime_mem_of_nonempty_bddAbove p c
    hnonempty hbounded
  have hL : 0 ≤ (L : ℝ) := L.property
  let F : ℝ → ℝ := fun x => p ⟨max x 0, le_max_right x 0⟩
  have hF : Continuous F := by
    apply p.continuous.comp
    exact (continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk
      (fun x => le_max_right x 0)
  have hFL : F (L : ℝ) = p L := by
    change p ⟨max (L : ℝ) 0, le_max_right _ _⟩ = p L
    congr 1
    exact Subtype.ext (max_eq_left hL)
  have htime := dyadicLastExitCeilingTime_coe_tendsto L
  have hcomp : Tendsto (fun n : ℕ => F (dyadicLastExitCeilingTime n L : ℝ))
      atTop (𝓝 (p L)) := by
    rw [← hFL]
    exact (hF.tendsto (L : ℝ)).comp htime
  have heval (n : ℕ) :
      F (dyadicLastExitCeilingTime n L : ℝ) =
        p (dyadicLastExitCeilingTime n L) := by
    change p ⟨max (dyadicLastExitCeilingTime n L : ℝ) 0, le_max_right _ _⟩ = _
    congr 1
    exact Subtype.ext (max_eq_left (dyadicLastExitCeilingTime n L).property)
  simpa [hlast, heval] using hcomp

end DOZZ.Proofs

end
