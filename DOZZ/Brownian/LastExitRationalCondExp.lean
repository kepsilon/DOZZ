/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.LastExitCondExpLimit
public import DOZZ.Statements.Brownian.BrownianPath

/-!
# Conditional-expectation limit along rational avoidance grids

The strict future-avoidance event is the intersection of a decreasing sequence of finite rational
grids. Continuity identifies the all-rational event with real-time avoidance once the separate
no-tangency hypothesis is available; the conditional-expectation limit itself needs no such
probabilistic input.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace DOZZ.Proofs

/-- A surjective enumeration of rational times. -/
noncomputable def lastExitRationalEnumeration : ℕ → ℚ :=
  (exists_surjective_nat ℚ).choose

theorem lastExitRationalEnumeration_surjective :
    Function.Surjective lastExitRationalEnumeration :=
  (exists_surjective_nat ℚ).choose_spec

/-- The path event that a reflected path is strictly above `c` at a rational time `q>t`.
The implication makes the coordinate constraint vacuous when `q≤t`. -/
def rationalFutureAvoidanceCoordinate (t c : ℝ) (ht : 0 ≤ t) (q : ℚ) :
    Set BrownianPath :=
  if hq : t < (q : ℝ) then
    {p | c < -p ⟨(q : ℝ), le_trans ht hq.le⟩}
  else Set.univ

theorem measurableSet_rationalFutureAvoidanceCoordinate
    (t c : ℝ) (ht : 0 ≤ t) (q : ℚ) :
    MeasurableSet (rationalFutureAvoidanceCoordinate t c ht q) := by
  by_cases hq : t < (q : ℝ)
  · simp only [rationalFutureAvoidanceCoordinate, hq]
    let s : ℝ≥0 := ⟨(q : ℝ), le_trans ht hq.le⟩
    change MeasurableSet {p : BrownianPath | c < -(p s)}
    exact measurableSet_lt measurable_const (ContinuousMap.measurable_eval s).neg
  · simp [rationalFutureAvoidanceCoordinate, hq]

/-- Avoidance on the first `n` entries of a fixed rational-time enumeration. -/
def rationalFutureAvoidanceGrid (t c : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    Set BrownianPath :=
  ⋂ k : Fin n, rationalFutureAvoidanceCoordinate t c ht
    (lastExitRationalEnumeration k.val)

/-- The countable rational-time version of strict future avoidance. -/
def rationalFutureAvoidance (t c : ℝ) (ht : 0 ≤ t) : Set BrownianPath :=
  ⋂ q : ℚ, rationalFutureAvoidanceCoordinate t c ht q

theorem measurableSet_rationalFutureAvoidanceGrid
    (t c : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    MeasurableSet (rationalFutureAvoidanceGrid t c ht n) := by
  apply MeasurableSet.iInter
  intro k
  exact measurableSet_rationalFutureAvoidanceCoordinate t c ht
    (lastExitRationalEnumeration k.val)

theorem rationalFutureAvoidanceGrid_antitone
    (t c : ℝ) (ht : 0 ≤ t) :
    Antitone (rationalFutureAvoidanceGrid t c ht) := by
  intro n m hnm
  change (⋂ k : Fin m, rationalFutureAvoidanceCoordinate t c ht
      (lastExitRationalEnumeration k.val)) ⊆
    ⋂ k : Fin n, rationalFutureAvoidanceCoordinate t c ht
      (lastExitRationalEnumeration k.val)
  intro p hp
  simp only [Set.mem_iInter] at hp ⊢
  intro k
  exact hp ⟨k.val, by omega⟩

theorem rationalFutureAvoidance_eq_iInter_grid
    (t c : ℝ) (ht : 0 ≤ t) :
    rationalFutureAvoidance t c ht = ⋂ n : ℕ, rationalFutureAvoidanceGrid t c ht n := by
  ext p
  constructor
  · intro hp
    simp only [rationalFutureAvoidance, Set.mem_iInter] at hp
    simp only [rationalFutureAvoidanceGrid, Set.mem_iInter]
    intro n k
    exact hp (lastExitRationalEnumeration k.val)
  · intro hp
    simp only [rationalFutureAvoidance, Set.mem_iInter]
    intro q
    obtain ⟨k, hkq⟩ := lastExitRationalEnumeration_surjective q
    subst q
    simp only [rationalFutureAvoidanceGrid, Set.mem_iInter] at hp
    let hk : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    have hgrid := hp (k + 1) hk
    simpa [hk] using hgrid


end DOZZ.Proofs

end
