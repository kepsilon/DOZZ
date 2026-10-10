/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianLaw
public import DOZZ.Brownian.LastExitAvoidanceChain

/-!
# Positive-coordinate factorization of conditioned entrance FDDs

The characterization `DOZZ.IsNegativeConditionedBrownianLaw` is stated for negative paths.
Reflecting every coordinate gives the positive entrance law, whose finite-dimensional density is
an entrance density followed by the positive Doob transition chain. This is the explicit density
factorization used in deterministic-time Markov calculations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- The positive conditioned transition chain over an ordered list of absolute observation times.
The initial state is observed at time `t₀`; each later factor uses the elapsed time since the
preceding observation. -/
noncomputable def conditionedPositiveTimeChainDensity (ν t₀ x₀ : ℝ) :
    List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      conditionedPositiveTransitionDensity ν (t - t₀) x₀ x *
        conditionedPositiveTimeChainDensity ν t x ts xs
  | _, _ => 0
termination_by times _ => times.length

/-- The positive-coordinate form of the entrance finite-dimensional density. -/
noncomputable def conditionedPositiveFDDDensity (ν : ℝ) : List ℝ → List ℝ → ℝ
  | [], [] => 1
  | t :: ts, x :: xs =>
      conditionedPositiveEntranceDensity ν t x *
        conditionedPositiveTimeChainDensity ν t x ts xs
  | _, _ => 0

/-- Convert a list of absolute observation times and values into elapsed-time transition steps. -/
noncomputable def conditionedPositiveTimeSteps (t₀ : ℝ) :
    List ℝ → List ℝ → List (ℝ × ℝ)
  | t :: ts, x :: xs =>
      (t - t₀, x) :: conditionedPositiveTimeSteps t ts xs
  | _, _ => []
termination_by times _ => times.length

/-- Reflecting the state and every later coordinate in the negative transition chain gives
exactly the positive Doob transition chain. -/
theorem negativeConditionedTransitionChainDensity_reflect
    (ν t x : ℝ) (times values : List ℝ) :
    negativeConditionedTransitionChainDensity ν t (-x) times (values.map fun y => -y) =
      conditionedPositiveTimeChainDensity ν t x times values := by
  induction times generalizing t x values with
  | nil =>
      cases values <;>
        simp [negativeConditionedTransitionChainDensity,
          conditionedPositiveTimeChainDensity]
  | cons s ss ih =>
      cases values with
      | nil =>
          simp [negativeConditionedTransitionChainDensity,
            conditionedPositiveTimeChainDensity]
      | cons y ys =>
          simp [negativeConditionedTransitionChainDensity,
            conditionedPositiveTimeChainDensity, negativeConditionedTransitionDensity, ih]

/-- The negative entrance density, after reflecting its coordinates, is the explicit
positive entrance density and transition chain. -/
theorem negativeConditionedFDDDensity_reflect
    (ν : ℝ) (times values : List ℝ) :
    negativeConditionedFDDDensity ν times (values.map fun y => -y) =
      conditionedPositiveFDDDensity ν times values := by
  cases times with
  | nil =>
      cases values <;>
        simp [negativeConditionedFDDDensity, conditionedPositiveFDDDensity]
  | cons t ts =>
      cases values with
      | nil =>
          simp [negativeConditionedFDDDensity, conditionedPositiveFDDDensity]
      | cons x xs =>
          simp only [negativeConditionedFDDDensity, conditionedPositiveFDDDensity,
            List.map_cons]
          rw [negativeConditionedTransitionChainDensity_reflect]
          simp

/-- The positive finite-dimensional density factors at its first observation into the entrance
density and the successive transition densities. -/
theorem conditionedPositiveFDDDensity_cons
    (ν t : ℝ) (x : ℝ) (times values : List ℝ) :
    conditionedPositiveFDDDensity ν (t :: times) (x :: values) =
      conditionedPositiveEntranceDensity ν t x *
        conditionedPositiveTimeChainDensity ν t x times values := by
  rfl


/-- The absolute-time transition chain is the pair-list chain of elapsed times and destination
states. -/
theorem conditionedPositiveTimeChainDensity_eq_steps
    (ν t₀ x₀ : ℝ) (times values : List ℝ)
    (hlen : times.length = values.length) :
    conditionedPositiveTimeChainDensity ν t₀ x₀ times values =
      conditionedPositiveChainDensity ν x₀ (conditionedPositiveTimeSteps t₀ times values) := by
  induction times generalizing t₀ x₀ values with
  | nil =>
      cases values with
      | nil => simp [conditionedPositiveTimeChainDensity, conditionedPositiveTimeSteps,
          conditionedPositiveChainDensity]
      | cons y ys => simp at hlen
  | cons t ts ih =>
      cases values with
      | nil => simp at hlen
      | cons y ys =>
          have htail : ts.length = ys.length := by simpa using hlen
          simp only [conditionedPositiveTimeChainDensity, conditionedPositiveTimeSteps,
            conditionedPositiveChainDensity]
          rw [ih t y ys htail]


/-- The final observation time after appending a finite ordered history to a starting time. -/
def conditionedPositiveLastTime (t₀ : ℝ) : List ℝ → ℝ
  | [] => t₀
  | t :: ts => conditionedPositiveLastTime t ts

/-- The final state after appending a finite state history to a starting state. -/
def conditionedPositiveLastState (x₀ : ℝ) : List ℝ → ℝ
  | [] => x₀
  | x :: xs => conditionedPositiveLastState x xs

/-- The absolute-time transition density factors at the final state of a finite past list. -/
theorem conditionedPositiveTimeChainDensity_append
    (ν t₀ x₀ : ℝ) (pastTimes pastValues futureTimes futureValues : List ℝ)
    (hpast : pastTimes.length = pastValues.length) :
    conditionedPositiveTimeChainDensity ν t₀ x₀
        (pastTimes ++ futureTimes) (pastValues ++ futureValues) =
      conditionedPositiveTimeChainDensity ν t₀ x₀ pastTimes pastValues *
        conditionedPositiveTimeChainDensity ν
          (conditionedPositiveLastTime t₀ pastTimes)
          (conditionedPositiveLastState x₀ pastValues) futureTimes futureValues := by
  induction pastTimes generalizing t₀ x₀ pastValues with
  | nil =>
      cases pastValues with
      | nil => simp [conditionedPositiveTimeChainDensity,
          conditionedPositiveLastTime, conditionedPositiveLastState]
      | cons x xs => simp at hpast
  | cons t ts ih =>
      cases pastValues with
      | nil => simp at hpast
      | cons x xs =>
          have htail : ts.length = xs.length := by simpa using hpast
          simp only [List.cons_append, conditionedPositiveTimeChainDensity,
            conditionedPositiveLastTime, conditionedPositiveLastState]
          rw [ih t x xs htail]
          ring

/-- The explicit entrance FDD density splits at the state reached after any finite ordered past.
The right factor is exactly the finite transition density started at that deterministic state. -/
theorem conditionedPositiveFDDDensity_split
    (ν t₀ x₀ : ℝ) (pastTimes pastValues futureTimes futureValues : List ℝ)
    (hpast : pastTimes.length = pastValues.length) :
    conditionedPositiveFDDDensity ν (t₀ :: (pastTimes ++ futureTimes))
        (x₀ :: (pastValues ++ futureValues)) =
      (conditionedPositiveEntranceDensity ν t₀ x₀ *
        conditionedPositiveTimeChainDensity ν t₀ x₀ pastTimes pastValues) *
        conditionedPositiveTimeChainDensity ν
          (conditionedPositiveLastTime t₀ pastTimes)
          (conditionedPositiveLastState x₀ pastValues) futureTimes futureValues := by
  rw [conditionedPositiveFDDDensity_cons,
    conditionedPositiveTimeChainDensity_append ν t₀ x₀ pastTimes pastValues
      futureTimes futureValues hpast]
  ring

/-- Splitting a finite Doob chain at a deterministic observation state factors its density into
the past-chain density and the future-chain density started from that state. -/
theorem conditionedPositiveChainDensity_append
    (ν x : ℝ) (past future : List (ℝ × ℝ)) :
    conditionedPositiveChainDensity ν x (past ++ future) =
      conditionedPositiveChainDensity ν x past *
        conditionedPositiveChainDensity ν (lastExitChainLastState x past) future := by
  induction past generalizing x with
  | nil => simp [conditionedPositiveChainDensity, lastExitChainLastState]
  | cons step past ih =>
      rcases step with ⟨t, y⟩
      simp only [List.cons_append, conditionedPositiveChainDensity, lastExitChainLastState]
      rw [ih y]
      ring


/-- Finite-grid killed-kernel cancellation continues to hold after inserting any cylinder test of
the translated future states. This is the test-function form of the all-grid density identity. -/
theorem conditionedKilledAboveChain_cylinder_avoidance_shift
    (ν c x : ℝ) (hν : 0 < ν) (hc : 0 < c) (hcx : c < x)
    (steps : List (ℝ × ℝ))
    (htimes : ∀ z ∈ steps, 0 < z.1)
    (hstates : ∀ z ∈ steps, c < z.2)
    (G : List ℝ → ℝ) :
    G (steps.map fun z => z.2 - c) *
        (conditionedKilledAboveChainDensity ν c x steps *
          (lastExitAvoidanceFactor ν c (lastExitChainLastState x steps) /
            lastExitAvoidanceFactor ν c x)) =
      G (steps.map fun z => z.2 - c) *
        conditionedPositiveChainDensity ν (x - c)
          (steps.map fun z => (z.1, z.2 - c)) := by
  have hshift := conditionedKilledAboveChain_avoidance_shift ν c x hν hc hcx
    steps htimes hstates
  calc
    G (steps.map fun z => z.2 - c) *
        (conditionedKilledAboveChainDensity ν c x steps *
          (lastExitAvoidanceFactor ν c (lastExitChainLastState x steps) /
            lastExitAvoidanceFactor ν c x)) =
      G (steps.map fun z => z.2 - c) *
        (conditionedPositiveChainDensity ν (x - c)
          (steps.map fun z => (z.1, z.2 - c))) := by rw [hshift]
    _ = _ := rfl


/-- A continuous path stays in the closed half-line `[c,∞)` after `t` exactly when it does so at
all rational times after `t`. For strict avoidance of the boundary, a separate no-tangency result
is needed; continuity alone only gives this closed-barrier statement. -/
theorem continuous_path_ge_iff_rational_ge
    (p : BrownianPath) (t c : ℝ) (ht : 0 ≤ t) :
    (∀ s : ℝ≥0, t < (s : ℝ) → c ≤ p s) ↔
      ∀ q : ℚ, ∀ hq : t < (q : ℝ),
        c ≤ p ⟨(q : ℝ), le_trans ht hq.le⟩ := by
  constructor
  · intro h q hq
    exact h ⟨(q : ℝ), le_trans ht hq.le⟩ hq
  · intro h s hts
    by_contra hnot
    have hbad : p s < c := lt_of_not_ge hnot
    let F : ℝ → ℝ := fun x => p ⟨max x 0, le_max_right _ _⟩
    have hmax : Continuous (fun x : ℝ => max x 0) :=
      continuous_max.comp (continuous_id.prodMk continuous_const)
    have hsub : Continuous (fun x : ℝ =>
        (⟨max x 0, le_max_right _ _⟩ : ℝ≥0)) :=
      hmax.subtype_mk (fun x => le_max_right x 0)
    have hF : Continuous F := p.continuous.comp hsub
    have hsnonneg : (0 : ℝ) ≤ (s : ℝ) := by exact_mod_cast s.2
    have hFs : F (s : ℝ) = p s := by
      change p ⟨max (s : ℝ) 0, le_max_right _ _⟩ = p s
      congr 1
      exact Subtype.ext (max_eq_left hsnonneg)
    let U : Set ℝ := {x | t < x ∧ F x < c}
    have hUopen : IsOpen U := by
      exact isOpen_Ioi.inter (isOpen_Iio.preimage hF)
    have hUnonempty : U.Nonempty := ⟨s, hts, by simpa [hFs] using hbad⟩
    obtain ⟨q, hqU⟩ := Rat.denseRange_cast.exists_mem_open hUopen hUnonempty
    have hqU' : t < (q : ℝ) ∧ F (q : ℝ) < c := hqU
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_trans ht (le_of_lt hqU'.1)
    have hqF : F (q : ℝ) = p ⟨(q : ℝ), hq0⟩ := by
      change p ⟨max (q : ℝ) 0, le_max_right _ _⟩ = p ⟨(q : ℝ), hq0⟩
      congr 1
      exact Subtype.ext (max_eq_left hq0)
    have hqbound := h q hqU'.1
    have hqbelow : p ⟨(q : ℝ), hq0⟩ < c := by
      simpa only [hqF] using hqU'.2
    exact (not_lt_of_ge hqbound) hqbelow

end DOZZ.Proofs

end
