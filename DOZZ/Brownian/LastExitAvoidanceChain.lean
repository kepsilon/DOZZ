/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernel

/-!
# Finite-horizon last-exit kernel cancellation

The deterministic-time avoidance correction telescopes along every finite observation grid.
This is the finite-horizon kernel identity used before taking the all-future avoidance limit in
the post-last-exit argument.
-/

@[expose] public section

namespace DOZZ.Proofs

/-- The killed transition weight along a finite list of time increments and destination states. -/
noncomputable def conditionedKilledAboveChainDensity (ν c x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 1
  | (t, y) :: rest =>
      conditionedKilledAboveDensity ν t c x y *
        conditionedKilledAboveChainDensity ν c y rest

/-- The translated positive Doob transition weight along the same finite observation grid. -/
noncomputable def conditionedPositiveChainDensity (ν x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => 1
  | (t, y) :: rest =>
      conditionedPositiveTransitionDensity ν t x y *
        conditionedPositiveChainDensity ν y rest

/-- The terminal state of a finite transition grid, starting from `x`. -/
def lastExitChainLastState (x : ℝ) : List (ℝ × ℝ) → ℝ
  | [] => x
  | (_, y) :: rest => lastExitChainLastState y rest

theorem lastExitChainLastState_gt_level {c x : ℝ} (hx : c < x)
    (steps : List (ℝ × ℝ)) (hsteps : ∀ z ∈ steps, c < z.2) :
    c < lastExitChainLastState x steps := by
  induction steps generalizing x with
  | nil => simpa [lastExitChainLastState] using hx
  | cons step rest ih =>
      rcases step with ⟨t, y⟩
      have hy : c < y := hsteps (t, y) (by simp)
      have hrest : ∀ z ∈ rest, c < z.2 := by
        intro z hz
        exact hsteps z (by simp [hz])
      exact ih hy hrest

private theorem conditionedH_pos_of_pos {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  have hν0 : ν ≠ 0 := ne_of_gt hν
  unfold conditionedH
  split_ifs with h
  · exact (hν0 h).elim
  have harg : -2 * ν * x < 0 := by nlinarith
  have hexp : Real.exp (-2 * ν * x) < 1 := (Real.exp_lt_one_iff).2 harg
  linarith

private theorem lastExitAvoidanceFactor_pos_of_above
    {ν c y : ℝ} (hν : 0 < ν) (hc : 0 < c) (hcy : c < y) :
    0 < lastExitAvoidanceFactor ν c y := by
  simp [lastExitAvoidanceFactor, hcy]
  exact div_pos
    (conditionedH_pos_of_pos hν (sub_pos.mpr hcy))
    (conditionedH_pos_of_pos hν (lt_trans hc hcy))

/-- On any finite deterministic grid above `c`, multiplying the killed Doob chain by the ratio
of terminal to initial future-avoidance probabilities translates it exactly to the original
positive entrance transition chain. The all-future path-avoidance limit is a separate step. -/
theorem conditionedKilledAboveChain_avoidance_shift
    (ν c x : ℝ) (hν : 0 < ν) (hc : 0 < c) (hcx : c < x)
    (steps : List (ℝ × ℝ))
    (htimes : ∀ z ∈ steps, 0 < z.1)
    (hstates : ∀ z ∈ steps, c < z.2) :
    conditionedKilledAboveChainDensity ν c x steps *
        (lastExitAvoidanceFactor ν c (lastExitChainLastState x steps) /
          lastExitAvoidanceFactor ν c x) =
      conditionedPositiveChainDensity ν (x - c)
        (steps.map (fun z => (z.1, z.2 - c))) := by
  induction steps generalizing x hcx with
  | nil =>
      have hax : lastExitAvoidanceFactor ν c x ≠ 0 :=
        ne_of_gt (lastExitAvoidanceFactor_pos_of_above hν hc hcx)
      simp [conditionedKilledAboveChainDensity, conditionedPositiveChainDensity,
        lastExitChainLastState, hax]
  | cons step rest ih =>
      rcases step with ⟨t, y⟩
      have ht : 0 < t := htimes (t, y) (by simp)
      have hcy : c < y := hstates (t, y) (by simp)
      have htimes' : ∀ z ∈ rest, 0 < z.1 := by
        intro z hz
        exact htimes z (by simp [hz])
      have hstates' : ∀ z ∈ rest, c < z.2 := by
        intro z hz
        exact hstates z (by simp [hz])
      have hy : c < lastExitChainLastState y rest :=
        lastExitChainLastState_gt_level hcy rest hstates'
      have hax : lastExitAvoidanceFactor ν c x ≠ 0 :=
        ne_of_gt (lastExitAvoidanceFactor_pos_of_above hν hc hcx)
      have hay : lastExitAvoidanceFactor ν c y ≠ 0 :=
        ne_of_gt (lastExitAvoidanceFactor_pos_of_above hν hc hcy)
      have halast :
          lastExitAvoidanceFactor ν c (lastExitChainLastState y rest) ≠ 0 :=
        ne_of_gt (lastExitAvoidanceFactor_pos_of_above hν hc hy)
      have hxH : conditionedH ν x ≠ 0 :=
        ne_of_gt (conditionedH_pos_of_pos hν (lt_trans hc hcx))
      have hyH : conditionedH ν y ≠ 0 :=
        ne_of_gt (conditionedH_pos_of_pos hν (lt_trans hc hcy))
      have hxcH : conditionedH ν (x - c) ≠ 0 :=
        ne_of_gt (conditionedH_pos_of_pos hν (sub_pos.mpr hcx))
      have hycH : conditionedH ν (y - c) ≠ 0 :=
        ne_of_gt (conditionedH_pos_of_pos hν (sub_pos.mpr hcy))
      have hstep := conditionedKilledAboveDensity_avoidance_shift
        ν t c x y hν ht hcx hcy hxH hyH hxcH hycH
      have htail := ih y hcy htimes' hstates'
      simp only [conditionedKilledAboveChainDensity, conditionedPositiveChainDensity,
        lastExitChainLastState, List.map_cons]
      calc
        (conditionedKilledAboveDensity ν t c x y *
              conditionedKilledAboveChainDensity ν c y rest) *
            (lastExitAvoidanceFactor ν c (lastExitChainLastState y rest) /
              lastExitAvoidanceFactor ν c x) =
          (conditionedKilledAboveDensity ν t c x y *
              (lastExitAvoidanceFactor ν c y / lastExitAvoidanceFactor ν c x)) *
            (conditionedKilledAboveChainDensity ν c y rest *
              (lastExitAvoidanceFactor ν c (lastExitChainLastState y rest) /
                lastExitAvoidanceFactor ν c y)) := by
                  field_simp [hax, hay, halast]
        _ = conditionedPositiveTransitionDensity ν t (x - c) (y - c) *
            conditionedPositiveChainDensity ν (y - c)
              (rest.map (fun z => (z.1, z.2 - c))) := by
                rw [hstep, htail]
        _ = conditionedPositiveChainDensity ν (x - c)
            ((t, y - c) :: rest.map (fun z => (z.1, z.2 - c))) := rfl

end DOZZ.Proofs

end
