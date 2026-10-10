/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitFinite
public import DOZZ.Brownian.LastExitEntranceTail
import Mathlib.Topology.Basic

/-!
# The conditioned path stays above the barrier after its last exit

The entrance state escapes every fixed lower interval in probability at deterministic integer
times. Thus it cannot stay below a fixed level forever. Combined with continuity and the finite
last-exit property, this determines the side of the barrier occupied after the last exit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- The positive coordinate lies below `c` at all sufficiently late positive integer times. -/
def conditionedPositiveEventuallyBelow (c : ℝ) : Set BrownianPath :=
  {p | ∃ N : ℕ, ∀ n : ℕ, N ≤ n → -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ c}

private def conditionedPositiveBelowAfter (c : ℝ) (N : ℕ) : Set BrownianPath :=
  {p | ∀ n : ℕ, N ≤ n → -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ c}

/-- Deterministic-time entrance tails rule out being below a fixed positive level eventually. -/
theorem conditionedPositiveEventuallyBelow_measure_zero
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) (c : ℝ) (hc : 0 < c) :
    P (conditionedPositiveEventuallyBelow c) = 0 := by
  let : IsProbabilityMeasure P := hP.2.1
  have htime : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ≥0)) atTop atTop).comp
        (tendsto_add_atTop_nat 1)
  have htail :=
    (conditionedPositiveStateAt_measureReal_Iic_tendsto_zero_atTop hP hν c hc).comp htime
  have hzero (N : ℕ) : P (conditionedPositiveBelowAfter c N) = 0 := by
    let E := conditionedPositiveBelowAfter c N
    have hconst : Tendsto (fun _ : ℕ => P.real E) atTop (𝓝 (P.real E)) :=
      tendsto_const_nhds
    have hbound : ∀ᶠ n : ℕ in atTop, P.real E ≤
        P.real {p | -(p ((n + 1 : ℕ) : ℝ≥0)) ≤ c} := by
      filter_upwards [eventually_ge_atTop N] with n hn
      exact measureReal_mono (fun p hp => hp n hn)
    have hlim : Tendsto (fun _ : ℕ => P.real E) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le'
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
        htail
        (Filter.Eventually.of_forall fun _ => measureReal_nonneg)
        hbound
    have hreal : P.real E = 0 := tendsto_nhds_unique hconst hlim
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hreal
  have hnull : P (⋃ N : ℕ, conditionedPositiveBelowAfter c N) = 0 :=
    measure_iUnion_null hzero
  have heq : conditionedPositiveEventuallyBelow c =
      ⋃ N : ℕ, conditionedPositiveBelowAfter c N := by
    ext p
    simp [conditionedPositiveEventuallyBelow, conditionedPositiveBelowAfter]
  simpa [heq] using hnull

/-- Almost surely, every time strictly after the last visit to `-c` has positive coordinate
strictly above `c`. The proof uses only deterministic-time tails and path continuity. -/
theorem ae_negativeConditionedPath_above_after_lastExit
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    ∀ᵐ p ∂P, ∀ t : ℝ≥0,
      negativeLastExitTime p (c : ℝ) < t → (c : ℝ) < -(p t) := by
  have hgood := ae_negativeConditionedLevelHitSet_nonempty_bddAbove
    hP hB hν c hc
  have hnotlow := conditionedPositiveEventuallyBelow_measure_zero hP hν (c : ℝ) hc
  have hnotlowAE : ∀ᵐ p ∂P, p ∉ conditionedPositiveEventuallyBelow (c : ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp hnotlow
  filter_upwards [hgood, hnotlowAE] with p hp hpn
  rcases hp with ⟨hnonempty, hbounded⟩
  have hlast : p (negativeLastExitTime p (c : ℝ)) = -(c : ℝ) :=
    negativeLastExitTime_mem_of_nonempty_bddAbove p (c : ℝ) hnonempty hbounded
  have hnohit : ∀ u : ℝ≥0, negativeLastExitTime p (c : ℝ) < u →
      p u ≠ -(c : ℝ) := by
    intro u hu hpu
    have huL : u ≤ negativeLastExitTime p (c : ℝ) := le_csSup hbounded hpu
    exact (not_le_of_gt hu) huL
  intro t ht
  by_contra hnot
  have hle : -(p t) ≤ (c : ℝ) := le_of_not_gt hnot
  have hlt : -(p t) < (c : ℝ) := by
    by_contra heq
    have hval : p t = -(c : ℝ) := by linarith
    exact hnohit t ht hval
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  have hEventually : p ∈ conditionedPositiveEventuallyBelow (c : ℝ) := by
    refine ⟨N, fun n hn => ?_⟩
    let T : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0)
    have htT : t ≤ T := by
      apply NNReal.coe_le_coe.mp
      have hNreal : (t : ℝ) < (N : ℝ) := hN
      have hnreal : (N : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_trans hn (Nat.le_succ n)
      dsimp [T]
      exact hNreal.le.trans hnreal
    by_contra hT
    have hTgt : (c : ℝ) < -(p T) := lt_of_not_ge hT
    let f : ℝ≥0 → ℝ := fun s => -(p s)
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc
      (a := t) (b := T) (f := f) htT p.continuous.neg.continuousOn
      ⟨hlt.le, hTgt.le⟩
    have hhit : p u = -(c : ℝ) := by
      have hneg := congrArg (fun x : ℝ => -x) hfu
      simpa [f] using hneg
    have htu : t ≤ u := hu.1
    exact hnohit u (lt_of_lt_of_le ht htu) hhit
  exact hpn hEventually

end DOZZ.Proofs

end
