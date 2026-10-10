/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.RandomTestApproximation
public import Mathlib.MeasureTheory.Measure.Continuity

/-! Countably many deterministic test limits permit an outcome-dependent test choice. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Correlated selection from a countable test family preserves convergence in measure.
Finite truncation reduces the assertion to finite-coordinate convergence; the discarded
choice tail vanishes by continuity of the finite source measure. -/
theorem tendstoInMeasure_countable_selection
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℕ → ℝ) (g : Ω → ℕ → ℝ) (choice : Ω → ℕ)
    (hc : Measurable choice)
    (hcoord : ∀ i, TendstoInMeasure P (fun n ω => f n ω i) atTop (fun ω => g ω i)) :
    TendstoInMeasure P (fun n ω => f n ω (choice ω)) atTop (fun ω => g ω (choice ω)) := by
  let select : (k : ℕ) → Ω → Fin (k+1) :=
    fun k ω => ⟨min (choice ω) k, Nat.lt_succ_of_le (min_le_right _ _)⟩
  let a : ℕ → ℕ → Ω → ℝ := fun k n ω => f n ω (select k ω)
  let b : ℕ → Ω → ℝ := fun k ω => g ω (select k ω)
  have hab (k : ℕ) : TendstoInMeasure P (a k) atTop (b k) :=
    tendstoInMeasure_finite_selection P
      (fun n ω (i : Fin (k+1)) => f n ω i) (fun ω (i : Fin (k+1)) => g ω i)
      (select k) (fun i => hcoord i)
  let S : ℕ → Set Ω := fun k => {ω | k < choice ω}
  have hS (k : ℕ) : MeasurableSet (S k) := measurableSet_lt measurable_const hc
  have hanti : Antitone S := by
    intro i j hij ω hω
    exact lt_of_le_of_lt hij hω
  have hempty : (⋂ k, S k) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (lt_irrefl (choice ω)) ((mem_iInter.mp hω) (choice ω))
  have he : Tendsto (fun k => P (S k)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (fun k => (hS k).nullMeasurableSet)
      hanti ⟨0, measure_ne_top P _⟩
    simpa only [Function.comp_def, hempty, measure_empty] using h
  apply tendstoInMeasure_uniform_approximation P _ _ a b hab
  intro ε hε
  refine ⟨fun k => P (S k), he, ?_, ?_⟩
  · intro k n
    apply measure_mono
    intro ω hω
    by_contra hn
    have hle : choice ω ≤ k := le_of_not_gt hn
    have hsame : (select k ω : ℕ) = choice ω := min_eq_left hle
    change ε ≤ ‖f n ω (choice ω) - f n ω (select k ω)‖ at hω
    rw [hsame, sub_self, norm_zero] at hω
    exact (not_le_of_gt hε) hω
  · intro k
    apply measure_mono
    intro ω hω
    by_contra hn
    have hle : choice ω ≤ k := le_of_not_gt hn
    have hsame : (select k ω : ℕ) = choice ω := min_eq_left hle
    change ε ≤ ‖g ω (select k ω) - g ω (choice ω)‖ at hω
    rw [hsame, sub_self, norm_zero] at hω
    exact (not_le_of_gt hε) hω


end DOZZ.Proofs
