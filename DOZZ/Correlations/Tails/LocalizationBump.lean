/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! A common compact localization, equal to one on a smaller insertion ball. -/

@[expose] public section
open Set Metric

namespace DOZZ.Proofs

theorem localization_bump (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ χ : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (χ : ℂ → ℝ) ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport (χ : ℂ → ℝ) ⊆ ball 0 ρ ∧
      ∀ x ∈ closedBall (0 : ℂ) (ρ/4), χ x = 1 := by
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := ρ/4, rOut := ρ/2,
      rIn_pos := by positivity,
      rIn_lt_rOut := by linarith only [hρ] }
  let χ := BoundedContinuousFunction.ofNormedAddCommGroup (b : ℂ → ℝ)
    b.continuous 1 (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg b.nonneg]
      exact b.le_one)
  refine ⟨χ,b.hasCompactSupport,fun x => ⟨b.nonneg,b.le_one⟩,?_,?_⟩
  · change tsupport (b : ℂ → ℝ) ⊆ ball 0 ρ
    rw [b.tsupport_eq]
    exact closedBall_subset_ball (by dsimp [b]; linarith only [hρ])
  · intro x hx
    exact b.one_of_mem_closedBall hx


end DOZZ.Proofs
