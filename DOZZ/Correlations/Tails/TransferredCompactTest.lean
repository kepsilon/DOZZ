/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.UnpinnedDensity
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! Deterministic compact tests for identifying the translated unpinned GMC. -/

@[expose] public section

open MeasureTheory Set
open scoped CompactlySupported

namespace DOZZ.Proofs

/-- The pin-removal weight applied to a translated compact test is again a compact test. -/
theorem transferred_compact_test (z : ℂ) (γ : ℝ)
    (f : BoundedContinuousFunction ℂ ℝ) (hf : HasCompactSupport (f : ℂ → ℝ)) :
    ∃ g : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (g : ℂ → ℝ) ∧
      ∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)) := by
  let g : ℂ → ℝ := fun w => f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))
  have hc : Continuous g := by
    apply Continuous.mul (f.continuous.comp (continuous_id.sub continuous_const))
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    apply Continuous.log
    · unfold normPlus
      exact continuous_const.max continuous_norm
    · intro w
      have h : 0 < normPlus w := by unfold normPlus; positivity
      exact h.ne'
  have hs : HasCompactSupport (fun w => f (w-z)) := by
    have h := hf.comp_homeomorph (Homeomorph.addRight (-z))
    change HasCompactSupport (fun w => f (w + -z)) at h
    simpa only [sub_eq_add_neg] using h
  have hg : HasCompactSupport g := hs.mul_right
  let gc : C_c(ℂ, ℝ) := ⟨⟨g, hc⟩, hg⟩
  exact ⟨gc.toBoundedContinuousFunction, gc.hasCompactSupport, fun w => rfl⟩


end DOZZ.Proofs
