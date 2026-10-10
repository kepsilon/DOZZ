/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A single integer coarse scale for a diagonal cutoff and both regularization radii. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A floor-log scale controls the root separation and both cutoffs at once, while retaining the
strict one-unit logarithmic slack used by the admissible two-root barrier estimate. -/
theorem exists_floor_log_coarse_scale
    (ρ d ε δ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hd : d ≤ ρ) (hε : ε ≤ ρ) (hδ : δ ≤ ρ) :
    ∃ k : ℕ,
      d ≤ Real.exp (-(k : ℝ)) ∧
      ε ≤ Real.exp (-(k : ℝ)) ∧
      δ ≤ Real.exp (-(k : ℝ)) ∧
      Real.log (1 / ρ) - 1 < (k : ℝ) := by
  have hdiv : 1 ≤ 1 / ρ := by
    rw [one_le_div₀ hρ]
    exact hρ1
  have ht : 0 ≤ Real.log (1 / ρ) := Real.log_nonneg hdiv
  let k : ℕ := ⌊Real.log (1 / ρ)⌋₊
  have hkfloor : (k : ℝ) ≤ Real.log (1 / ρ) := by
    dsimp [k]
    exact Nat.floor_le ht
  have hlogexp : Real.exp (-(Real.log (1 / ρ))) = ρ := by
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < (1 / ρ : ℝ))]
    field_simp
  have hρscale : ρ ≤ Real.exp (-(k : ℝ)) := by
    rw [← hlogexp]
    exact Real.exp_le_exp.mpr (by linarith)
  have hfloor : Real.log (1 / ρ) - 1 < (k : ℝ) := by
    have hlt := Nat.lt_floor_add_one (Real.log (1 / ρ))
    linarith
  exact ⟨k, hd.trans hρscale, hε.trans hρscale, hδ.trans hρscale, hfloor⟩

end DOZZ.Proofs
