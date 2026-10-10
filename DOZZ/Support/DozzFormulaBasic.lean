/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

/-!
# Elementary facts about the DOZZ definitions

Elementary helper lemmas about `dozzFormula` and about `4/γ²` for irrational `γ²`.
-/

public section

open Complex

namespace DOZZ

/-- The number `4/γ²` is not a natural number when `γ²` is irrational. -/
theorem four_div_sq_ne_nat_of_irrational {γ : ℝ} (hγ : 0 < γ) (h : Irrational (γ ^ 2)) :
    ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ) := by
  intro k hk
  have hγ2 : γ ^ 2 ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by
    intro h0; rw [h0] at hk; exact absurd hk (by positivity)
  apply h
  refine ⟨4 / k, ?_⟩
  push_cast
  field_simp at hk ⊢
  linarith

/-- Symmetry of `C^{DOZZ}` under exchanging `α₁` and `α₂` (see [KRV, §11]). -/
theorem dozzFormula_swap12 (γ μ : ℝ) (U : ℂ → ℂ) (α₁ α₂ α₃ : ℂ) :
    dozzFormula γ μ U α₁ α₂ α₃ = dozzFormula γ μ U α₂ α₁ α₃ := by
  unfold dozzFormula; ring_nf

/-- Symmetry of `C^{DOZZ}` under exchanging `α₂` and `α₃` (see [KRV, §11]). -/
theorem dozzFormula_swap23 (γ μ : ℝ) (U : ℂ → ℂ) (α₁ α₂ α₃ : ℂ) :
    dozzFormula γ μ U α₁ α₂ α₃ = dozzFormula γ μ U α₁ α₃ α₂ := by
  unfold dozzFormula; ring_nf

end DOZZ
