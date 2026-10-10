/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TwoMassTailSandwich

/-! Keep one threshold of order x in the two-insertion remainder event. -/

@[expose] public section
open MeasureTheory Set

namespace DOZZ.Proofs

theorem two_mass_tail_half_threshold
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A B : Ω → ℝ) (x h : ℝ) :
    P.real {ω | x < A ω+B ω} ≤
      P.real {ω | x-h < A ω} + P.real {ω | x-h < B ω} +
        (P.real {ω | x/2 < A ω ∧ h < B ω} +
          P.real {ω | h < A ω ∧ x/2 < B ω}) := by
  let E₁ := {ω | x-h < A ω}
  let E₂ := {ω | x-h < B ω}
  let J₁ := {ω | x/2 < A ω ∧ h < B ω}
  let J₂ := {ω | h < A ω ∧ x/2 < B ω}
  have hi : {ω | x < A ω+B ω} ⊆ (E₁ ∪ E₂) ∪ (J₁ ∪ J₂) := by
    intro ω hω
    by_cases ha : x-h < A ω
    · exact Or.inl (Or.inl ha)
    by_cases hb : x-h < B ω
    · exact Or.inl (Or.inr hb)
    by_cases hx : x/2 < A ω
    · exact Or.inr (Or.inl ⟨hx,by dsimp at *; linarith⟩)
    · exact Or.inr (Or.inr ⟨by dsimp at *; linarith,by dsimp at *; linarith⟩)
  have hm := measureReal_mono hi (μ := P)
  have h1 := measureReal_union_le (μ := P) (E₁ ∪ E₂) (J₁ ∪ J₂)
  have h2 := measureReal_union_le (μ := P) E₁ E₂
  have h3 := measureReal_union_le (μ := P) J₁ J₂
  linarith only [hm,h1,h2,h3]


end DOZZ.Proofs
