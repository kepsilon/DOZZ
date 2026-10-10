/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Tactic.Linarith

/-! Event bounds for the sum of two possibly dependent positive masses. -/

@[expose] public section
open MeasureTheory Set

namespace DOZZ.Proofs

theorem two_mass_tail_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A B : Ω → ℝ) (hB : AEMeasurable B P)
    (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω) (x h : ℝ) :
    P.real {ω | x < A ω} + P.real {ω | x < B ω} -
      P.real {ω | x < A ω ∧ x < B ω} ≤ P.real {ω | x < A ω+B ω} ∧
    P.real {ω | x < A ω+B ω} ≤
      P.real {ω | x-h < A ω} + P.real {ω | x-h < B ω} +
        P.real {ω | h < A ω ∧ h < B ω} := by
  constructor
  · have hi : {ω | x < A ω} ∪ {ω | x < B ω} ⊆ {ω | x < A ω+B ω} := by
      intro ω hω
      rcases hω with hω | hω
      · exact lt_of_lt_of_le hω (le_add_of_nonneg_right (hB0 ω))
      · exact lt_of_lt_of_le hω (le_add_of_nonneg_left (hA0 ω))
    have hm := measureReal_mono hi (μ := P)
    have hu := measureReal_union_add_inter₀ (μ := P)
      (s := {ω | x < A ω}) (nullMeasurableSet_lt aemeasurable_const hB)
    change P.real ({ω | x < A ω} ∪ {ω | x < B ω}) +
      P.real {ω | x < A ω ∧ x < B ω} = _ at hu
    linarith only [hm,hu]
  · have hi : {ω | x < A ω+B ω} ⊆
        ({ω | x-h < A ω} ∪ {ω | x-h < B ω}) ∪ {ω | h < A ω ∧ h < B ω} := by
      intro ω hω
      by_cases ha : x-h < A ω
      · exact Or.inl (Or.inl ha)
      by_cases hb : x-h < B ω
      · exact Or.inl (Or.inr hb)
      · exact Or.inr ⟨by dsimp at *; linarith, by dsimp at *; linarith⟩
    have hm := measureReal_mono hi (μ := P)
    have h1 := measureReal_union_le (μ := P)
      ({ω | x-h < A ω} ∪ {ω | x-h < B ω}) {ω | h < A ω ∧ h < B ω}
    have h2 := measureReal_union_le (μ := P) {ω | x-h < A ω} {ω | x-h < B ω}
    linarith only [hm,h1,h2]

/-- Marginal tail approximations and joint exceedances control the sum tail. -/
theorem two_mass_tail_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A B : Ω → ℝ) (hB : AEMeasurable B P)
    (hA0 : ∀ ω, 0 ≤ A ω) (hB0 : ∀ ω, 0 ≤ B ω) (x h L₁ L₂ e₁ e₂ j : ℝ)
    (hlo₁ : |P.real {ω | x < A ω}-L₁| ≤ e₁)
    (hlo₂ : |P.real {ω | x < B ω}-L₂| ≤ e₂)
    (hhi₁ : |P.real {ω | x-h < A ω}-L₁| ≤ e₁)
    (hhi₂ : |P.real {ω | x-h < B ω}-L₂| ≤ e₂)
    (hjx : P.real {ω | x < A ω ∧ x < B ω} ≤ j)
    (hjh : P.real {ω | h < A ω ∧ h < B ω} ≤ j) :
    |P.real {ω | x < A ω+B ω}-(L₁+L₂)| ≤ e₁+e₂+j := by
  have hs := two_mass_tail_sandwich P A B hB hA0 hB0 x h
  have h1 := (abs_le.mp hlo₁).1
  have h2 := (abs_le.mp hlo₂).1
  have h3 := (abs_le.mp hhi₁).2
  have h4 := (abs_le.mp hhi₂).2
  apply abs_le.mpr
  constructor <;> linarith only [hs.1,hs.2,h1,h2,h3,h4,hjx,hjh]


end DOZZ.Proofs
