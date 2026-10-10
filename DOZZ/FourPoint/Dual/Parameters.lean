/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Domain
import Mathlib.Tactic

/-! # Nonresonant parameters for the full dual seed domain

The second multiplier uses C₁ at ε. The interval bounds below establish the nonresonance and
`K₂ ≠ 0` conditions (erratum K27, see docs/ERRATA-AND-DEVIATIONS.md) on the entire source domain,
using the physical Gauss parameter theorem `gauss_physical_parameter_range`.
-/

public section

namespace DOZZ.Proofs

/-- The second-channel parameter satisfies C₁ = 1 − (C₀ − A − B). -/
theorem dual_seed_channel_parameter (γ α ε α' : ℝ) (hγ : γ ≠ 0) :
    gaussParameterC γ (2 / γ) ε =
      1 - (gaussParameterC γ (2 / γ) α -
        gaussParameterA γ (2 / γ) α ε α' - gaussParameterB γ (2 / γ) α ε α') := by
  unfold gaussParameterC gaussParameterA gaussParameterB Q
  field_simp
  ring

/-- The first Gauss parameter is one half minus the total deficit divided by γ. -/
theorem dual_seed_parameterA_deficits (γ α ε α' : ℝ) (hγ : γ ≠ 0) :
    gaussParameterA γ (2 / γ) α ε α' =
      1 / 2 - ((Q γ - α) + (Q γ - ε) + (Q γ - α')) / γ := by
  unfold gaussParameterA Q
  field_simp
  ring

/-- All arguments in the two crossing multipliers lie in their strict Gamma intervals. -/
theorem dual_seed_parameter_intervals (γ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α') :
    let A := gaussParameterA γ (2 / γ) α ε α'
    let B := gaussParameterB γ (2 / γ) α ε α'
    let C₀ := gaussParameterC γ (2 / γ) α
    let C₁ := gaussParameterC γ (2 / γ) ε
    0 < A ∧ A < 1 / 2 ∧
      0 < B ∧ B < 1 ∧ 0 < C₀ ∧ C₀ < 1 ∧ 0 < C₁ ∧ C₁ < 1 ∧
      -1 < A + B - C₀ ∧ A + B - C₀ < 0 ∧
      -1 < C₁ - 1 ∧ C₁ - 1 < 0 ∧
      1 < C₁ - A - B + 1 ∧ C₁ - A - B + 1 < 2 ∧
      0 < C₁ - A ∧ C₁ - A < 1 ∧ 0 < C₁ - B ∧ C₁ - B < 1 ∧
      0 < gaussK₂ A B C₀ := by
  dsimp only
  obtain ⟨hA, hAB, hBC, hC, hδ, hδ₁, _, hK₂⟩ :=
    DOZZ.gauss_physical_parameter_range γ (2 / γ) α ε α'
      hγ hγ₂ (Or.inr rfl) hs hα hε hα'
  have hC₁ := dual_seed_channel_parameter γ α ε α' hγ.ne'
  have hAhalf : gaussParameterA γ (2 / γ) α ε α' < 1 / 2 := by
    rw [dual_seed_parameterA_deficits γ α ε α' hγ.ne']
    have ht : 0 < ((Q γ - α) + (Q γ - ε) + (Q γ - α')) / γ :=
      div_pos (add_pos (add_pos (sub_pos.mpr hα) (sub_pos.mpr hε))
        (sub_pos.mpr hα')) hγ
    linarith only [ht]
  refine ⟨hA, hAhalf, ?_, ?_, ?_, hC, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, hK₂⟩ <;>
    linarith only [hA, hAB, hBC, hC, hδ, hδ₁, hC₁]


end DOZZ.Proofs
