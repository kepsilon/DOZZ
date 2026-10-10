/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.Correlations.Symmetry.ReflectionMomentSwap
import DOZZ.Correlations.Residue.FullFromUnit
/-! # The strict dual fusion window inside the first-case charge box -/
public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- Shrinking around a fixed pair handles the endpoint eta = gamma/4. -/
theorem dualFirstCase_shrink (γ η a₂ a₃ : ℝ) (hη : 0 < η ∧ γ < Q γ - 2 * η)
    (hsmall : η ≤ γ / 4) (h₂ : Q γ - η < a₂ ∧ a₂ < Q γ)
    (h₃ : Q γ - η < a₃ ∧ a₃ < Q γ) :
    ∃ e : ℝ, 0 < e ∧ e < η ∧ e < γ / 4 ∧ γ < Q γ - 2 * e ∧
      (Q γ - e < a₂ ∧ a₂ < Q γ) ∧ (Q γ - e < a₃ ∧ a₃ < Q γ) := by
  let d := max (Q γ - a₂) (Q γ - a₃)
  have hd : 0 < d := (sub_pos.mpr h₂.2).trans_le (le_max_left _ _)
  have hdη : d < η := max_lt (by linarith only [h₂.1]) (by linarith only [h₃.1])
  refine ⟨(d + η) / 2, by linarith only [hd, hη.1], by linarith only [hdη],
    by linarith only [hdη, hsmall], by linarith only [hdη, hη.2],
    ⟨?_, h₂.2⟩, ⟨?_, h₃.2⟩⟩
  · have := le_max_left (Q γ - a₂) (Q γ - a₃)
    change Q γ - a₂ ≤ d at this
    linarith only [this, hdη]
  · have := le_max_right (Q γ - a₂) (Q γ - a₃)
    change Q γ - a₃ ≤ d at this
    linarith only [this, hdη]
/-- A nonempty interval near Q simultaneously supports the dual fusion and both physical
shifted charges. -/
theorem dualFirstCase_seed_interval (γ e a₂ a₃ : ℝ) (hγ : 0 < γ) (he : e < γ / 4)
    (h₂ : Q γ - e < a₂) (h₃ : Q γ - e < a₃) :
    ∃ lo : ℝ, lo < Q γ ∧ ∀ x : ℝ, lo < x → x < Q γ →
      2 * Q γ + 2 / γ < x + a₂ + a₃ ∧
      (2 * e < x - 2 / γ ∧ x - 2 / γ < Q γ) ∧
      (2 * e < 2 * Q γ - x - 2 / γ ∧ 2 * Q γ - x - 2 / γ < Q γ) := by
  refine ⟨max (max (2 * Q γ + 2 / γ - a₂ - a₃) (2 * e + 2 / γ)) (Q γ - 2 / γ), ?_, ?_⟩
  · apply max_lt
    · apply max_lt
      · unfold Q at *
        linarith only [h₂, h₃, he]
      · unfold Q
        linarith only [he]
    · have : 0 < 2 / γ := div_pos (by norm_num) hγ
      linarith only [this]
  · intro x hx hxQ
    have hsum := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hlo := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have href := lt_of_le_of_lt (le_max_right _ _) hx
    refine ⟨by linarith only [hsum], ⟨by linarith only [hlo], ?_⟩,
      ⟨?_, by linarith only [href]⟩⟩
    · have : 0 < 2 / γ := by positivity
      linarith only [hxQ, this]
    · unfold Q at *
      linarith only [hxQ, he]
/-- Reflection Gamma poles do not occur in the near-Q seed interval. -/
theorem dualFirstCase_poleFree {γ a : ℝ} (hγ : 0 < γ)
    (hlo : Q γ - γ / 2 < a) : ReflectionPoleFree γ a := by
  intro n hn
  have hp : reflectionExponent γ a < 1 := by
    unfold reflectionExponent
    apply (div_lt_iff₀ hγ).mpr
    linarith only [hlo]
  have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  exact (not_lt_of_ge hn1) (hn ▸ hp)
/-- The full structure constant inherits the permutation symmetry of the unit-volume structure
constant (`unitVolumeStructureConstant_swap12`). -/
theorem dualFirstCase_structure_swap12 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ a b c : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    structureConstant P M γ μ a b c = structureConstant P M γ μ b a c := by
  rw [residue_structureConstant_eq_unitVolume, residue_structureConstant_eq_unitVolume,
    unitVolumeStructureConstant_swap12 P X M γ a b c hγ hγ2 hX hM]
  have hs : sExp γ a b c = sExp γ b a c := by unfold sExp; ring
  rw [hs]
end DOZZ.Proofs
