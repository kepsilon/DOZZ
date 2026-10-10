/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FreezingAnnulusNegativeMomentLocal
public import DOZZ.FourPoint.FreezingAnnulusNegativeMoment
import Mathlib.Tactic

/-! # The freezing input at the actual reflected charge and order

The freezing estimate and the first-order error at charge `α₁ + γ/2` and order `p + 1`. The local
and exterior versions follow from `freezing_annulus_negative_moment_local` and
`freezing_annulus_negative_moment` with their literal thresholds.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The reflected supercritical charge satisfies the full freezing-order threshold. -/
theorem reflected_freezing_margins (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hα₁ : α₁ < Q γ) (hreflect : Q γ - α₁ < γ / 2)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    Q γ < α₁ + γ / 2 ∧
      0 < (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1 ∧
      α₁ + γ / 2 - Q γ <
        γ * ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1) := by
  have hp : 0 < (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ :=
    div_pos (by linarith only [hs]) hγ
  have he : γ * ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1) =
      (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) + γ := by
    rw [mul_add, mul_div_cancel₀ _ hγ.ne', mul_one]
  refine ⟨?_, by linarith only [hp], ?_⟩
  · linarith only [hreflect]
  · rw [he]
    linarith only [hs, hα₁, hγ]

/-- The actual local estimate needed for the buffer and the small-maximum error. -/
theorem reflected_freezing_local_input {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα₁ : α₁ < Q γ)
    (hreflect : Q γ - α₁ < γ / 2)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      (∫⁻ ω, (freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 ε (1 / 2)) ^
        (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P) ≤
      ENNReal.ofReal (C * ε ^ ((α₁ + γ / 2 - Q γ) ^ 2 / 2)) := by
  obtain ⟨hα, hp, ht⟩ := reflected_freezing_margins γ α₁ α₂ α₃ hγ hα₁ hreflect hs
  obtain ⟨C, ε₀, hC, hε₀, hb⟩ := freezing_annulus_negative_moment_local P M X
    γ (α₁ + γ / 2) ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)
    (1 / 2) {0} isCompact_singleton hγ hγ₂ hX hM (by norm_num) hα hp ht
  exact ⟨C, ε₀, hC, hε₀, hb 0 (mem_singleton 0)⟩

end DOZZ.Proofs
