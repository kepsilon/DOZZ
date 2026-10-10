/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Assembly.CircleGMCExists
public import DOZZ.Upsilon.Continuation
/-! # Characterized parameter families through an arbitrary supplied model -/
public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- GMC existence supplies a subcritical family taking the prescribed value at the current parameter. -/
theorem roots_GMC_family_through {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : ℝ → Ω → Measure ℂ, N γ = M ∧
      ∀ g, 0 < g → g < 2 → IsGMCOf P X g (N g) := by
  classical
  have hex : ∀ g ∈ Ioo (0 : ℝ) 2, ∃ N : Ω → Measure ℂ, IsGMCOf P X g N := by
    intro g hg
    obtain ⟨Xc, N, _hc, hN⟩ := equatorGFF_circle_average_GMC_exists P X hX g hg.1 hg.2
    exact ⟨N, hN⟩
  let N := fun g : ℝ => if hg : g ∈ Ioo (0 : ℝ) 2 then Classical.choose (hex g hg) else fun _ => 0
  refine ⟨fun g => if g = γ then M else N g, by simp only [ite_true], ?_⟩
  intro g hg hg2
  by_cases he : g = γ
  · subst g
    simpa only [ite_true] using hM
  · simp only [ite_eq_right he, N, dite_eq_left (show g ∈ Ioo (0 : ℝ) 2 from ⟨hg, hg2⟩)]
    exact Classical.choose_spec (hex g ⟨hg, hg2⟩)
/-- Upsilon existence supplies a subcritical family taking the prescribed entire function at gamma. -/
theorem roots_Upsilon_family_through (γ : ℝ) (U : ℂ → ℂ) (hU : IsUpsilon γ U) :
    ∃ V : ℝ → ℂ → ℂ, V γ = U ∧ ∀ g ∈ Ioo (0 : ℝ) 2, IsUpsilon g (V g) := by
  classical
  let V := fun g : ℝ => if hg : g ∈ Ioo (0 : ℝ) 2 then
    Classical.choose (exists_IsUpsilon hg.1 hg.2) else fun _ => 0
  refine ⟨fun g => if g = γ then U else V g, by simp only [ite_true], ?_⟩
  intro g hg
  by_cases he : g = γ
  · subst g
    simpa only [ite_true] using hU
  · simp only [ite_eq_right he, V, dite_eq_left hg]
    exact Classical.choose_spec (exists_IsUpsilon hg.1 hg.2)
end DOZZ.Proofs
