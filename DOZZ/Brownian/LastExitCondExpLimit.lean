/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Conditional-expectation limits for finite-grid avoidance

This module isolates the dominated-convergence step in the deterministic-time last-exit argument.
Decreasing finite-grid avoidance tests converge in conditional expectation in `L¹` to the
all-future avoidance test.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ.Proofs

/-- Conditional expectations of a boundedly dominated test, restricted to a decreasing sequence
of measurable events, converge in `L¹` to the conditional expectation on their intersection. -/
theorem tendsto_condExpL1_indicator_of_antitone
    {Ω : Type*} [measΩ : MeasurableSpace Ω] (μ : Measure Ω)
    {m : MeasurableSpace Ω} (hm : m ≤ measΩ) [SigmaFinite (μ.trim hm)]
    (G : Ω → ℝ) (hG : Integrable G μ)
    (A : ℕ → Set Ω) (hA : ∀ n, @MeasurableSet Ω measΩ (A n)) (hanti : Antitone A) :
    Tendsto (fun n => @condExpL1 Ω ℝ _ _ m measΩ hm μ _
      ((A n).indicator G)) atTop
      (𝓝 (@condExpL1 Ω ℝ _ _ m measΩ hm μ _
        ((⋂ n : ℕ, A n).indicator G))) := by
  let Ainf : Set Ω := ⋂ n : ℕ, A n
  let f : Ω → ℝ := Ainf.indicator G
  have hfn_int (n : ℕ) : Integrable ((A n).indicator G) μ := hG.indicator (hA n)
  have hfn_meas (n : ℕ) :
      @AEStronglyMeasurable Ω ℝ _ measΩ measΩ ((A n).indicator G) μ :=
    (hfn_int n).1
  have hbound : Integrable (fun ω => ‖G ω‖) μ := hG.norm
  have hfn_bound (n : ℕ) : ∀ᵐ ω ∂μ, ‖(A n).indicator G ω‖ ≤ ‖G ω‖ := by
    filter_upwards with ω
    by_cases hω : ω ∈ A n
    · simp [Set.indicator_of_mem hω]
    · simp [Set.indicator_of_notMem hω]
  have hpoint (ω : Ω) :
      Tendsto (fun n => (A n).indicator G ω) atTop (𝓝 (f ω)) := by
    by_cases hall : ∀ n, ω ∈ A n
    · have hseq : (fun n => (A n).indicator G ω) = fun _ => G ω := by
        funext n
        simp [Set.indicator_of_mem (hall n)]
      have hlim : f ω = G ω := by
        have hωAinf : ω ∈ Ainf := Set.mem_iInter.mpr hall
        change Ainf.indicator G ω = G ω
        exact Set.indicator_of_mem hωAinf G
      rw [hseq, hlim]
      exact tendsto_const_nhds
    · push Not at hall
      obtain ⟨N, hN⟩ := hall
      have htail : ∀ᶠ n : ℕ in atTop, ω ∉ A n := by
        refine eventually_atTop.2 ⟨N, ?_⟩
        intro n hNn hωn
        exact hN (hanti hNn hωn)
      have hseq : (fun n => (A n).indicator G ω) =ᶠ[atTop] fun _ => 0 := by
        filter_upwards [htail] with n hn
        simp [Set.indicator_of_notMem hn]
      have hnot : ω ∉ Ainf := by
        simp only [Ainf, mem_iInter]
        exact fun h => hN (h N)
      have hlim : f ω = 0 := by simp [f, Set.indicator_of_notMem hnot]
      rw [hlim]
      exact Tendsto.congr' hseq.symm tendsto_const_nhds
  exact tendsto_condExpL1_of_dominated_convergence
    (m := m) (m₀ := measΩ) (μ := μ) hm _ hfn_meas hbound hfn_bound
    (Eventually.of_forall hpoint)

end DOZZ.Proofs

end
