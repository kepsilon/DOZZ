/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.ReflectionPoleFree
public import DOZZ.Statements.Defs.ReflectionDOZZ

/-!
# Isolation of reflection poles

The punctured reflection theorem is a topological consequence of the off-pole identity once the
integer Gamma poles are locally isolated. This module proves that isolation and packages the
punctured-limit reduction without importing a theorem statement from `DOZZ/Statements`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- Near a point where the exponent is a positive integer, that same pole is the only possible
reflection pole. Removing the center therefore gives a pole-free punctured neighborhood. -/
theorem reflectionPoleFree_eventually_punctured
    {γ α₀ : ℝ} (hγ : 0 < γ) (n : ℕ)
    (hn : reflectionExponent γ α₀ = n + 1) :
    ∀ᶠ α : ℝ in 𝓝[≠] α₀, ReflectionPoleFree γ α := by
  have hcont : ContinuousAt (fun α : ℝ => reflectionExponent γ α) α₀ := by
    unfold reflectionExponent
    fun_prop
  have hnlow : (n : ℝ) < reflectionExponent γ α₀ := by
    rw [hn]
    exact_mod_cast Nat.lt_succ_self n
  have hnup : reflectionExponent γ α₀ < (n : ℝ) + 2 := by
    rw [hn]
    norm_num
  have hclose : ∀ᶠ α : ℝ in 𝓝 α₀,
      reflectionExponent γ α ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 2) :=
    hcont.tendsto.eventually_mem (isOpen_Ioo.mem_nhds ⟨hnlow, hnup⟩)
  have hclose' : ∀ᶠ α : ℝ in 𝓝[≠] α₀,
      reflectionExponent γ α ∈ Set.Ioo (n : ℝ) ((n : ℝ) + 2) :=
    hclose.filter_mono nhdsWithin_le_nhds
  filter_upwards [hclose', self_mem_nhdsWithin] with α hα hαne
  intro m hm
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hle : ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hmn
    rw [hm] at hα
    exact (not_lt_of_ge hle) hα.1
  · subst m
    have hpEq : reflectionExponent γ α = reflectionExponent γ α₀ := by
      rw [hm, hn]
      norm_num
    have hpEq' :
        2 * (Q γ - α) / γ = 2 * (Q γ - α₀) / γ := by
      simpa [reflectionExponent] using hpEq
    have hmul := congrArg (fun x : ℝ => x * γ) hpEq'
    have hlin : 2 * (Q γ - α) = 2 * (Q γ - α₀) := by
      field_simp [hγ.ne'] at hmul
      linarith
    have : α = α₀ := by linarith
    exact hαne this
  · have hge : (n : ℝ) + 2 ≤ ((m + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.succ_le_of_lt hnm)
    rw [hm] at hα
    exact (not_lt_of_ge hge) hα.2

/-- Assuming the pointwise off-pole reflection identity, the difference has zero punctured limit
at any interior positive-integer pole. -/
theorem reflection_Rtheor_punctured_of_offPoleEquality
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α₀ : ℝ)
    (hγ : 0 < γ) (_hγ2 : γ < 2) (_hμ : 0 < μ)
    (hα₀ : γ / 2 < α₀ ∧ α₀ < Q γ)
    (n : ℕ) (hn : reflectionExponent γ α₀ = n + 1)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z)
    (hOff : ∀ α, γ / 2 < α → α < Q γ → ReflectionPoleFree γ α →
      IsReflectionData P γ α (B α) Z →
        (reflectionR P γ μ α (B α) Z : ℂ) = reflectionDOZZ γ μ (α : ℂ)) :
    Tendsto (fun α : ℝ =>
      (reflectionR P γ μ α (B α) Z : ℂ) - reflectionDOZZ γ μ (α : ℂ))
        (𝓝[≠] α₀) (𝓝 0) := by
  have hIoo : ∀ᶠ α : ℝ in 𝓝 α₀,
      α ∈ Set.Ioo (γ / 2) (Q γ) := by
    exact isOpen_Ioo.mem_nhds
      (show α₀ ∈ Set.Ioo (γ / 2) (Q γ) from ⟨hα₀.1, hα₀.2⟩)
  have hrange : ∀ᶠ α : ℝ in 𝓝[≠] α₀,
      α ∈ Set.Ioo (γ / 2) (Q γ) :=
    hIoo.filter_mono nhdsWithin_le_nhds
  have hpole := reflectionPoleFree_eventually_punctured hγ n hn
  have hzero : (fun α : ℝ =>
      (reflectionR P γ μ α (B α) Z : ℂ) - reflectionDOZZ γ μ (α : ℂ)) =ᶠ[𝓝[≠] α₀]
      fun _ => (0 : ℂ) := by
    filter_upwards [hrange, hpole] with α hα hfree
    have hdata := hData α hα.1 hα.2
    rw [hOff α hα.1 hα.2 hfree hdata]
    simp
  exact tendsto_const_nhds.congr' hzero.symm

end DOZZ.Proofs

end
