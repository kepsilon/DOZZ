/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionParameterDomain
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Successive one-variable continuation on the nonresonant Gauss parameter domain. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- The integer lattice excluded by the two connection exponents. -/
def gaussConnectionIntegerRange : Set ℂ := Set.range fun n : ℤ => (n : ℂ)

private theorem gaussConnectionIntegerRange_isClosed :
    IsClosed gaussConnectionIntegerRange := by
  have hIso : Isometry (fun n : ℤ => (n : ℂ)) := Complex.isometry_intCast
  exact hIso.isClosedEmbedding.isClosed_range

private theorem gaussNonintegerDomain_isOpen :
    IsOpen gaussConnectionIntegerRangeᶜ :=
  gaussConnectionIntegerRange_isClosed.isOpen_compl

private theorem gaussNonintegerDomain_isPreconnected :
    IsPreconnected gaussConnectionIntegerRangeᶜ := by
  have hcount : gaussConnectionIntegerRange.Countable :=
    Set.countable_range fun n : ℤ => (n : ℂ)
  have hpath : IsPathConnected gaussConnectionIntegerRangeᶜ :=
    Set.Countable.isPathConnected_compl_of_one_lt_rank
      (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) hcount
  exact hpath.isConnected.isPreconnected

/-- Convert the product coordinates `(c, δ, a)` to the source parameter order `(a,b,c)`. -/
def gaussConnectionCoordinates (c δ a : ℂ) : ℂ × ℂ × ℂ :=
  (a, c - δ - a, c)

/-- Equality of two parameter-differentiable functions on one open Euler box propagates to the
whole nonresonant connection domain. The proof uses only one-variable identity theorems, in the
coordinates `(c, δ, a)` where the domain is `(ℂ \ ℤ) × (ℂ \ ℤ) × ℂ`. -/
theorem eq_of_eq_on_open_gaussConnection_box
    {f g : ℂ × ℂ × ℂ → ℂ}
    (hf : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ f p)
    (hg : ∀ p ∈ gaussConnectionParameterDomain, DifferentiableAt ℂ g p)
    {S T V : Set ℂ} {c₀ δ₀ a₀ : ℂ}
    (hSopen : IsOpen S) (hTopen : IsOpen T) (hVopen : IsOpen V)
    (hc₀ : c₀ ∈ S) (hδ₀ : δ₀ ∈ T) (ha₀ : a₀ ∈ V)
    (hS : S ⊆ gaussConnectionIntegerRangeᶜ)
    (hT : T ⊆ gaussConnectionIntegerRangeᶜ)
    (hEq : ∀ c ∈ S, ∀ δ ∈ T, ∀ a ∈ V,
      f (gaussConnectionCoordinates c δ a) = g (gaussConnectionCoordinates c δ a))
    {a b c : ℂ} (hp : (a, b, c) ∈ gaussConnectionParameterDomain) :
    f (a, b, c) = g (a, b, c) := by
  let F : ℂ → ℂ → ℂ → ℂ := fun c δ a =>
    f (gaussConnectionCoordinates c δ a)
  let G : ℂ → ℂ → ℂ → ℂ := fun c δ a =>
    g (gaussConnectionCoordinates c δ a)
  have hFdiff (c δ a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => F x δ a) c := by
    have hcoord : gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
      have hcoord' : (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, δ ≠ (n : ℂ) := by
        simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ
      simpa [F, gaussConnectionCoordinates, gaussConnectionParameterDomain] using hcoord'
    have hmap : DifferentiableAt ℂ (fun x : ℂ => gaussConnectionCoordinates x δ a) c := by
      dsimp [gaussConnectionCoordinates]
      fun_prop
    exact (hf _ hcoord).comp c hmap
  have hGdiff (c δ a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => G x δ a) c := by
    have hcoord : gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
      have hcoord' : (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, δ ≠ (n : ℂ) := by
        simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ
      simpa [G, gaussConnectionCoordinates, gaussConnectionParameterDomain] using hcoord'
    have hmap : DifferentiableAt ℂ (fun x : ℂ => gaussConnectionCoordinates x δ a) c := by
      dsimp [gaussConnectionCoordinates]
      fun_prop
    exact (hg _ hcoord).comp c hmap
  have hFδdiff (c δ a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => F c x a) δ := by
    have hcoord : gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
      have hcoord' : (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, δ ≠ (n : ℂ) := by
        simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ
      simpa [F, gaussConnectionCoordinates, gaussConnectionParameterDomain] using hcoord'
    have hmap : DifferentiableAt ℂ (fun x : ℂ => gaussConnectionCoordinates c x a) δ := by
      dsimp [gaussConnectionCoordinates]
      fun_prop
    exact (hf _ hcoord).comp δ hmap
  have hGδdiff (c δ a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => G c x a) δ := by
    have hcoord : gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
      have hcoord' : (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, δ ≠ (n : ℂ) := by
        simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ
      simpa [G, gaussConnectionCoordinates, gaussConnectionParameterDomain] using hcoord'
    have hmap : DifferentiableAt ℂ (fun x : ℂ => gaussConnectionCoordinates c x a) δ := by
      dsimp [gaussConnectionCoordinates]
      fun_prop
    exact (hg _ hcoord).comp δ hmap
  have hFaDiff (c δ a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => F c δ x) a := by
    have hcoord : gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
      have hcoord' : (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, δ ≠ (n : ℂ) := by
        simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ
      simpa [F, gaussConnectionCoordinates, gaussConnectionParameterDomain] using hcoord'
    have hmap : DifferentiableAt ℂ (fun x : ℂ => gaussConnectionCoordinates c δ x) a := by
      dsimp [gaussConnectionCoordinates]
      fun_prop
    exact (hf _ hcoord).comp a hmap
  have hGaDiff (c δ a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      DifferentiableAt ℂ (fun x => G c δ x) a := by
    have hcoord : gaussConnectionCoordinates c δ a ∈ gaussConnectionParameterDomain := by
      have hcoord' : (∀ n : ℤ, c ≠ (n : ℂ)) ∧ ∀ n : ℤ, δ ≠ (n : ℂ) := by
        simpa [gaussConnectionIntegerRange, eq_comm] using And.intro hc hδ
      simpa [G, gaussConnectionCoordinates, gaussConnectionParameterDomain] using hcoord'
    have hmap : DifferentiableAt ℂ (fun x : ℂ => gaussConnectionCoordinates c δ x) a := by
      dsimp [gaussConnectionCoordinates]
      fun_prop
    exact (hg _ hcoord).comp a hmap
  have hFanalyticC (δ a : ℂ) (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => F x δ a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hFdiff x δ a hx hδ).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hGanalyticC (δ a : ℂ) (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => G x δ a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hGdiff x δ a hx hδ).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hFanalyticδ (c a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => F c x a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hFδdiff c x a hc hx).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hGanalyticδ (c a : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ) :
      AnalyticOnNhd ℂ (fun x => G c x a) gaussConnectionIntegerRangeᶜ := by
    apply DifferentiableOn.analyticOnNhd
    · intro x hx
      exact (hGδdiff c x a hc hx).differentiableWithinAt
    · exact gaussNonintegerDomain_isOpen
  have hC (δ : ℂ) (hδ : δ ∈ T) (a : ℂ) (ha : a ∈ V) :
      ∀ c ∈ gaussConnectionIntegerRangeᶜ, F c δ a = G c δ a := by
    have hnear : (fun x => F x δ a) =ᶠ[𝓝 c₀] (fun x => G x δ a) := by
      filter_upwards [hSopen.mem_nhds hc₀] with x hx
      exact hEq x hx δ hδ a ha
    intro c hc
    have hEqC := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hFanalyticC δ a (hT hδ)) (hGanalyticC δ a (hT hδ))
      gaussNonintegerDomain_isPreconnected (hS hc₀) hnear
    exact hEqC hc
  have hDelta (c : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ) :
      ∀ δ ∈ gaussConnectionIntegerRangeᶜ, ∀ a ∈ V, F c δ a = G c δ a := by
    intro δ hδ a ha
    have hnear : (fun x => F c x a) =ᶠ[𝓝 δ₀] (fun x => G c x a) := by
      filter_upwards [hTopen.mem_nhds hδ₀] with x hx
      exact hC x hx a ha c hc
    exact (AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hFanalyticδ c a hc) (hGanalyticδ c a hc) gaussNonintegerDomain_isPreconnected
      (hT hδ₀) hnear) hδ
  have hA (c δ : ℂ) (hc : c ∈ gaussConnectionIntegerRangeᶜ)
      (hδ : δ ∈ gaussConnectionIntegerRangeᶜ) : ∀ a, F c δ a = G c δ a := by
    have hFan : AnalyticOnNhd ℂ (fun x => F c δ x) Set.univ := by
      apply DifferentiableOn.analyticOnNhd
      · intro x _
        exact (hFaDiff c δ x hc hδ).differentiableWithinAt
      · exact isOpen_univ
    have hGan : AnalyticOnNhd ℂ (fun x => G c δ x) Set.univ := by
      apply DifferentiableOn.analyticOnNhd
      · intro x _
        exact (hGaDiff c δ x hc hδ).differentiableWithinAt
      · exact isOpen_univ
    have hnear : (fun x => F c δ x) =ᶠ[𝓝 a₀] (fun x => G c δ x) := by
      filter_upwards [hVopen.mem_nhds ha₀] with x hx
      exact hDelta c hc δ hδ x hx
    intro a
    have hEqA := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      hFan hGan isPreconnected_univ (Set.mem_univ a₀) hnear
    exact hEqA (Set.mem_univ a)
  have hTarget : F c (c - a - b) a = G c (c - a - b) a := by
    have hc' : c ∈ gaussConnectionIntegerRangeᶜ := by
      have := hp.1
      simpa [gaussConnectionParameterDomain, gaussConnectionIntegerRange, eq_comm] using this
    have hδ' : c - a - b ∈ gaussConnectionIntegerRangeᶜ := by
      have := hp.2
      simpa [gaussConnectionParameterDomain, gaussConnectionIntegerRange, eq_comm] using this
    exact hA c (c - a - b) hc' hδ' a
  have htuple : gaussConnectionCoordinates c (c - a - b) a = (a, b, c) := by
    simp [gaussConnectionCoordinates]
    ring
  simpa [F, G, htuple] using hTarget

end DOZZ.Proofs
