/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RealCenterCutoff
public import DOZZ.Correlations.Analytic.GeometricHolomorphicLimit
public import DOZZ.Correlations.Analytic.NormalizedRealLimit

/-! Holomorphic extension of the literal mixed-frame Coulomb expectation. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The normalized cutoff limit gives one holomorphic extension on an open neighborhood of
the full strict mixed-frame moment domain. Every real value is the literal Coulomb expectation;
no continuity or analyticity hypothesis on that expectation is assumed. -/
theorem mixed_coulomb_holomorphic
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (hz : Function.Injective z) :
    ∃ V : Set (Fin (N + 1) → ℂ), IsOpen V ∧
      (∀ α : Fin (N + 1) → ℝ, (∀ i, α i < Q γ) →
        (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2 →
        (∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i)) →
          (fun i => (α i : ℂ)) ∈ V) ∧
      ∃ f : (Fin (N + 1) → ℂ) → ℂ, DifferentiableOn ℂ f V ∧
        ∀ α : Fin (N + 1) → ℝ, (∀ i, α i < Q γ) →
          (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2 →
          (∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i)) →
            f (fun i => (α i : ℂ)) =
              ((∫⁻ ω, coulombMass γ (M ω) (fun i => α i.castSucc) z (α (Fin.last N)) ^
                ((2 * Q γ - ∑ i, α i) / γ) ∂P).toReal : ℂ) := by
  classical
  let F (n : ℕ) := normalizedVertexMoment P Xc M
    (retainedRegion z (n : ℝ)) γ z (n : ℝ)
  let f := fun β => limUnder atTop (fun n => F n β)
  let D : Set (Fin (N + 1) → ℝ) := {α | (∀ i, α i < Q γ) ∧
    (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2 ∧
      ∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i)}
  have hlocal : ∀ α : D, ∃ S : Fin (N + 1) → ℝ, (∀ i, 0 < S i) ∧
      DifferentiableOn ℂ f (complexPolydisc (fun i => (α.val i : ℂ)) S) ∧
        TendstoUniformlyOn F f atTop (complexPolydisc (fun i => (α.val i : ℂ)) S) := by
    intro α
    obtain ⟨S, hS, K, κ, hK, hκ, hest⟩ := real_center_cutoff_estimates
      P X hX γ hγ hγ2 M hM Xc hc z hz α.val α.property.1 α.property.2.1 α.property.2.2
    have he := holomorphic_limit_of_eventual_geometric
      (complexPolydisc (fun i => (α.val i : ℂ)) S) (isOpen_complexPolydisc _ _) F K κ hK hκ hest
    exact ⟨S, hS, he.1, he.2⟩
  choose S hS hd hlim using hlocal
  let V := ⋃ α : D, complexPolydisc (fun i => (α.val i : ℂ)) (S α)
  have hV : IsOpen V := isOpen_iUnion (fun α => isOpen_complexPolydisc _ _)
  have hmem (α : Fin (N + 1) → ℝ) (ha : ∀ i, α i < Q γ)
      (hp : (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2)
      (hpi : ∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i)) :
      (fun i => (α i : ℂ)) ∈ V :=
    mem_iUnion.mpr ⟨⟨α, ha, hp, hpi⟩, mem_complexPolydisc_center _ _ (hS _)⟩
  refine ⟨V, hV, hmem, f, ?_, ?_⟩
  · intro β hβ
    obtain ⟨α, hα⟩ := mem_iUnion.mp hβ
    exact ((hd α).differentiableAt ((isOpen_complexPolydisc _ _).mem_nhds hα)).differentiableWithinAt
  · intro α ha hp hpi
    let αD : D := ⟨α, ha, hp, hpi⟩
    have he := (hlim αD).tendsto_at (mem_complexPolydisc_center _ _ (hS αD))
    have hr := normalized_vertex_real_limit P X hX γ hγ hγ2 M hM Xc hc z hz α hp hpi
    exact tendsto_nhds_unique he hr

end DOZZ.Proofs
