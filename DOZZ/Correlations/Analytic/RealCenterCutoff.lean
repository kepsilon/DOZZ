/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedExponential
public import DOZZ.Correlations.Analytic.ComplexChargeNeighborhood
public import DOZZ.Correlations.Analytic.SeparatedGeometry

/-! Strict real admissibility produces the actual local holomorphic Cauchy family. -/

@[expose] public section
open MeasureTheory Filter Topology
namespace DOZZ.Proofs

/-- Every strictly admissible real mixed-frame charge vector has a complex neighborhood on
which the actual normalized cutoff family is eventually holomorphic and has uniform summable
increments. All moment and geometric margins are constructed from the literal inequalities. -/
theorem real_center_cutoff_estimates
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin (N + 1) → ℝ)
    (ha : ∀ i, α i < Q γ)
    (hp : (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2)
    (hpi : ∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i)) :
    ∃ S : Fin (N + 1) → ℝ, (∀ i, 0 < S i) ∧ ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧
      ∀ᶠ n : ℕ in atTop,
        DifferentiableOn ℂ
          (normalizedVertexMoment P Xc M (retainedRegion z (n : ℝ)) γ z (n : ℝ))
          (complexPolydisc (fun i => (α i : ℂ)) S) ∧
        ∀ β ∈ complexPolydisc (fun i => (α i : ℂ)) S,
          ‖normalizedVertexMoment P Xc M (retainedRegion z ((n + 1 : ℕ) : ℝ))
              γ z ((n + 1 : ℕ) : ℝ) β -
            normalizedVertexMoment P Xc M (retainedRegion z (n : ℝ))
              γ z (n : ℝ) β‖ ≤ K * Real.exp (-κ * n) := by
  classical
  obtain ⟨A, a, gap, m, g, lo, hi, q, b, hA, haa, hgap, hgapQ, hm, hm1, hms,
    hg, hlo, hlop, hhi, hphi, hq, hb, hbulk, hroot⟩ :=
      real_charge_moment_budget γ hγ α ((2 * Q γ - ∑ i, α i) / γ) ha hp hpi
  obtain ⟨δ, hδ, hδ8, hsep⟩ := separated_geometry z hz
  let Zs := ∑ i, ‖z i‖
  let R := 1 + 2 * Zs
  have hZs : 0 ≤ Zs := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  obtain ⟨radius, hradius, hbox⟩ := complex_charge_budget_neighborhood γ α
    A a lo hi b hA haa hlop hphi hb
  obtain ⟨K, κ, d, hK, hκ, hd, hdec⟩ := normalized_cutoff_exponential_polydisc
    P X hX γ hγ hγ2 M hM Xc hc z hz δ R Zs A a gap m g lo hi q b hδ hδ8 hR hZs
      hsep le_rfl hzR hgap hgapQ hm hm1 hms hg hlo hhi hq hbulk hroot
        α radius hradius hbox
  obtain ⟨S, hS, hsub, hthin⟩ := polydisc_thin_imaginary α radius hradius d hd
  refine ⟨S, hS, K, κ, hK, hκ, ?_⟩
  filter_upwards [hdec, retained_cutoff_geometry_eventually z δ R hδ] with n hn hgeo
  have hr : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  have hball := exterior_ball_subset_retainedRegion z R hR hzR (n : ℝ) hr hgeo.2.2.2
  have hne : (retainedRegion z (n : ℝ)).Nonempty :=
    (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1 / 8)).mono hball
  constructor
  · apply (normalized_vertex_moment_holomorphic P X hX γ hγ hγ2 M hM Xc hc
      (retainedRegion z (n : ℝ)) (retainedRegion_isOpen z _)
      (retainedRegion_isBounded z _) hne z (n : ℝ)).2.mono
    intro β hβ
    change (complexMomentPower γ β).re < 4 / γ ^ 2
    have he := (hbox β (hsub hβ)).2.2.2.1
    have hhiq : hi ≤ hi * q := by nlinarith
    linarith
  · intro β hβ
    exact hn β (hsub hβ) (hthin β hβ)

end DOZZ.Proofs
