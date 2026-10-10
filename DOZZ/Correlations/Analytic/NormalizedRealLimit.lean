/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.NormalizedRealValue
public import DOZZ.Correlations.Analytic.RetainedCoulombLimit
public import DOZZ.Correlations.Analytic.CutoffGeometry

/-! Identification of the canonical analytic cutoff limit on real charges. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The literal full Coulomb moment is finite throughout the strict moment range, for either
sign of the exponent. -/
theorem coulomb_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (hz : Function.Injective z) (αinf p : ℝ)
    (hpbulk : p < 4 / γ ^ 2) (hproot : ∀ i, p < 2 / γ * (Q γ - α i))
    (hpinf : p < 2 / γ * (Q γ - αinf)) :
    (∫⁻ ω, coulombMass γ (M ω) α z αinf ^ p ∂P) < ⊤ := by
  by_cases hp : 0 < p
  · exact coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf p hp hpbulk hproot hpinf
  · obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
    have hi := retained_coulomb_mass_nonpos_moment_finite P X hX γ hγ hγ2 M hM α z αinf
      Set.univ (1 + 2 * ∑ j, ‖z j‖) hR hzR (Set.subset_univ _) p (le_of_not_gt hp)
    simpa only [Measure.restrict_univ, ← coulombMass_eq_lintegral_coulombWeight] using hi

/-- The actual complex cutoff observable converges on every strictly admissible real vector
to the exact full Coulomb expectation. -/
theorem normalized_vertex_real_limit
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin (N + 1) → ℝ)
    (hp : (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2)
    (hpi : ∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i)) :
    Tendsto (fun n : ℕ => normalizedVertexMoment P Xc M
      (retainedRegion z (n : ℝ)) γ z (n : ℝ) (fun i => (α i : ℂ))) atTop
      (𝓝 ((∫⁻ ω, coulombMass γ (M ω) (fun i => α i.castSucc) z (α (Fin.last N)) ^
        ((2 * Q γ - ∑ i, α i) / γ) ∂P).toReal : ℂ)) := by
  let p := (2 * Q γ - ∑ i, α i) / γ
  have hret := retained_coulomb_moment_tendsto P X hX γ hγ hγ2 M hM
    (fun i => α i.castSucc) z hz (α (Fin.last N)) p hp
    (fun i => hpi i.castSucc) (hpi (Fin.last N))
  have hfin := coulomb_moment_finite P X hX γ hγ hγ2 M hM
    (fun i => α i.castSucc) z hz (α (Fin.last N)) p hp
    (fun i => hpi i.castSucc) (hpi (Fin.last N))
  have hreal := (Complex.continuous_ofReal.tendsto _).comp
    ((ENNReal.continuousAt_toReal hfin.ne).tendsto.comp hret)
  apply hreal.congr'
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  filter_upwards [retained_cutoff_geometry_eventually z 1
    (1 + 2 * ∑ j, ‖z j‖) (by norm_num)] with n hn
  have hball := exterior_ball_subset_retainedRegion z _ hR hzR (n : ℝ)
    (Nat.cast_nonneg _) hn.2.2.2
  have hne : (retainedRegion z (n : ℝ)).Nonempty :=
    (Metric.nonempty_ball.mpr (by norm_num : (0 : ℝ) < 1 / 8)).mono hball
  exact (normalized_vertex_moment_ofReal P X hX γ hγ hγ2 M hM Xc hc α z (n : ℝ)
    (Nat.cast_nonneg _) (retainedRegion z (n : ℝ)) (retainedRegion_isOpen z _)
      (retainedRegion_isBounded z _) hne Set.Subset.rfl).symm

end DOZZ.Proofs
