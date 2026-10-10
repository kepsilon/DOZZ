/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralMoments.AnnularBounds
public import DOZZ.Brownian.Lateral.RadialWindowUniform
public import DOZZ.Brownian.Lateral.PositiveUniform

/-! The full compact-uniform interval moment range for every given lateral chaos. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Distributions
namespace DOZZ.Proofs

/-- Every translate of a fixed bounded interval has the full positive and negative moment range,
locally uniformly in compact charge and moment ranges with strict subcritical slack. See
[KRV, (zmoment)]. -/
theorem lateralGMC_interval_moment_range
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kγ Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKq : IsCompact Kq)
    (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (a b : ℝ) (hab : a < b)
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
        (∫⁻ ω, ENNReal.rpow ((Z γ ω) (Set.Ioc (a + t) (b + t))) q ∂P) ≤ C := by
  by_cases hγne : Kγ.Nonempty
  · obtain ⟨g, hgK, hmax⟩ := hKγ.exists_isMaxOn hγne continuous_id.continuousOn
    have hg := (hZ g hgK).1
    have hg2 := (hZ g hgK).2.1
    obtain ⟨X₀, M₀, hS₀⟩ := (hZ g hgK).2.2.2.2.2.2.2.2
    obtain ⟨Xc₀, hXc₀, _⟩ := hS₀.2.1.2
    obtain ⟨l, u, δ, hl, hu, hδ, hend, hmargin⟩ :=
      lateralGMC_compact_moment_endpoints_across_one P Kγ Kq hKγ hKq hγne Z hZ hq
    have hγbound : ∀ γ ∈ Kγ, 0 < γ ∧ γ ≤ g :=
      fun γ hγ => ⟨(hZ γ hγ).1, hmax hγ⟩
    have hlcrit : l < 4 / g ^ 2 := hl.trans (by positivity)
    have hucrit : u < 4 / g ^ 2 := by linarith only [hmargin g hgK, hδ]
    obtain ⟨Cl, hCl, hL⟩ := latmom_annular_uniform_convex_moment P X₀ hS₀.1 Xc₀ hXc₀
      g hg hg2 Kγ hγbound l (Or.inl hl.le) hlcrit a b hab
    obtain ⟨Cu, hCu, hU⟩ := latmom_annular_uniform_convex_moment P X₀ hS₀.1 Xc₀ hXc₀
      g hg hg2 Kγ hγbound u (Or.inr hu.le) hucrit a b hab
    apply lateralGMC_uniform_interval_moments_of_all_source_annular P Kγ Kq hKq Z hZ
      a b (Cl+Cu) (ENNReal.add_lt_top.mpr ⟨hCl, hCu⟩)
    intro γ hγ q hqm X M hS
    have hVm : AEMeasurable (fun ω => M ω (lateralLogAnnulus a b)) P :=
      gmc_set_mass_aemeasurable_of_isGMCOf P X hS.1 γ (hZ γ hγ).1 (hZ γ hγ).2.1
        M hS.2.1 _ (measurableSet_lateralLogAnnulus a b)
    exact (lintegral_rpow_le_endpoint_sum P _ hVm (hend q hqm).1.le (hend q hqm).2.le).trans
      (add_le_add (hL γ hγ X M hS.1 hS.2.1) (hU γ hγ X M hS.1 hS.2.1))
  · exact lateralGMC_interval_uniform_empty P Kγ Kq Z a b
      (Or.inl (Set.not_nonempty_iff_eq_empty.mp hγne))

end DOZZ.Proofs
end
