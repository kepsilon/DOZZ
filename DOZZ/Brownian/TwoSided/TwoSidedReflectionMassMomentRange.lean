/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.TwoSided.LateralMoments
public import DOZZ.Brownian.TwoSided.PositiveMoments
public import DOZZ.Brownian.TwoSided.InverseMoments

/-! Proof of `DOZZ.twoSidedReflectionMass_moment_range`, with all compact-parameter moment inputs
discharged. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The two-sided conditioned integral has every real moment below `4/γ²`, locally uniformly on
compact positive-drift and strict subcritical parameter ranges. See [KRV, Lemma 3.3] and its
proof in [KRV, §12.3]. -/
theorem twoSidedReflectionMass_moment_range
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kγ Kν Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKν : IsCompact Kν)
    (hKq : IsCompact Kq)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (hν : ∀ ν ∈ Kν, 0 < ν)
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) q ∂P) ≤ C := by
  classical
  by_cases hγne : Kγ.Nonempty
  · by_cases hνne : Kν.Nonempty
    · obtain ⟨νstar, hνstar⟩ := hνne
      have hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ) :=
        fun γ hγ => (hData γ hγ νstar hνstar).2.1
      obtain ⟨γ₀, hγ₀mem, hmin⟩ := hKγ.exists_isMinOn hγne continuous_id.continuousOn
      have hγ₀ : 0 < γ₀ := (hZ γ₀ hγ₀mem).1
      let g : ℝ := sSup Kγ
      have hgm : g ∈ Kγ := hKγ.sSup_mem hγne
      have hg : 0 < g := (hZ g hgm).1
      have hg2 : g < 2 := (hZ g hgm).2.1
      have hγbound : ∀ γ ∈ Kγ, γ₀ ≤ γ ∧ γ ≤ g :=
        fun γ hγ => ⟨hmin hγ, le_csSup hKγ.bddAbove hγ⟩
      obtain ⟨ν₀, N, hν₀, hνbound⟩ :=
        conditioned_compact_positive_drift_bounds Kν hKν ⟨νstar, hνstar⟩ hν
      obtain ⟨l, u, δ, hl, hu, hδ, hend, hmargin⟩ :=
        lateralGMC_compact_moment_endpoints_across_one P Kγ Kq hKγ hKq hγne Z hZ hq
      obtain ⟨Y, Mg, hS⟩ := (hZ g hgm).2.2.2.2.2.2.2.2
      obtain ⟨Yc, hYc, -⟩ := hS.2.1.2
      have hlcrit : l < 4 / g ^ 2 :=
        hl.trans (div_pos (by norm_num) (sq_pos_of_pos hg))
      have hucrit : u < 4 / g ^ 2 := by
        have hm := hmargin g hgm
        linarith
      obtain ⟨Cl, hCl, hRefl⟩ := twosided_reference_convex_moments_uniform
        P Y hS.1 Yc hYc g hg hg2 l (Or.inl hl) hlcrit
      obtain ⟨Cu, hCu, hRefu⟩ := twosided_reference_convex_moments_uniform
        P Y hS.1 Yc hYc g hg hg2 u (Or.inr hu.le) hucrit
      obtain ⟨Ll, hLl, hUnitl⟩ := twosided_lateral_unit_inverse_uniform
        P Kγ Z hZ l hl Cl hCl (fun γ hγ X M hX hM =>
          hRefl γ (hZ γ hγ).1 (hγbound γ hγ).2 X M hX hM)
      obtain ⟨Lu, hLu, hUnitu⟩ := twosided_lateral_unit_positive_uniform
        P Kγ Z hZ u (lt_trans zero_lt_one hu).le Cu hCu (fun γ hγ X M hX hM =>
          hRefu γ (hZ γ hγ).1 (hγbound γ hγ).2 X M hX hM)
      obtain ⟨Rl, hRl, hLower⟩ := twosided_inverse_moment_uniform_from_lateral
        P Kγ Kν B Z hData l N hl (fun ν hν => (hνbound ν hν).2) Ll hLl hUnitl
      obtain ⟨Ru, hRu, hUpper⟩ := twosided_positive_moment_uniform_from_lateral
        P Kγ Kν B Z hData u γ₀ g ν₀ N (lt_trans zero_lt_one hu) hγ₀ hν₀
        hγbound hνbound Lu hLu hUnitu
      exact twoSidedReflectionMass_uniform_moments_of_endpoints P Kγ Kν Kq B Z hData
        l u (fun q hq => (hend q hq).1.le) (fun q hq => (hend q hq).2.le)
        Rl Ru hRl hRu hLower hUpper
    · refine ⟨0, bot_lt_top, ?_⟩
      intro γ hγ ν hν
      exact False.elim (hνne ⟨ν, hν⟩)
  · refine ⟨0, bot_lt_top, ?_⟩
    intro γ hγ
    exact False.elim (hγne ⟨γ, hγ⟩)

end DOZZ.Proofs
