/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.UniformCutoff
public import DOZZ.Correlations.SeparatedTail.SingularLimit

/-! Uniform mixed moments for the actual singular masses of the separated joint-tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Sharp marginal moments make the singular masses finite almost surely. -/
theorem separatedTail_weighted_mass_ae_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α a : ℝ) (hα : α < Q γ) (ha : 0 < a)
    (hrange : a < min (4/γ^2) (reflectionExponent γ α)) (z : ℂ) :
    ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) α z 1 ≠ ⊤ := by
  have hb := (equatorGFF_GMC_weighted_local_moment_range P X hX γ hγ hγ2 M hM
    α hα a ha z 1 (by norm_num)).mpr (by
      simpa only [reflectionExponent, div_mul_eq_mul_div] using hrange)
  have hm := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM α z 1
  have hf := ae_lt_top' (hm.pow_const a) hb.ne
  exact hf.mono fun ω hω => (ENNReal.rpow_eq_top_iff_of_pos ha).not.mp hω.ne

/-- The actual two-root mixed moment has the same uniform finite bound after the cutoff limit. -/
theorem separatedTail_singular_mixed_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K2 K3 : Set ℂ) (hK2 : IsCompact K2) (hK3 : IsCompact K3)
    (hsep : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2-z3‖)
    (A2 A3 : Set ℝ) (hA2 : IsCompact A2) (hA3 : IsCompact A3)
    (hα2 : ∀ α ∈ A2, γ/2 < α ∧ α < Q γ)
    (hα3 : ∀ α ∈ A3, γ/2 < α ∧ α < Q γ)
    (ε : ℝ) (hε : 0 < ε)
    (hε2 : ∀ α ∈ A2, ε < reflectionExponent γ α)
    (hε3 : ∀ α ∈ A3, ε < reflectionExponent γ α) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
        (∫⁻ ω, weightedGmcBallMass γ (M ω) α2 z2 1 ^ (reflectionExponent γ α2-ε) *
          weightedGmcBallMass γ (M ω) α3 z3 1 ^ (reflectionExponent γ α3-ε) ∂P) ≤ B := by
  obtain ⟨Xc,hc,_⟩ := hM.2
  obtain ⟨B,hB,hBb⟩ := separatedTail_cutoff_mixed_moment_uniform P X hX Xc hc γ hγ hγ2 K2 K3 hK2 hK3
    hsep A2 A3 hA2 hA3 hα2 hα3 ε hε hε2 hε3
  refine ⟨B,hB,fun z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem => ?_⟩
  have ha2 : 0 < reflectionExponent γ α2-ε := sub_pos.mpr (hε2 α2 hα2mem)
  have ha3 : 0 < reflectionExponent γ α3-ε := sub_pos.mpr (hε3 α3 hα3mem)
  have hr2 : reflectionExponent γ α2-ε < min (4/γ^2) (reflectionExponent γ α2) :=
    lt_min (by linarith [separatedTail_reflectionExponent_lt_bulk hγ (hα2 α2 hα2mem).1]) (by linarith)
  have hr3 : reflectionExponent γ α3-ε < min (4/γ^2) (reflectionExponent γ α3) :=
    lt_min (by linarith [separatedTail_reflectionExponent_lt_bulk hγ (hα3 α3 hα3mem).1]) (by linarith)
  apply separatedTail_singular_mixed_moment_le_of_cutoff P X hX γ hγ hγ2 M hM Xc hc z2 z3 α2 α3
    (by linarith [(hα2 α2 hα2mem).1]) (by linarith [(hα3 α3 hα3mem).1])
    _ _ ha2.le ha3.le
    (separatedTail_weighted_mass_ae_finite P X hX γ hγ hγ2 M hM α2 _ (hα2 α2 hα2mem).2 ha2 hr2 z2)
    (separatedTail_weighted_mass_ae_finite P X hX γ hγ hγ2 M hM α3 _ (hα3 α3 hα3mem).2 ha3 hr3 z3) B
  exact hBb z2 hz2 z3 hz3 α2 hα2mem α3 hα3mem

end DOZZ.Proofs
