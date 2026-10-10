/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.Irrational
public import DOZZ.Roots.FormulaGammaContinuity
public import DOZZ.Roots.GammaDensity
public import DOZZ.Roots.ParameterFamilies
/-! # Conditional assembly of the finite DOZZ root -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
universe u
namespace DOZZ.Proofs
/-- The calibrated residual identity is the only additional input `hresidual` of the finite root
assembly. The input below is the complete statement of `DOZZ.unitVolume_residual_factor_eq_one`; the
full dual-shift statement is not used. -/
theorem dozz_main_of_residual_factor (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
    (hs : ∀ n : ℕ, sExp γ α₁ α₂ α₃ ≠ -(n : ℝ))
    (U : ℂ → ℂ) (hU : IsUpsilon γ U)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hresidual : ∀
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ) (U : ℂ → ℂ)
    (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hγirr : Irrational (γ ^ 2)) (_hμ : 0 < μ)
    (_hη : 0 < η ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ)
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M)
    (_hU : IsUpsilon γ U),
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ cγ : ℂ, cγ = 1 ∧
              ∀ α₁ α₂ α₃ : ℝ,
                Q γ - η < α₁ → α₁ < Q γ →
                Q γ - η < α₂ → α₂ < Q γ →
                Q γ - η < α₃ → α₃ < Q γ →
                  (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
                    cγ * ((μ : ℂ) ^ ((sExp γ α₁ α₂ α₃ : ℂ)) /
                      Complex.Gamma (sExp γ α₁ α₂ α₃ : ℂ) *
                        dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ))) :
    (structureConstant P M γ μ α₁ α₂ α₃ : ℂ) = dozzFormula γ μ U α₁ α₂ α₃ := by
  obtain ⟨N, hNγ, hN⟩ := roots_GMC_family_through P X hX γ M hM
  obtain ⟨V, hVγ, hV⟩ := roots_Upsilon_family_through γ U hU
  have hC : ContinuousAt (fun g => (structureConstant P (N g) g μ α₁ α₂ α₃ : ℂ)) γ :=
    Complex.continuous_ofReal.continuousAt.comp
      (roots_structureConstant_gamma_continuousAt P X N hX hN γ μ α₁ α₂ α₃ hγ hγ2 hμ hα hs)
  have hD := roots_dozzFormula_gamma_continuousAt V hV γ μ α₁ α₂ α₃ hγ hγ2 hμ hα hs
  have heq : ∃ᶠ g : ℝ in nhds γ,
      (structureConstant P (N g) g μ α₁ α₂ α₃ : ℂ) = dozzFormula g μ (V g) α₁ α₂ α₃ := by
    have hfreq := (roots_frequently_irrational_sq γ hγ).and_eventually
      ((roots_extended_parameters_nhds hγ hγ2 hα).and (roots_poleFree_gamma_nhds γ α₁ α₂ α₃ hγ.ne' hs))
    apply hfreq.mono
    rintro g ⟨hgirr, ⟨hg, hg2, hgα⟩, hgs⟩
    apply roots_main_of_calibrated_residual P X (N g) g μ hg hg2 hμ (V g) (hV g ⟨hg, hg2⟩) hX (hN g hg hg2)
    · intro η hη
      exact hresidual P X (N g) g μ η (V g) hg hg2 hgirr hμ hη hX (hN g hg hg2) (hV g ⟨hg, hg2⟩)
    · exact hgα
    · exact hgs
  have he := tendsto_nhds_unique_of_frequently_eq hC.tendsto hD.tendsto heq
  simpa only [hNγ, hVγ] using he
end DOZZ.Proofs
