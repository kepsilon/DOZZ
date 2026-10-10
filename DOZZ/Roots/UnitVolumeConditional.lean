/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.MainConditional
/-! # Conditional assembly of the unit-volume DOZZ root -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
universe u
namespace DOZZ.Proofs
theorem dozz_unitVolume_of_residual_factor (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (α₁ α₂ α₃ : ℝ) (hα : ExtendedSeiberg3 γ α₁ α₂ α₃)
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
    Tendsto
      (fun a : ℝ × ℝ × ℝ =>
        ((μ : ℂ) ^ (sExp γ a.1 a.2.1 a.2.2 : ℂ) / Complex.Gamma (sExp γ a.1 a.2.1 a.2.2)) *
          dozzFormula γ μ U a.1 a.2.1 a.2.2)
      (𝓝[{a | ExtendedSeiberg3 γ a.1 a.2.1 a.2.2 ∧
              ∀ n : ℕ, sExp γ a.1 a.2.1 a.2.2 ≠ -(n : ℝ)}] (α₁, α₂, α₃))
      (𝓝 (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ)) := by
  obtain ⟨V, hVo, _hVα, f, hfd, hfv⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  let A : ℝ × ℝ × ℝ → Fin 3 → ℂ := fun a => complexifyNCharges ![a.1, a.2.1, a.2.2]
  have hA : Continuous A := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun a : ℝ × ℝ × ℝ => (a.1 : ℂ))
      fun_prop
    · change Continuous (fun a : ℝ × ℝ × ℝ => (a.2.1 : ℂ))
      fun_prop
    · change Continuous (fun a : ℝ × ℝ × ℝ => (a.2.2 : ℂ))
      fun_prop
  have hpoint : A (α₁, α₂, α₃) ∈ V := _hVα ![α₁, α₂, α₃] hα
  have hc : ContinuousAt (fun a => f (A a)) (α₁, α₂, α₃) :=
    (hfd.continuousOn.continuousAt (hVo.mem_nhds hpoint)).comp
      (f := A) hA.continuousAt
  have hl : Tendsto (fun a => f (A a))
      (𝓝[{a : ℝ × ℝ × ℝ | ExtendedSeiberg3 γ a.1 a.2.1 a.2.2 ∧
        ∀ n : ℕ, sExp γ a.1 a.2.1 a.2.2 ≠ -(n : ℝ)}] (α₁, α₂, α₃))
      (𝓝 (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ)) := by
    have he : f (A (α₁, α₂, α₃)) = (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) :=
      hfv ![α₁, α₂, α₃] hα
    rw [← he]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  rw [show f (A a) = (unitVolumeStructureConstant P M γ a.1 a.2.1 a.2.2 : ℂ) from
    hfv ![a.1, a.2.1, a.2.2] ha.1]
  rw [← roots_unitVolume_normalization P M γ μ a.1 a.2.1 a.2.2 hμ ha.2]
  rw [dozz_main_of_residual_factor γ μ hγ hγ2 hμ a.1 a.2.1 a.2.2 ha.1 ha.2
    U hU P X M hX hM hresidual]
end DOZZ.Proofs
