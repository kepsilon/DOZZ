/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Reflection.RbarContinuity
public import DOZZ.Statements.Brownian.IsLateralGMCOf
import DOZZ.ShiftEquations.Reflection.Witness
import DOZZ.ShiftEquations.Reflection.Endpoint
import DOZZ.Brownian.Lateral.ReflectionJointLaw

/-!
# Endpoint limits and continuity in `γ` from the `R̄` representation

The reflection witnesses for all `γ` come from the lateral decomposition and the Williams
post-maximum witness family; the endpoint limits are `reflection_endpoint_limits`; the joint
continuity of `C̄` is `continuousOn_unitVolumeStructureConstant` (from
`DOZZ.unitVolumeNPoint_jointly_continuous_parameters`); the joint continuity of `R̄` and `R` follows
from the representation `R̄ = coefficient · C̄(α, γ, α)`, which enters as the hypothesis `hBarRRepresentation` (the
conclusion of `DOZZ.reflectionBarR_holomorphic_representation` at the given field, for every `γ` and
chaos).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- **Endpoint limits and continuity in `γ` from the `R̄` representation.** -/
theorem reflection_endpoint_and_gamma_continuity_of_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (hX : IsEquatorGFF P X)
    (μ : ℝ) (hμ : 0 < μ)
    (hM : ∀ γ, 0 < γ → γ < 2 → IsGMCOf P X γ (M γ))
    (hBarRRepresentation : ∀ (γ : ℝ) (Mγ : Ω → Measure ℂ) (_ : 0 < γ) (_ : γ < 2) (_ : IsGMCOf P X γ Mγ)
      (I : Set ℝ) (_ : IsCompact I) (_ : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ Mγ Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P Mγ γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              ∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ)) :
    ∃ B : ℝ → ℝ → Ω →
        BrownianPath × BrownianPath,
      ∃ Z : ℝ → Ω → Measure ℝ,
        (∀ γ, 0 < γ → γ < 2 →
          IsSourceLateralProjection P X γ (M γ) (Z γ) ∧
            ∀ α, γ / 2 < α → α < Q γ →
              IsReflectionData P γ α (B γ α) (Z γ)) ∧
          (∀ γ, 0 < γ → γ < 2 →
            Tendsto (fun α : ℝ =>
              reflectionBarR P γ α (B γ α) (Z γ))
              (𝓝[<] (Q γ)) (𝓝 1) ∧
            Tendsto (fun α : ℝ =>
              reflectionR P γ μ α (B γ α) (Z γ))
              (𝓝[<] (Q γ)) (𝓝 (-1))) ∧
          (∀ K : Set (ℝ × ℝ), IsCompact K →
            (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) →
              ContinuousOn (fun q => reflectionBarR P q.1 q.2 (B q.1 q.2) (Z q.1)) K ∧
                ((∀ q ∈ K, ReflectionPoleFree q.1 q.2) →
                  ContinuousOn (fun q => reflectionR P q.1 μ q.2 (B q.1 q.2) (Z q.1)) K)) ∧
          ∀ K : Set (ℝ × (Fin 3 → ℝ)), IsCompact K →
            (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧
              ExtendedSeiberg3 q.1 (q.2 0) (q.2 1) (q.2 2)) →
              ContinuousOn (fun q => unitVolumeStructureConstant P (M q.1) q.1
                (q.2 0) (q.2 1) (q.2 2)) K := by
  have hW : ∀ γ : ℝ, ∃ BZ : (ℝ → Ω → BrownianPath × BrownianPath) × (Ω → Measure ℝ),
      0 < γ → γ < 2 → IsSourceLateralProjection P X γ (M γ) BZ.2 ∧
        ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BZ.1 α) BZ.2 := by
    intro γ
    by_cases h : 0 < γ ∧ γ < 2
    · obtain ⟨A, hXcA, hAm, hA0, hBf, hBb, hInd, hLm, hIndL, hLat⟩ :=
        equatorGFF_lateral_GMC_decomposition P X (M γ) γ h.1 h.2 hX (hM γ h.1 h.2)
      have hSLP : IsSourceLateralProjection P X γ (M γ)
          (fun ω => lateralProjectedGMC γ (A ω) (M γ ω)) :=
        ⟨hX, hM γ h.1 h.2, A, hXcA, hAm, hA0, hBf, hBb, hInd, hLm, hIndL,
          Eventually.of_forall fun _ => rfl⟩
      obtain ⟨B, hB⟩ := exists_reflectionData_family P X γ (M γ) _ hSLP hLat
      exact ⟨(B, fun ω => lateralProjectedGMC γ (A ω) (M γ ω)),
        fun _ _ => ⟨hSLP, fun α _ hα => hB α hα⟩⟩
    · exact ⟨(fun _ _ => (0, 0), fun _ => 0), fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose BZ hBZ using hW
  have hData : ∀ γ, 0 < γ → γ < 2 → ∀ α, γ / 2 < α → α < Q γ →
      IsReflectionData P γ α ((BZ γ).1 α) (BZ γ).2 :=
    fun γ h1 h2 α ha1 ha2 => (hBZ γ h1 h2).2 α ha1 ha2
  refine ⟨fun γ => (BZ γ).1, fun γ => (BZ γ).2, fun γ h1 h2 => hBZ γ h1 h2,
    fun γ h1 h2 => reflection_endpoint_limits P γ μ h1 h2 hμ _ _ (hData γ h1 h2),
    fun K hK hKdom => continuousOn_reflection_of_representation P X M hX hM hBarRRepresentation μ hμ
      (fun γ => (BZ γ).1) (fun γ => (BZ γ).2) hData K hK hKdom,
    fun K hK hKdom => continuousOn_unitVolumeStructureConstant P X M hX hM K hK hKdom⟩

end DOZZ.Proofs

end
