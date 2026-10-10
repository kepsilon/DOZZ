/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SumTail.VariableRate
public import DOZZ.Correlations.SumTail.Ceiling
public import DOZZ.Correlations.Tails.ReflectionWitness
public import DOZZ.Brownian.Reflection.WitnessIndependence

/-! The literal one-insertion input yields variable-rate estimates for one common witness. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Localizing only the charge compact set retains the common physical reflection coefficient. -/
theorem sumtail_uniform_one_tail_for_common_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ)
    (hone : ∀
    (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (_hKα : IsCompact Kα)
    (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound),
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧
        ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
                oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) *
                  Real.rpow x (-reflectionExponent γ α)| ≤
                C * Real.rpow x (-reflectionExponent γ α - η) )
    (Kz : Set ℂ) (hKz : IsCompact Kz) (hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (hKα : IsCompact Kα) (hα : ∀ α ∈ Kα, γ/2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : ∀ α ∈ Kα, IsReflectionData P γ α (B α) Z)
    (d : ℝ) (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
      |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
        oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z)*x^(-reflectionExponent γ α)| ≤
      C*x^(-reflectionExponent γ α-oneInsertionErrorCeiling γ α+d) := by
  let S := {q : ℂ × (ℂ → ℝ) // q.1 ∈ Kz ∧ q.2 ∈ Family q.1}
  let err (α : ℝ) (s : S) (x : ℝ) :=
    |(P {ω | ENNReal.ofReal x < localSingularMass M s.1.2 s.1.1 γ α ω}).toReal -
      oneInsertionTailCoefficient γ α s.1.1 (s.1.2 s.1.1) (reflectionBarR P γ α (B α) Z)*x^(-reflectionExponent γ α)|
  have hfixed : ∀ L : Set ℝ, IsCompact L → L ⊆ Kα → ∀ η : ℝ, 0 < η →
      (∀ α ∈ L, η < oneInsertionErrorCeiling γ α) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ α ∈ L, ∀ s : S, ∀ x : ℝ, 1 ≤ x →
        err α s x ≤ C*x^(-reflectionExponent γ α-η) := by
    intro L hL hLK η hη hηL
    obtain ⟨B',Z',_hsource,hB',happrox⟩ := hone Kz hKz hz L hL
      (fun α hαL => hα α (hLK hαL)) Family radius supBound derivBound lowerBound hFamily
    obtain ⟨C,hC,hCb⟩ := happrox η hη hηL
    refine ⟨C,hC,?_⟩
    intro α hαL s x hx
    have hb := hCb s.1.1 s.2.1 α hαL s.1.2 s.2.2 x hx
    have hr := reflectionBarR_eq_of_isReflectionData P P γ α (B' α) Z' (B α) Z
      (hB' α hαL) (hB α (hLK hαL))
    rw [hr] at hb
    simpa only [err,Real.rpow_eq_pow] using hb
  obtain ⟨C,hC,hCb⟩ := sumtail_uniform_variable_rate Kα hKα (oneInsertionErrorCeiling γ)
    (reflectionExponent γ) (sumtail_one_error_continuousOn γ Kα hγ hα)
    (fun α ha => residue_oneInsertionErrorCeiling_pos γ α hγ (hα α ha).1 (hα α ha).2)
    err hfixed d hd
  refine ⟨C,hC,?_⟩
  intro z hz α hα F hF x hx
  exact hCb α hα ⟨(z,F),hz,hF⟩ x hx

end DOZZ.Proofs
