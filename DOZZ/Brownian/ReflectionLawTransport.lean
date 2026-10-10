/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR

/-!
# Reflection moment transport under joint-law equality

The unit-volume reflection moment is a function of the joint input law of the two conditioned
paths and the lateral measure. This file proves that transport statement; source-level uniqueness
of the lateral law and the conditioned path law remain separate inputs.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Evaluate the two-sided conditioned path and its lateral mass on a single joint input point. -/
noncomputable def twoSidedReflectionMassInput (γ : ℝ)
    (z : (BrownianPath × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s, ENNReal.ofReal (Real.exp (γ *
    (if hs : 0 ≤ s then z.1.1 ⟨s, hs⟩ else z.1.2 ⟨-s, by linarith⟩))) ∂z.2

/-- Equal joint laws of the Brownian pair and lateral measure give equal unit-volume reflection
moments, assuming the induced mass moment is a.e. measurable. -/
theorem reflectionBarR_eq_of_joint_input_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ α : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (B' : Ω' → BrownianPath × BrownianPath) (Z' : Ω' → Measure ℝ)
    (hPair : AEMeasurable (fun ω => (B ω, Z ω)) P)
    (hPair' : AEMeasurable (fun ω => (B' ω, Z' ω)) P')
    (hLaw : P.map (fun ω => (B ω, Z ω)) = P'.map (fun ω => (B' ω, Z' ω)))
    (hMassMoment : AEMeasurable
      (fun z : (BrownianPath × BrownianPath) × Measure ℝ =>
        ENNReal.rpow (twoSidedReflectionMassInput γ z) (reflectionExponent γ α))
      (P.map (fun ω => (B ω, Z ω)))) :
    reflectionBarR P γ α B Z = reflectionBarR P' γ α B' Z' := by
  let pair : Ω → (BrownianPath × BrownianPath) × Measure ℝ :=
    fun ω => (B ω, Z ω)
  let pair' : Ω' → (BrownianPath × BrownianPath) × Measure ℝ :=
    fun ω => (B' ω, Z' ω)
  let f : (BrownianPath × BrownianPath) × Measure ℝ → ℝ≥0∞ := fun z =>
    ENNReal.rpow (twoSidedReflectionMassInput γ z) (reflectionExponent γ α)
  have hMassMoment' : AEMeasurable f (P'.map pair') := by
    rw [← hLaw]
    exact hMassMoment
  have hmoment :
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω)
        (reflectionExponent γ α) ∂P) =
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B' Z' ω)
        (reflectionExponent γ α) ∂P') := by
    calc
      _ = ∫⁻ ω, f (pair ω) ∂P := by
        apply lintegral_congr
        intro ω
        rfl
      _ = ∫⁻ z, f z ∂P.map pair := (lintegral_map' hMassMoment hPair).symm
      _ = ∫⁻ z, f z ∂P'.map pair' := by rw [hLaw]
      _ = ∫⁻ ω, f (pair' ω) ∂P' := lintegral_map' hMassMoment' hPair'
      _ = _ := by
        apply lintegral_congr
        intro ω
        rfl
  unfold reflectionBarR
  exact congrArg ENNReal.toReal hmoment

end DOZZ.Proofs

end
