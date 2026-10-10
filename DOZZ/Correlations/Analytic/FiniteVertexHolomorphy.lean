/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedMassMoments
public import DOZZ.Correlations.Analytic.FiniteVertexGaussian
public import DOZZ.Complex.Charge

/-! Holomorphy of finite-radius Wick vertices with a retained, charge-independent GMC mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Sum of the complex charges as a continuous linear functional. -/
noncomputable def chargeSumCLM (N : ℕ) : (Fin N → ℂ) →L[ℂ] ℂ :=
  ∑ i : Fin N, ContinuousLinearMap.proj i

/-- The continuous linear charge sum has the expected coordinate formula. -/
theorem chargeSumCLM_apply {N : ℕ} (α : Fin N → ℂ) :
    chargeSumCLM N α = ∑ i, α i := by
  simp [chargeSumCLM]

/-- The finite-radius Wick normalization is a holomorphic quadratic polynomial. -/
noncomputable def vertexWickPolynomial {N : ℕ} (v : Fin N → ℝ)
    (α : Fin N → ℂ) : ℂ := - (∑ i, α i ^ 2 * (v i : ℂ)) / 2

/-- Finite-radius charge observables retain the unweighted mass independently of the charges. -/
noncomputable def finiteVertexMoment
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (O : Set ℂ)
    (γ : ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ) (α : Fin N → ℂ) : ℂ :=
  ∫ ω, Complex.exp
    (vertexWickPolynomial (fun i => gaussianVariance P (fun ω' => Xc ω' (z i) (r i))) α +
      ∑ i, α i * (Xc ω (z i) (r i) : ℂ)) *
    ((M ω O).toReal : ℂ) ^
      (- (((-2 * Q γ / γ : ℝ) : ℂ) + (γ : ℂ)⁻¹ * ∑ i, α i)) ∂P


end DOZZ.Proofs
