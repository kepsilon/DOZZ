/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.MixedRadiusTiltPotential
public import DOZZ.GMC.Construction.GMCGeneralTiltLimit

/-! Real vertex tilting with mixed inward and outward circle radii. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Inward and outward vertices at different radii tilt the same retained mass by the sum of their
exact averaged Green kernels. This applies the general GMC tilt `DOZZ.equatorGFF_GMC_tilt` with
proved premises. -/
theorem mixed_vertex_tilt_retained_mass
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (O : Set ℂ) (ho : MeasurableSet O) (p : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((∑ i, α i * Xc ω (z i) (r i)) -
      gaussianVariance P (fun ω' => ∑ i, α i * Xc ω' (z i) (r i)) / 2)) * M ω O ^ p ∂P) =
    ∫⁻ ω, ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
      (γ * ∑ i, α i * ∫ v, gffKernel x v ∂circleMeasure (z i) (r i)))) O) ^ p ∂P := by
  let L : Ω → ℝ := fun ω => ∑ i, α i * Xc ω (z i) (r i)
  have hL := circle_vertices_gaussianL2Limit P X hX Xc hXc α z r
  obtain ⟨c, hc, hcov⟩ := mixed_circle_covariance_uniform P X hX Xc hXc α z r
  let H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun _ μ => μ O ^ p
  have hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2) :=
    ((Measure.measurable_coe ho).comp measurable_snd).pow_const p
  have ht := equatorGFF_GMC_tilt P X hX γ hγ hγ2 M hM Xc hXc L hL c hcov H hH
  simpa only [L, H, hc] using ht

end DOZZ.Proofs
