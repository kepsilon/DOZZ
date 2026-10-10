/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.MixedRealVertexTilt
public import DOZZ.Correlations.Analytic.MixedRetainedKernel

/-! Measurable complex mass increments and their real vertex tilt. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Complex powers of measurable nonnegative real masses are measurable, including at zero. -/
theorem measurable_cpow_nonnegative
    {A : Type*} [MeasurableSpace A] (f : A → ℝ) (hf : Measurable f)
    (hn : ∀ a, 0 ≤ f a) (p : ℂ) : Measurable (fun a => (f a : ℂ) ^ p) := by
  have he : (fun a => (f a : ℂ) ^ p) = fun a =>
      if f a = 0 then (if p = 0 then 1 else 0) else Complex.exp ((Real.log (f a) : ℂ) * p) := by
    funext a
    rw [Complex.cpow_def, ← Complex.ofReal_log (hn a)]
    simp only [Complex.ofReal_eq_zero]
  rw [he]
  exact Measurable.ite (measurableSet_eq_fun hf measurable_const) measurable_const
    (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (Real.measurable_log.comp hf)).mul_const p))

/-- The norm of a difference of complex chaos-mass powers is a measurable functional of the
measure, so the GMC tilt `DOZZ.equatorGFF_GMC_tilt` can be used after taking absolute values. -/
theorem measurable_complex_mass_difference
    (O₁ O₀ : Set ℂ) (h₁ : MeasurableSet O₁) (h₀ : MeasurableSet O₀) (p : ℂ) :
    Measurable (fun μ : Measure ℂ => ENNReal.ofReal
      ‖((μ O₁).toReal : ℂ) ^ p - ((μ O₀).toReal : ℂ) ^ p‖) := by
  have hm (O : Set ℂ) (hO : MeasurableSet O) :
      Measurable (fun μ : Measure ℂ => ((μ O).toReal : ℂ) ^ p) :=
    measurable_cpow_nonnegative _
      (ENNReal.measurable_toReal.comp (Measure.measurable_coe hO))
      (fun _ => ENNReal.toReal_nonneg) p
  exact ENNReal.measurable_ofReal.comp ((hm O₁ h₁).sub (hm O₀ h₀)).norm

/-- Mixed real circle vertices tilt every measurable chaos functional. -/
theorem mixed_vertex_tilt_functional
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (a : Fin N → ℝ) (z : Fin N → ℂ) (r : Fin N → ℝ)
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((∑ i, a i * Xc ω (z i) (r i)) -
      gaussianVariance P (fun ω' => ∑ i, a i * Xc ω' (z i) (r i)) / 2)) * H (M ω) ∂P) =
      ∫⁻ ω, H ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
        (γ * ∑ i, a i * ∫ v, gffKernel x v ∂circleMeasure (z i) (r i))))) ∂P := by
  let L : Ω → ℝ := fun ω => ∑ i, a i * Xc ω (z i) (r i)
  have hL := circle_vertices_gaussianL2Limit P X hX Xc hXc a z r
  obtain ⟨c, hc, hcov⟩ := mixed_circle_covariance_uniform P X hX Xc hXc a z r
  have ht := equatorGFF_GMC_tilt P X hX γ hγ hγ2 M hM Xc hXc L hL c hcov
    (fun _ μ => H μ) (hH.comp measurable_snd)
  simpa only [L, hc] using ht

end DOZZ.Proofs
