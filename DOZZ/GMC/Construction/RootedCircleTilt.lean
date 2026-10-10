/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.GMCVertexTilt

/-! A finite-circle root tilt with the limiting GMC as the chaos mark. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The exact single-circle tilt retains an arbitrary limiting chaos version as its mark. -/
theorem gmc_joint_single_circle_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (u : ℂ) (r : ℝ)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Xc ω u r - γ ^ 2 / 2 *
        ∫ ω', Xc ω' u r ^ 2 ∂P)) * H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + γ * circleCross u r f)
        ((M ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u r)))) ∂P := by
  have hvar : gaussianVariance P (fun ω => γ * Xc ω u r) =
      γ ^ 2 * ∫ ω, Xc ω u r ^ 2 ∂P := by
    rw [gaussianVariance, gaussianCovariance]
    calc
      _ = ∫ ω, γ ^ 2 * Xc ω u r ^ 2 ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ fun ω => by ring
      _ = _ := integral_const_mul _ _
  have ht := equatorGFF_GMC_vertex_tilt P X hX γ hγ hγ2 M hM Xc hXc
    (fun _ : Fin 1 => γ) (fun _ => u) r H hH
  simp only [Fin.sum_univ_one] at ht
  rw [hvar] at ht
  have hleft (ω : Ω) : γ * Xc ω u r -
      (γ ^ 2 * ∫ ω', Xc ω' u r ^ 2 ∂P) / 2 =
      γ * Xc ω u r - γ ^ 2 / 2 * ∫ ω', Xc ω' u r ^ 2 ∂P := by ring
  have hright (x : ℂ) : γ * (γ * ∫ v, gffKernel x v ∂circleMeasure u r) =
      γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u r := by ring
  simpa only [hleft, hright] using ht

end DOZZ.Proofs
