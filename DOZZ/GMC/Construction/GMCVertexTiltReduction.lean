/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.Construction.GMCVertexTiltInputs

/-! The vertex-insertion identity reduces to the general GMC chaos-tilt identity. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- If the general chaos-tilt identity is available for every Gaussian `L²` limit and every
uniform covariance limit, then its specialization to a finite weighted collection of insertion
circles is the vertex-tilt identity. The single premise is the general tilt identity; the
specialization inputs are proved in `GMCVertexTiltInputs`. -/
theorem equatorGFF_GMC_vertex_tilt_of_general_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (r : ℝ)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2))
    (hTilt : (_hγ : 0 < γ) → (_hγ2 : γ < 2) →
      (_hM : IsGMCOf P X γ M) →
      (_hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) →
      ∀ (L : Ω → ℝ) (_hL : IsGaussianL2Limit P X L)
      (c : BoundedContinuousFunction ℂ ℝ)
      (_hc : TendstoUniformly
        (fun (s : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x s) L) c atTop),
      (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
          H (fun f => X ω f) (M ω) ∂P) =
        ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
          ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((∑ k, α k * Xc ω (z k) r) -
        gaussianVariance P (fun ω' => ∑ k, α k * Xc ω' (z k) r) / 2)) *
        H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + ∑ k, α k * circleCross (z k) r f)
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r)))) ∂P := by
  classical
  let L : Ω → ℝ := fun ω => ∑ k, α k * Xc ω (z k) r
  have hL : IsGaussianL2Limit P X L := by
    simpa only [L] using
      circleAverage_sum_isGaussianL2Limit P X hX Xc hXc α z r
  obtain ⟨c, hpotential, hcov⟩ :=
    circleAverage_sum_covariance_uniform P X hX Xc hXc α z r
  have hshift (f : TestFn) :
      gaussianCovariance P (fun ω => X ω f) L =
        ∑ k, α k * circleCross (z k) r f := by
    simpa only [L] using
      circleAverage_sum_test_covariance P X hX Xc hXc α z r f
  have hfield (ω : Ω) :
      (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L) =
        (fun f => X ω f + ∑ k, α k * circleCross (z k) r f) := by
    funext f
    exact congrArg (fun q : ℝ => X ω f + q) (hshift f)
  have hdensity :
      (fun x => ENNReal.ofReal (Real.exp (γ * c x))) =
        (fun x => ENNReal.ofReal (Real.exp
          (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r))) := by
    funext x
    rw [hpotential x]
  have hmeasure (ω : Ω) :
      (M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x))) =
        (M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r))) :=
    congrArg (fun d : ℂ → ℝ≥0∞ => (M ω).withDensity d) hdensity
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (M ω) ∂P := by
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by simp only [L])
    _ = ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
          ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P :=
      hTilt hγ hγ2 hM hH L hL c hcov
    _ = ∫⁻ ω, H (fun f => X ω f + ∑ k, α k * circleCross (z k) r f)
          ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
            (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r)))) ∂P := by
      apply lintegral_congr_ae
      exact ae_of_all _ (fun ω => by
        change H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
            ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) =
          H (fun f => X ω f + ∑ k, α k * circleCross (z k) r f)
            ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
              (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r))))
        rw [hfield ω, hmeasure ω])

end DOZZ.Proofs
