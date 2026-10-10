/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.SharpMoments.TiltCutoff

/-! The statement `DOZZ.equatorGFF_GMC_tilt_cutoff`,
proved by `DOZZ.Proofs.equatorGFF_GMC_tilt_cutoff`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Cameron–Martin for joint functionals of the test coordinates, one cutoff chaos and the limit
chaos: tilting by `L` multiplies the cutoff chaos by `exp (γ Cov(X_r(x), L))` and the limit chaos
by `exp (γ c)`. With `L = γ X_r(u)` and Tonelli this gives finite-cutoff rooting. -/
theorem equatorGFF_GMC_tilt_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x r) L) c atTop)
    (r : ℝ) (H : (TestFn → ℝ) → Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ × Measure ℂ =>
      H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (regularizedGMC P Xc γ r ω) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω => Xc ω x r) L))))
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P := by exact DOZZ.Proofs.equatorGFF_GMC_tilt_cutoff P X hX γ hγ hγ2 M hM Xc hXc L hL c hc r H hH

end DOZZ
