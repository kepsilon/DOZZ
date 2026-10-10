/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Construction.GMCGeneralTiltLimit

/-! The statement `DOZZ.equatorGFF_GMC_tilt`, proved by `DOZZ.Proofs.equatorGFF_GMC_tilt`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Cameron–Martin for chaos functionals: tilting by any `L` in the Gaussian `L²` closure shifts
the test coordinates by `Cov(X(f), L)` and multiplies the chaos by `exp (γ c)`, where `c` is the
uniform limit of the circle-average covariance potential `x ↦ Cov(X_r(x), L)`. -/
theorem equatorGFF_GMC_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x r) L) c atTop)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P := by exact DOZZ.Proofs.equatorGFF_GMC_tilt P X hX γ hγ hγ2 M hM Xc hXc L hL c hc H hH

end DOZZ
