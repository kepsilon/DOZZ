/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GffRootCovariance
import DOZZ.GMC.Construction.GMCVertexTilt

/-! The statement `DOZZ.equatorGFF_GMC_vertex_tilt`,
proved by `DOZZ.Proofs.equatorGFF_GMC_vertex_tilt`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Cameron–Martin tilt by a regularized vertex insertion, jointly translating the field and
its chaos. The pointwise chaos density is the averaged Green potential of the insertion circles.
See [KRV, (Z1)] and [KRV, Theorem 12.1]. -/
theorem equatorGFF_GMC_vertex_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (r : ℝ)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((∑ k, α k * Xc ω (z k) r) -
        gaussianVariance P (fun ω' => ∑ k, α k * Xc ω' (z k) r) / 2)) *
        H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + ∑ k, α k * circleCross (z k) r f)
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r)))) ∂P := by exact DOZZ.Proofs.equatorGFF_GMC_vertex_tilt P X hX γ hγ hγ2 M hM Xc hXc α z r H hH

end DOZZ
