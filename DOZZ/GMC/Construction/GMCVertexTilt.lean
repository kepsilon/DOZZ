/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTiltLimit
public import DOZZ.GMC.Construction.GMCVertexTiltReduction

/-! Proof of `DOZZ.equatorGFF_GMC_vertex_tilt` (exact vertex-insertion tilt) from the general GMC
tilt theorem. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The finite-circle vertex tilt is the specialization of the general chaos tilt to a finite
linear combination of circle averages. -/
theorem equatorGFF_GMC_vertex_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (r : ℝ)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp ((∑ k, α k * Xc ω (z k) r) -
        gaussianVariance P (fun ω' => ∑ k, α k * Xc ω' (z k) r) / 2)) *
        H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + ∑ k, α k * circleCross (z k) r f)
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * ∑ k, α k * ∫ v, gffKernel x v ∂circleMeasure (z k) r)))) ∂P := by
  apply equatorGFF_GMC_vertex_tilt_of_general_tilt P X hX γ hγ hγ2 M hM Xc hXc α z r H hH
  intro hγ' hγ2' hM' hH' L hL c hc
  exact equatorGFF_GMC_tilt P X hX γ hγ' hγ2' M hM' Xc hXc L hL c hc H hH'

end DOZZ.Proofs
