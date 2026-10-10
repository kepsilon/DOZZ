/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.ComplexPolydisc
import DOZZ.Complex.Basic

/-! The statement `DOZZ.differentiableOn_integral_polydisc`,
proved by `DOZZ.Proofs.differentiableOn_integral_polydisc`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Thin polydisc packaging of Mathlib's dominated Fréchet integral derivative (see
[KRV, Theorem 6.1]). The envelope bounds the first derivative; integrability at the center
supplies the value. This does not assert that the paper's random integrand meets these analytic
hypotheses. -/
theorem differentiableOn_integral_polydisc {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (a : Fin N → ℂ) (R : Fin N → ℝ)
    (hR : ∀ i, 0 < R i) (F : (Fin N → ℂ) → Ω → ℂ)
    (F' : (Fin N → ℂ) → Ω → ((Fin N → ℂ) →L[ℂ] ℂ)) (bound : Ω → ℝ)
    (hF : ∀ z ∈ complexPolydisc a R, AEStronglyMeasurable (F z) P)
    (hF' : ∀ z ∈ complexPolydisc a R, AEStronglyMeasurable (F' z) P)
    (hbase : Integrable (F a) P) (hbound : Integrable bound P)
    (hdom : ∀ᵐ ω ∂P, ∀ z ∈ complexPolydisc a R, ‖F' z ω‖ ≤ bound ω)
    (hderiv : ∀ᵐ ω ∂P, ∀ z ∈ complexPolydisc a R,
      HasFDerivAt (fun w => F w ω) (F' z ω) z) :
    DifferentiableOn ℂ (fun z => ∫ ω, F z ω ∂P) (complexPolydisc a R) ∧
      ∀ z ∈ complexPolydisc a R,
        Integrable (F z) P ∧ Integrable (F' z) P ∧
        HasFDerivAt (fun w => ∫ ω, F w ω ∂P) (∫ ω, F' z ω ∂P) z := by exact DOZZ.Proofs.differentiableOn_integral_polydisc P a R hR F F' bound hF hF' hbase hbound hdom hderiv

end DOZZ
