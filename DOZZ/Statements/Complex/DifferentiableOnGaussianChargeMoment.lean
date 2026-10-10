/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.ComplexPolydisc
import DOZZ.Complex.Charge

/-! The statement `DOZZ.differentiableOn_gaussian_charge_moment`,
proved by `DOZZ.Proofs.differentiableOn_gaussian_charge_moment`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Actual Gaussian charge/mass observable of the proof of [KRV, Theorem 6.1]. Gaussian
coordinates may be correlated with the positive mass. Positive mass moments have a strict
threshold; no entire-parameter claim is made. -/
theorem differentiableOn_gaussian_charge_moment {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set (Fin N → ℂ)) (hU : IsOpen U)
    (L : Ω → Fin N → ℝ) (hL : ProbabilityTheory.HasGaussianLaw L P)
    (A : Ω → ℝ) (hA : AEMeasurable A P) (hpos : ∀ᵐ ω ∂P, 0 < A ω)
    (pstar : ℝ) (hpstar : 0 < pstar)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => A ω ^ (-q)) P)
    (hmom : ∀ p : ℝ, 0 ≤ p → p < pstar → Integrable (fun ω => A ω ^ p) P)
    (c : (Fin N → ℂ) → ℂ) (hc : DifferentiableOn ℂ c U)
    (s₀ : ℂ) (sL : (Fin N → ℂ) →L[ℂ] ℂ) :
    (∀ z ∈ {z ∈ U | -(s₀ + sL z).re < pstar},
      Integrable (fun ω => Complex.exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z))) P) ∧
    DifferentiableOn ℂ
      (fun z => ∫ ω, Complex.exp (c z + ∑ i, z i * (L ω i : ℂ)) *
        (A ω : ℂ) ^ (-(s₀ + sL z)) ∂P)
      {z ∈ U | -(s₀ + sL z).re < pstar} := by exact DOZZ.Proofs.differentiableOn_gaussian_charge_moment P U hU L hL A hA hpos pstar hpstar hinv hmom c hc s₀ sL

end DOZZ
