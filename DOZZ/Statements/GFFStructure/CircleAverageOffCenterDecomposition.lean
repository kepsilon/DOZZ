/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.OffCenterDecomposition

/-! The statement `DOZZ.circleAverage_offCenter_decomposition`,
proved by `DOZZ.Proofs.circleAverage_offCenter_decomposition`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Off-center radial decomposition, used in [KRV, §7.1]. For a jointly measurable continuous
witness, `N = X_0(z)`, `B_t = X_t(z) - N`, and the lateral field
`Y_z(ψ) = X(ψ) - ∫ ψ(w) X_{-log|w-z|}(z)` on tests in the punctured unit disk about `z`. -/
theorem circleAverage_offCenter_decomposition {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) :
    IsGaussianProcess (fun j : Option {ψ : TestFn //
        tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}} => fun ω =>
      j.elim (Xc ω z 0) fun ψ => X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖)) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω z t - Xc ω z 0)
      (fun ω => fun j : Option {ψ : TestFn //
          tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}} =>
        j.elim (Xc ω z 0) fun ψ =>
          X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖)) P ∧
    covariance (fun ω => Xc ω z 0) (fun ω => Xc ω z 0) P = 2 * Real.log ‖z‖ ∧
    (∀ ψ : {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}},
      covariance (fun ω => X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖))
        (fun ω => Xc ω z 0) P =
        ∫ w : ℂ, ψ.val w * (Real.log ‖w‖ - Real.log ‖z‖)) ∧
    (∀ ψ χ : {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}},
      covariance (fun ω => X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖))
        (fun ω => X ω χ.val - ∫ w : ℂ, χ.val w * Xc ω z (-Real.log ‖w - z‖)) P =
        ∫ w : ℂ, ψ.val w * ∫ w' : ℂ,
          (-Real.log ‖w - w'‖ + Real.log (max ‖w - z‖ ‖w' - z‖)) * χ.val w') := by exact DOZZ.Proofs.circleAverage_offCenter_decomposition P X Xc hX hc hmeas hcont z hz

end DOZZ
