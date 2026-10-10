/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GaussianRegression

/-! The translated Gaussian decomposition of the one-insertion tail estimate, retaining the
correlated equator pin. The residual lateral family is independent of the pin. The radial Brownian
motion is independent of their entire joint block. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Tests supported inside the punctured insertion disk. -/
abbrev offCenterTest (z : ℂ) :=
  {ψ : TestFn // tsupport ψ ⊆ {w : ℂ | 0 < ‖w - z‖ ∧ ‖w - z‖ < 1}}

/-- The actual off-center lateral evaluation, before removing its regression on the pin. -/
noncomputable def offCenterLateral {Ω : Type*} (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (ψ : offCenterTest z) (ω : Ω) : ℝ :=
  X ω ψ.val - ∫ w : ℂ, ψ.val w * Xc ω z (-Real.log ‖w - z‖)

/-- The deterministic coefficient of the pin in the lateral Gaussian regression. -/
noncomputable def offCenterRegressionCoefficient (z : ℂ)
    (ψ : offCenterTest z) : ℝ :=
  (∫ w : ℂ, ψ.val w * (Real.log ‖w‖ - Real.log ‖z‖)) / (2 * Real.log ‖z‖)

/-- The pin variance is strictly positive throughout the compact-center geometry of the
one-insertion tail estimate. -/
theorem offCenter_pin_variance_pos (z : ℂ) (hz : 2 ≤ ‖z‖) :
    0 < 2 * Real.log ‖z‖ := by
  exact mul_pos (by norm_num) (Real.log_pos (by linarith))

/-- Off-center Brownian motion is independent of the pin and its regressed lateral field.
The pin and the regressed lateral field are independent of each other as well. -/
theorem offCenter_regression_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X)
    (hc : IsCircleAverage P X Xc)
    (hmeas : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω z t - Xc ω z 0) P ∧
    IsGaussianProcess (fun j : Option (offCenterTest z) => fun ω =>
      j.elim (Xc ω z 0) (fun ψ => offCenterLateral X Xc z ψ ω -
        offCenterRegressionCoefficient z ψ * Xc ω z 0)) P ∧
    IndepFun (fun ω => Xc ω z 0)
      (fun ω => fun ψ : offCenterTest z => offCenterLateral X Xc z ψ ω -
        offCenterRegressionCoefficient z ψ * Xc ω z 0) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω z t - Xc ω z 0)
      (fun ω => fun j : Option (offCenterTest z) =>
        j.elim (Xc ω z 0) (fun ψ => offCenterLateral X Xc z ψ ω -
          offCenterRegressionCoefficient z ψ * Xc ω z 0)) P := by
  let Z : Option (offCenterTest z) → Ω → ℝ := fun j ω =>
    j.elim (Xc ω z 0) (fun ψ => offCenterLateral X Xc z ψ ω)
  let a := offCenterRegressionCoefficient z
  have hD := circleAverage_offCenter_decomposition P X Xc hX hc hmeas hcont z hz
  have hZ : IsGaussianProcess Z P := hD.1
  have ha (ψ : offCenterTest z) :
      covariance (Z (some ψ)) (Z none) P / (2 * Real.log ‖z‖) = a ψ := by
    change covariance (offCenterLateral X Xc z ψ) (fun ω => Xc ω z 0) P /
      (2 * Real.log ‖z‖) = _
    unfold offCenterLateral
    rw [hD.2.2.2.1 ψ]
    rfl
  refine ⟨circleAverage_exterior_brownian P X Xc hX hc hcont z hz,
    gaussian_regression_process P Z hZ a, ?_, ?_⟩
  · have h := gaussian_regression_indep P Z hZ (2 * Real.log ‖z‖)
      (offCenter_pin_variance_pos z hz).ne' hD.2.2.1
    simp only [ha] at h
    exact h
  · let T : (Option (offCenterTest z) → ℝ) →
        (Option (offCenterTest z) → ℝ) := fun f j =>
      j.elim (f none) (fun ψ => f (some ψ) - a ψ * f none)
    have hm : Measurable T := by
      apply Measurable.of_eval
      intro j
      cases j with
      | none => exact measurable_pi_apply none
      | some ψ =>
        change Measurable (fun f : Option (offCenterTest z) → ℝ =>
          f (some ψ) - a ψ * f none)
        fun_prop
    exact hD.2.1.comp measurable_id hm



end DOZZ.Proofs
