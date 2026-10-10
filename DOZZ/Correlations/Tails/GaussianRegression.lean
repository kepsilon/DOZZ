/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.OffCenterDecomposition
public import DOZZ.Statements.GFFStructure.CircleAverageExteriorBrownian

/-! Gaussian regression of the correlated off-center pin in the one-insertion tail argument.
The radial Brownian motion is independent of the entire pin/lateral block;
subtracting the regression on the pin separates that block into independent parts. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Regression on a nondegenerate coordinate preserves joint Gaussianity. -/
theorem gaussian_regression_process {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Option I → Ω → ℝ) (hZ : IsGaussianProcess Z P)
    (a : I → ℝ) :
    IsGaussianProcess (fun j : Option I => fun ω =>
      j.elim (Z none ω) (fun i => Z (some i) ω - a i * Z none ω)) P := by
  classical
  apply hZ.of_isGaussianProcess
  intro j
  let S : Finset (Option I) := {j, none}
  let p : S := ⟨j, by simp [S]⟩
  let q : S := ⟨none, by simp [S]⟩
  let L : (S → ℝ) →L[ℝ] ℝ :=
    match j with
    | none => ContinuousLinearMap.proj q
    | some i => ContinuousLinearMap.proj p - a i • ContinuousLinearMap.proj q
  refine ⟨S, L, fun ω => ?_⟩
  cases j <;> simp [L, p, q, Finset.restrict_def]

/-- The regression residual is independent of the pin. No independence of the original
lateral field and the pin is asserted. -/
theorem gaussian_regression_indep {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Option I → Ω → ℝ) (hZ : IsGaussianProcess Z P)
    (v : ℝ) (hv : v ≠ 0) (hvar : covariance (Z none) (Z none) P = v) :
    IndepFun (Z none)
      (fun ω => fun i => Z (some i) ω -
        covariance (Z (some i)) (Z none) P / v * Z none ω) P := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  let a := fun i => covariance (Z (some i)) (Z none) P / v
  have hG := gaussian_regression_process P Z hZ a
  have hJoint : IsGaussianProcess
      (Sum.elim (fun _ : Unit => Z none)
        (fun i ω => Z (some i) ω - a i * Z none ω)) P := by
    convert hG.comp_right (Sum.elim (fun _ : Unit => (none : Option I)) some) using 1
    funext j ω
    cases j <;> rfl
  have h := hJoint.indepFun_of_covariance_eq_zero
    (fun _ => hZ.aemeasurable none) (fun i => hG.aemeasurable (some i))
    (fun _ i => ?_)
  · exact h.comp (measurable_pi_apply ()) measurable_id
  · have hN := (hZ.hasGaussianLaw_eval none).memLp_two
    have hY := (hZ.hasGaussianLaw_eval (some i)).memLp_two
    rw [covariance_comm, covariance_fun_sub_left hY (hN.const_mul (a i)) hN,
      covariance_const_mul_left, hvar]
    dsimp [a]
    rw [div_mul_cancel₀ _ hv, sub_self]

end DOZZ.Proofs
