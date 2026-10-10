/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.WirtingerZ
public import DOZZ.Statements.Hypergeom.IsRealGaussSolution
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! First-order calculus rules for the Wirtinger derivative. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- The Wirtinger derivative obeys the ordinary product rule for real-differentiable
complex-valued functions. -/
theorem wirtingerZ_mul {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerZ (fun w => f w * g w) z =
      f z * wirtingerZ g z + g z * wirtingerZ f z := by
  rw [wirtingerZ, wirtingerZ, wirtingerZ, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply]
  ring

/-- The Wirtinger derivative is additive on functions differentiable at the point. -/
theorem wirtingerZ_add {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    wirtingerZ (fun w => f w + g w) z = wirtingerZ f z + wirtingerZ g z := by
  have hfd : fderiv ℝ (fun w => f w + g w) z = fderiv ℝ f z + fderiv ℝ g z := by
    exact fderiv_add hf hg
  rw [wirtingerZ, wirtingerZ, wirtingerZ, hfd]
  simp only [add_apply]
  ring

/-- On a complex-differentiable function, the Wirtinger derivative is the ordinary complex
derivative. -/
theorem wirtingerZ_eq_deriv_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    wirtingerZ f z = deriv f z := by
  have hfR : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have hCR := (differentiableAt_complex_iff_differentiableAt_real.mp hf).2
  have hI : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
    simpa only [smul_eq_mul] using hCR
  rw [wirtingerZ, hI, complexOfReal_deriv hfR hCR]
  rw [← mul_assoc, Complex.I_mul_I]
  ring

/-- The Wirtinger derivative annihilates the conjugate of a holomorphic function. -/
theorem wirtingerZ_star_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) :
    wirtingerZ (fun w => star (f w)) z = 0 := by
  have hfR : DifferentiableAt ℝ f z := hf.restrictScalars ℝ
  have hCR := (differentiableAt_complex_iff_differentiableAt_real.mp hf).2
  have hI : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := by
    simpa only [smul_eq_mul] using hCR
  rw [wirtingerZ, fderiv_star]
  simp only [ContinuousLinearMap.comp_apply]
  change (star (fderiv ℝ f z 1) -
      Complex.I * star (fderiv ℝ f z Complex.I)) / 2 = 0
  rw [hI]
  rw [star_mul]
  simp only [Complex.star_def, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- A holomorphic times antiholomorphic tensor has the expected `z`-derivative. -/
theorem wirtingerZ_mul_star_of_differentiableAt {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    wirtingerZ (fun w => f w * star (g w)) z =
      star (g z) * deriv f z := by
  rw [wirtingerZ_mul (hf.restrictScalars ℝ) ((hg.restrictScalars ℝ).star),
    wirtingerZ_star_eq_zero_of_differentiableAt hg,
    wirtingerZ_eq_deriv_of_differentiableAt hf]
  simp

/-- The first Wirtinger derivative of a holomorphic-antiholomorphic tensor is differentiable
as a real function of the evaluation point. -/
theorem differentiableAt_wirtingerZ_mul_star_of_analyticOnNhd
    {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    {z : ℂ} (hz : z ∈ U) :
    DifferentiableAt ℝ (fun w => wirtingerZ (fun u => f u * star (g u)) w) z := by
  have hfd : AnalyticOnNhd ℂ (deriv f) U := hf.deriv
  have hfdAt : DifferentiableAt ℂ (deriv f) z := (hfd z hz).differentiableAt
  have hgAt : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
  have hEq : (fun w => wirtingerZ (fun u => f u * star (g u)) w) =ᶠ[𝓝 z]
      (fun w => deriv f w * star (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [wirtingerZ_mul_star_of_differentiableAt
      (hf w hw).differentiableAt (hg w hw).differentiableAt]
    ring
  have hRightDiff : DifferentiableAt ℝ (fun w => deriv f w * star (g w)) z :=
    (hfdAt.restrictScalars ℝ).mul ((hgAt.restrictScalars ℝ).star)
  exact hRightDiff.congr_of_eventuallyEq hEq

/-- The Wirtinger derivative is unchanged when two functions agree near the evaluation point. -/
theorem wirtingerZ_congr_of_eventuallyEq {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z)
    (hfg : f =ᶠ[𝓝 z] g) :
    wirtingerZ f z = wirtingerZ g z := by
  have hfd : fderiv ℝ f z = fderiv ℝ g z := by
    have hF : HasFDerivAt f (fderiv ℝ f z) z := hf.hasFDerivAt
    have hG : HasFDerivAt g (fderiv ℝ f z) z := hfg.hasFDerivAt_iff.mp hF
    exact hG.unique hg.hasFDerivAt
  rw [wirtingerZ, wirtingerZ, hfd]

/-- The second Wirtinger derivative of an analytic tensor `f · star(g)` differentiates
only its holomorphic factor. -/
theorem wirtingerZ_second_mul_star_of_analyticOnNhd
    {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    {z : ℂ} (hz : z ∈ U) :
    wirtingerZ (fun w => wirtingerZ (fun u => f u * star (g u)) w) z =
      star (g z) * deriv (deriv f) z := by
  have hfd : AnalyticOnNhd ℂ (deriv f) U := hf.deriv
  have hfAt : DifferentiableAt ℂ f z := (hf z hz).differentiableAt
  have hgAt : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
  have hfdAt : DifferentiableAt ℂ (deriv f) z := (hfd z hz).differentiableAt
  have hEq : (fun w => wirtingerZ (fun u => f u * star (g u)) w) =ᶠ[𝓝 z]
      (fun w => deriv f w * star (g w)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [wirtingerZ_mul_star_of_differentiableAt
      (hf w hw).differentiableAt (hg w hw).differentiableAt]
    ring
  have hRightDiff : DifferentiableAt ℝ (fun w => deriv f w * star (g w)) z :=
    (hfdAt.restrictScalars ℝ).mul ((hgAt.restrictScalars ℝ).star)
  have hLeftDiff : DifferentiableAt ℝ
      (fun w => wirtingerZ (fun u => f u * star (g u)) w) z :=
    hRightDiff.congr_of_eventuallyEq hEq
  calc
    _ = wirtingerZ (fun w => deriv f w * star (g w)) z :=
      wirtingerZ_congr_of_eventuallyEq hLeftDiff hRightDiff hEq
    _ = star (g z) * deriv (deriv f) z :=
      wirtingerZ_mul_star_of_differentiableAt hfdAt hgAt

/-- If the holomorphic factor solves the Gauss ODE, its tensor with an antiholomorphic factor
satisfies the `z`-PDE at every regular point. -/
theorem realGaussTensor_pde_of_holomorphicSolution
    (a b c : ℝ) {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hODE : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f w = 0)
    {z : ℂ} (hz : z ∈ U) (hzReg : z ∈ gaussRegularPlane) :
    wirtingerZ (fun w => wirtingerZ (fun u => f u * star (g u)) w) z +
        ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
          wirtingerZ (fun w => f w * star (g w)) z -
        (a : ℂ) * b / (z * (1 - z)) * (f z * star (g z)) = 0 := by
  rw [wirtingerZ_second_mul_star_of_analyticOnNhd hU hf hg hz,
    wirtingerZ_mul_star_of_differentiableAt
      (hf z hz).differentiableAt (hg z hz).differentiableAt]
  have hzden : z * (1 - z) ≠ 0 :=
    mul_ne_zero hzReg.1 (sub_ne_zero.mpr (Ne.symm hzReg.2))
  have hzden' : z - z ^ 2 ≠ 0 := by
    convert hzden using 1; ring
  have hode := hODE z hz
  dsimp [gaussHolomorphicOperator] at hode
  have hode' : z * (1 - z) * deriv (deriv f) z +
      ((c : ℂ) - z * ((a : ℂ) + b + 1)) * deriv f z -
      (a : ℂ) * b * f z = 0 := by
    convert hode using 1; ring
  calc
    _ = star (g z) *
        (z * (1 - z) * deriv (deriv f) z +
          ((c : ℂ) - z * ((a : ℂ) + b + 1)) * deriv f z -
          (a : ℂ) * b * f z) / (z * (1 - z)) := by
      field_simp [hzden']
      ring_nf
      have hcancel : z * (z - z ^ 2)⁻¹ - z ^ 2 * (z - z ^ 2)⁻¹ = 1 := by
        rw [← sub_mul, mul_inv_cancel₀ hzden']
      linear_combination -star (g z) * deriv (deriv f) z * hcancel
    _ = 0 := by rw [hode']; simp

/-- A sum of two analytic holomorphic-antiholomorphic Gauss tensors still satisfies the
Wirtinger PDE. -/
theorem realGaussTensor_pde_add_of_holomorphicSolutions
    (a b c : ℝ) {U : Set ℂ} (hU : IsOpen U)
    {f₁ g₁ f₂ g₂ : ℂ → ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ U) (hg₁ : AnalyticOnNhd ℂ g₁ U)
    (hODE₁ : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f₁ w = 0)
    (hf₂ : AnalyticOnNhd ℂ f₂ U) (hg₂ : AnalyticOnNhd ℂ g₂ U)
    (hODE₂ : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f₂ w = 0)
    {z : ℂ} (hz : z ∈ U) (hzReg : z ∈ gaussRegularPlane) :
    wirtingerZ (fun w => wirtingerZ
          (fun u => f₁ u * star (g₁ u) + f₂ u * star (g₂ u)) w) z +
        ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
          wirtingerZ (fun w => f₁ w * star (g₁ w) + f₂ w * star (g₂ w)) z -
        (a : ℂ) * b / (z * (1 - z)) *
          (f₁ z * star (g₁ z) + f₂ z * star (g₂ z)) = 0 := by
  let q₁ : ℂ → ℂ := fun w => f₁ w * star (g₁ w)
  let q₂ : ℂ → ℂ := fun w => f₂ w * star (g₂ w)
  have hq₁ : DifferentiableAt ℝ q₁ z :=
    ((hf₁ z hz).differentiableAt.restrictScalars ℝ).mul
      (((hg₁ z hz).differentiableAt.restrictScalars ℝ).star)
  have hq₂ : DifferentiableAt ℝ q₂ z :=
    ((hf₂ z hz).differentiableAt.restrictScalars ℝ).mul
      (((hg₂ z hz).differentiableAt.restrictScalars ℝ).star)
  have hfirst : wirtingerZ (fun w => q₁ w + q₂ w) z =
      wirtingerZ q₁ z + wirtingerZ q₂ z := wirtingerZ_add hq₁ hq₂
  have hinnerEq : (fun w => wirtingerZ (fun u => q₁ u + q₂ u) w) =ᶠ[𝓝 z]
      (fun w => wirtingerZ q₁ w + wirtingerZ q₂ w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact wirtingerZ_add
      (((hf₁ w hw).differentiableAt.restrictScalars ℝ).mul
        (((hg₁ w hw).differentiableAt.restrictScalars ℝ).star))
      (((hf₂ w hw).differentiableAt.restrictScalars ℝ).mul
        (((hg₂ w hw).differentiableAt.restrictScalars ℝ).star))
  have hinnerRightDiff : DifferentiableAt ℝ
      (fun w => wirtingerZ q₁ w + wirtingerZ q₂ w) z :=
    (differentiableAt_wirtingerZ_mul_star_of_analyticOnNhd hU hf₁ hg₁ hz).add
      (differentiableAt_wirtingerZ_mul_star_of_analyticOnNhd hU hf₂ hg₂ hz)
  have hinnerLeftDiff : DifferentiableAt ℝ
      (fun w => wirtingerZ (fun u => q₁ u + q₂ u) w) z :=
    hinnerRightDiff.congr_of_eventuallyEq hinnerEq
  have hsecond :
      wirtingerZ (fun w => wirtingerZ (fun u => q₁ u + q₂ u) w) z =
        wirtingerZ (fun w => wirtingerZ q₁ w) z +
          wirtingerZ (fun w => wirtingerZ q₂ w) z := by
    calc
      _ = wirtingerZ (fun w => wirtingerZ q₁ w + wirtingerZ q₂ w) z :=
        wirtingerZ_congr_of_eventuallyEq hinnerLeftDiff hinnerRightDiff hinnerEq
      _ = _ := wirtingerZ_add
        (differentiableAt_wirtingerZ_mul_star_of_analyticOnNhd hU hf₁ hg₁ hz)
        (differentiableAt_wirtingerZ_mul_star_of_analyticOnNhd hU hf₂ hg₂ hz)
  have hPDE₁ := realGaussTensor_pde_of_holomorphicSolution a b c hU hf₁ hg₁
    hODE₁ hz hzReg
  have hPDE₂ := realGaussTensor_pde_of_holomorphicSolution a b c hU hf₂ hg₂
    hODE₂ hz hzReg
  rw [hsecond, hfirst]
  dsimp [q₁, q₂] at *
  linear_combination hPDE₁ + hPDE₂


end DOZZ.Proofs
