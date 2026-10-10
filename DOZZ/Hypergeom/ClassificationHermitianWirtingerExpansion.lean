/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianDecomposition
public import DOZZ.Hypergeom.ClassificationWirtingerBarAnalytic

/-! The conjugate derivatives of a real solution are computed from its Cramer coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- Conjugating the real Gauss PDE gives its conjugate-Wirtinger form. -/
theorem realGaussSolution_conjugate_pde
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {z : ℂ} (hz : z ∈ gaussRegularPlane) :
    wirtingerBar (fun w => wirtingerBar (fun u => (T u : ℂ)) w) z +
        star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
          wirtingerBar (fun w => (T w : ℂ)) z -
        star ((a : ℂ) * b / (z * (1 - z))) * (T z : ℂ) = 0 := by
  let t : ℂ → ℂ := fun w => (T w : ℂ)
  have hself : (fun w => star (t w)) = t := by
    funext w
    simp [t]
  have hconj :
      star (wirtingerZ (fun w => wirtingerZ t w) z) +
        star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
          star (wirtingerZ t z) -
        star ((a : ℂ) * b / (z * (1 - z))) * t z = 0 := by
    have h := congrArg star (hT.2 z hz)
    simpa [t, hself] using h
  rw [wirtingerBar_wirtingerBar_eq_star_wirtingerZ_wirtingerZ hself]
  have hbar : wirtingerBar t z = star (wirtingerZ t z) := by
    unfold wirtingerBar
    rw [hself]
  rw [hbar]
  exact hconj

/-- The first conjugate Wirtinger derivative of a real Gauss solution is the corresponding
combination of conjugate derivatives of its Cramer coefficients. -/
theorem realGaussCramer_wirtingerBar_expansion
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      wirtingerBar (fun w => (T w : ℂ)) z =
        f z * wirtingerBar (gaussCramerCoefficient₁ T f g) z +
          g z * wirtingerBar (gaussCramerCoefficient₂ T f g) z := by
  intro z hz
  have hzReg : z ∈ gaussRegularPlane := gaussCutPlane_subset_regularPlane hz
  have hTAtReal : ContDiffAt ℝ 2 T z :=
    (hT.1 z hzReg).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hzReg)
  have hTAt : ContDiffAt ℝ 2 (fun w => (T w : ℂ)) z := by
    change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hTAtReal
  have ht0 : DifferentiableAt ℝ (fun w => (T w : ℂ)) z :=
    hTAt.differentiableAt (by norm_num)
  have hcoeff := realGaussCramerCoefficients_wirtingerZ_eq_zero
    a b c T hT hf hg hODEf hODEg hW
  obtain ⟨hαAt, _, hβAt, _⟩ := hcoeff z hz
  have hfAt := (hf z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  have hsumAt : DifferentiableAt ℝ
      (fun w => gaussCramerCoefficient₁ T f g w * f w +
        gaussCramerCoefficient₂ T f g w * g w) z := by
    exact (hαAt.mul (hfAt.restrictScalars ℝ)).add
      (hβAt.mul (hgAt.restrictScalars ℝ))
  have hEq : (fun w => (T w : ℂ)) =ᶠ[𝓝 z]
      (fun w => gaussCramerCoefficient₁ T f g w * f w +
        gaussCramerCoefficient₂ T f g w * g w) := by
    filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw
    exact (realGaussCramer_reconstruct T (hW w hw)).1
  calc
    wirtingerBar (fun w => (T w : ℂ)) z =
        wirtingerBar (fun w => gaussCramerCoefficient₁ T f g w * f w +
          gaussCramerCoefficient₂ T f g w * g w) z :=
      wirtingerBar_congr_of_eventuallyEq ht0 hsumAt hEq
    _ = f z * wirtingerBar (gaussCramerCoefficient₁ T f g) z +
          g z * wirtingerBar (gaussCramerCoefficient₂ T f g) z := by
      have h₁At : DifferentiableAt ℝ
          (fun w => gaussCramerCoefficient₁ T f g w * f w) z :=
        hαAt.mul (hfAt.restrictScalars ℝ)
      have h₂At : DifferentiableAt ℝ
          (fun w => gaussCramerCoefficient₂ T f g w * g w) z :=
        hβAt.mul (hgAt.restrictScalars ℝ)
      rw [wirtingerBar_add h₁At h₂At,
        wirtingerBar_mul hαAt (hfAt.restrictScalars ℝ),
        wirtingerBar_mul hβAt (hgAt.restrictScalars ℝ),
        wirtingerBar_eq_zero_of_differentiableAt hfAt,
        wirtingerBar_eq_zero_of_differentiableAt hgAt]
      ring

/-- The second conjugate Wirtinger derivative is likewise the basis-weighted sum of the second
conjugate derivatives of the coefficients. -/
theorem realGaussCramer_wirtingerBar_second_expansion
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      wirtingerBar (fun w => wirtingerBar (fun u => (T u : ℂ)) w) z =
        f z * wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₁ T f g) w) z +
        g z * wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₂ T f g) w) z := by
  intro z hz
  have hzReg : z ∈ gaussRegularPlane := gaussCutPlane_subset_regularPlane hz
  have hTAtReal : ContDiffAt ℝ 2 T z :=
    (hT.1 z hzReg).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hzReg)
  have hTAt : ContDiffAt ℝ 2 (fun w => (T w : ℂ)) z := by
    change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hTAtReal
  let t0 : ℂ → ℂ := fun w => (T w : ℂ)
  have ht1At : DifferentiableAt ℝ (fun w => wirtingerZ t0 w) z :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hTAt
  have hself : (fun w => star (t0 w)) = t0 := by
    funext w
    simp [t0]
  have hbarTfun : (fun w => wirtingerBar t0 w) =
      (fun w => star (wirtingerZ t0 w)) := by
    funext w
    unfold wirtingerBar
    rw [hself]
  have hclmT : DifferentiableAt ℝ (starRingEnd ℂ) (wirtingerZ t0 z) :=
    Complex.differentiable_conj.differentiableAt (x := wirtingerZ t0 z)
  have hbarTAt : DifferentiableAt ℝ (fun w => wirtingerBar t0 w) z := by
    rw [hbarTfun]
    exact hclmT.comp z ht1At
  have hcoeff := realGaussCramerCoefficients_wirtingerZ_eq_zero
    a b c T hT hf hg hODEf hODEg hW
  have hconjAnalytic := realGaussCramer_conjugates_analytic
    a b c T hT hf hg hODEf hODEg hW
  obtain ⟨hαAt, _, hβAt, _⟩ := hcoeff z hz
  have hαBarAt := differentiableAt_wirtingerBar_of_analytic_conjugate
    gaussCutPlane_isOpen hconjAnalytic.1 hz
  have hβBarAt := differentiableAt_wirtingerBar_of_analytic_conjugate
    gaussCutPlane_isOpen hconjAnalytic.2 hz
  have hfAt := (hf z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  let S : ℂ → ℂ := fun w =>
    f w * wirtingerBar (gaussCramerCoefficient₁ T f g) w +
      g w * wirtingerBar (gaussCramerCoefficient₂ T f g) w
  have hS₁At : DifferentiableAt ℝ
      (fun w => f w * wirtingerBar (gaussCramerCoefficient₁ T f g) w) z :=
    (hfAt.restrictScalars ℝ).mul hαBarAt
  have hS₂At : DifferentiableAt ℝ
      (fun w => g w * wirtingerBar (gaussCramerCoefficient₂ T f g) w) z :=
    (hgAt.restrictScalars ℝ).mul hβBarAt
  have hSAt : DifferentiableAt ℝ S z := by
    dsimp [S]
    exact hS₁At.add hS₂At
  have hfirst : (fun w => wirtingerBar t0 w) =ᶠ[𝓝 z] S := by
    filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw
    exact realGaussCramer_wirtingerBar_expansion
      a b c T hT hf hg hODEf hODEg hW w hw
  have hSbar : wirtingerBar S z =
      f z * wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₁ T f g) w) z +
        g z * wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₂ T f g) w) z := by
    have hprod₁ : DifferentiableAt ℝ
        (fun w => f w * wirtingerBar (gaussCramerCoefficient₁ T f g) w) z := hS₁At
    have hprod₂ : DifferentiableAt ℝ
        (fun w => g w * wirtingerBar (gaussCramerCoefficient₂ T f g) w) z := hS₂At
    calc
      wirtingerBar S z =
          wirtingerBar (fun w => f w * wirtingerBar
            (gaussCramerCoefficient₁ T f g) w) z +
          wirtingerBar (fun w => g w * wirtingerBar
            (gaussCramerCoefficient₂ T f g) w) z := by
        exact wirtingerBar_add hprod₁ hprod₂
      _ = _ := by
        rw [wirtingerBar_mul (hfAt.restrictScalars ℝ) hαBarAt,
          wirtingerBar_mul (hgAt.restrictScalars ℝ) hβBarAt,
          wirtingerBar_eq_zero_of_differentiableAt hfAt,
          wirtingerBar_eq_zero_of_differentiableAt hgAt]
        ring
  calc
    wirtingerBar (fun w => wirtingerBar t0 w) z = wirtingerBar S z :=
      wirtingerBar_congr_of_eventuallyEq hbarTAt hSAt hfirst
    _ = _ := hSbar

/-- After expanding the conjugated real PDE in a holomorphic fundamental pair, the two Cramer
coefficients' conjugate Gauss residuals have zero basis-weighted sum. -/
theorem realGaussCramer_conjugate_pde_expansion
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      f z * (wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₁ T f g) w) z +
          star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
            wirtingerBar (gaussCramerCoefficient₁ T f g) z -
          star ((a : ℂ) * b / (z * (1 - z))) *
            gaussCramerCoefficient₁ T f g z) +
        g z * (wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₂ T f g) w) z +
          star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
            wirtingerBar (gaussCramerCoefficient₂ T f g) z -
          star ((a : ℂ) * b / (z * (1 - z))) *
            gaussCramerCoefficient₂ T f g z) = 0 := by
  intro z hz
  have hzReg := gaussCutPlane_subset_regularPlane hz
  have hPDE := realGaussSolution_conjugate_pde a b c T hT hzReg
  have hbar := realGaussCramer_wirtingerBar_expansion
    a b c T hT hf hg hODEf hODEg hW z hz
  have hbarbar := realGaussCramer_wirtingerBar_second_expansion
    a b c T hT hf hg hODEf hODEg hW z hz
  have hrec := (realGaussCramer_reconstruct T (hW z hz)).1
  rw [hbarbar, hbar, hrec] at hPDE
  linear_combination hPDE

end DOZZ.Proofs
