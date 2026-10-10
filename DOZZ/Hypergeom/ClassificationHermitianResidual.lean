/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianWirtingerExpansion

/-! The conjugated PDE and its `∂z` derivative separate the two Cramer coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- The two Cramer coefficients of a real Gauss solution each satisfy the conjugated Gauss
equation. The proof differentiates their basis-weighted residual identity in the `∂z`
direction and uses the nonzero basis Wronskian. -/
theorem realGaussCramer_conjugate_residuals_eq_zero
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
      wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₁ T f g) w) z +
          star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
            wirtingerBar (gaussCramerCoefficient₁ T f g) z -
          star ((a : ℂ) * b / (z * (1 - z))) *
            gaussCramerCoefficient₁ T f g z = 0 ∧
      wirtingerBar (fun w => wirtingerBar
          (gaussCramerCoefficient₂ T f g) w) z +
          star (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) *
            wirtingerBar (gaussCramerCoefficient₂ T f g) z -
          star ((a : ℂ) * b / (z * (1 - z))) *
            gaussCramerCoefficient₂ T f g z = 0 := by
  intro z hz
  let α : ℂ → ℂ := gaussCramerCoefficient₁ T f g
  let β : ℂ → ℂ := gaussCramerCoefficient₂ T f g
  let p : ℂ → ℂ := fun w =>
    ((c : ℂ) - w * ((a : ℂ) + b + 1)) / (w * (1 - w))
  let q : ℂ → ℂ := fun w => (a : ℂ) * b / (w * (1 - w))
  let R₁ : ℂ → ℂ := fun w =>
    wirtingerBar (fun u => wirtingerBar α u) w +
      star (p w) * wirtingerBar α w - star (q w) * α w
  let R₂ : ℂ → ℂ := fun w =>
    wirtingerBar (fun u => wirtingerBar β u) w +
      star (p w) * wirtingerBar β w - star (q w) * β w
  have hzReg : z ∈ gaussRegularPlane := gaussCutPlane_subset_regularPlane hz
  have hden : z * (1 - z) ≠ 0 :=
    mul_ne_zero hzReg.1 (sub_ne_zero.mpr (Ne.symm hzReg.2))
  have hdenAt : DifferentiableAt ℂ (fun w : ℂ => w * (1 - w)) z := by
    exact differentiableAt_id.mul (differentiableAt_id.const_sub 1)
  have hpAt : DifferentiableAt ℂ p z := by
    have hmul : DifferentiableAt ℂ
        (fun w : ℂ => w * ((a : ℂ) + b + 1)) z :=
      differentiableAt_id.mul (differentiableAt_const _)
    have hnum : DifferentiableAt ℂ
        (fun w : ℂ => (c : ℂ) - w * ((a : ℂ) + b + 1)) z :=
      (differentiableAt_const _).sub hmul
    change DifferentiableAt ℂ
      (fun w => ((c : ℂ) - w * ((a : ℂ) + b + 1)) / (w * (1 - w))) z
    exact hnum.div hdenAt hden
  have hqAt : DifferentiableAt ℂ q z := by
    change DifferentiableAt ℂ
      (fun w => (a : ℂ) * b / (w * (1 - w))) z
    exact (differentiableAt_const ((a : ℂ) * b)).div hdenAt hden
  have hpStarAt : DifferentiableAt ℝ (fun w => star (p w)) z := by
    have hclm := Complex.differentiable_conj.differentiableAt (x := p z)
    exact hclm.comp z (hpAt.restrictScalars ℝ)
  have hqStarAt : DifferentiableAt ℝ (fun w => star (q w)) z := by
    have hclm := Complex.differentiable_conj.differentiableAt (x := q z)
    exact hclm.comp z (hqAt.restrictScalars ℝ)
  have hcoeff := realGaussCramerCoefficients_wirtingerZ_eq_zero
    a b c T hT hf hg hODEf hODEg hW
  obtain ⟨hαAt, hαz, hβAt, hβz⟩ := hcoeff z hz
  have hconjAnalytic := realGaussCramer_conjugates_analytic
    a b c T hT hf hg hODEf hODEg hW
  have hαConj : AnalyticOnNhd ℂ (fun w => star (α w)) gaussCutPlane := by
    simpa [α] using hconjAnalytic.1
  have hβConj : AnalyticOnNhd ℂ (fun w => star (β w)) gaussCutPlane := by
    simpa [β] using hconjAnalytic.2
  have hαBarAt := differentiableAt_wirtingerBar_of_analytic_conjugate
    gaussCutPlane_isOpen hαConj hz
  have hβBarAt := differentiableAt_wirtingerBar_of_analytic_conjugate
    gaussCutPlane_isOpen hβConj hz
  have hαBarBarAt := differentiableAt_wirtingerBar_wirtingerBar_of_analytic_conjugate
    gaussCutPlane_isOpen hαConj hz
  have hβBarBarAt := differentiableAt_wirtingerBar_wirtingerBar_of_analytic_conjugate
    gaussCutPlane_isOpen hβConj hz
  have hαBarZ := wirtingerZ_wirtingerBar_eq_zero_of_analytic_conjugate
    gaussCutPlane_isOpen hαConj hz
  have hβBarZ := wirtingerZ_wirtingerBar_eq_zero_of_analytic_conjugate
    gaussCutPlane_isOpen hβConj hz
  have hαBarBarZ := wirtingerZ_wirtingerBar_wirtingerBar_eq_zero_of_analytic_conjugate
    gaussCutPlane_isOpen hαConj hz
  have hβBarBarZ := wirtingerZ_wirtingerBar_wirtingerBar_eq_zero_of_analytic_conjugate
    gaussCutPlane_isOpen hβConj hz
  have hpStarZ := wirtingerZ_star_eq_zero_of_differentiableAt hpAt
  have hqStarZ := wirtingerZ_star_eq_zero_of_differentiableAt hqAt
  have hR₁pAt : DifferentiableAt ℝ (fun w => star (p w) * wirtingerBar α w) z :=
    hpStarAt.mul hαBarAt
  have hR₁qAt : DifferentiableAt ℝ (fun w => star (q w) * α w) z :=
    hqStarAt.mul hαAt
  have hR₂pAt : DifferentiableAt ℝ (fun w => star (p w) * wirtingerBar β w) z :=
    hpStarAt.mul hβBarAt
  have hR₂qAt : DifferentiableAt ℝ (fun w => star (q w) * β w) z :=
    hqStarAt.mul hβAt
  have hR₁At : DifferentiableAt ℝ R₁ z := by
    dsimp [R₁]
    exact (hαBarBarAt.add hR₁pAt).sub hR₁qAt
  have hR₂At : DifferentiableAt ℝ R₂ z := by
    dsimp [R₂]
    exact (hβBarBarAt.add hR₂pAt).sub hR₂qAt
  have hR₁pZ : wirtingerZ (fun w => star (p w) * wirtingerBar α w) z = 0 := by
    rw [wirtingerZ_mul hpStarAt hαBarAt, hpStarZ, hαBarZ]
    simp
  have hR₁qZ : wirtingerZ (fun w => star (q w) * α w) z = 0 := by
    rw [wirtingerZ_mul hqStarAt hαAt, hqStarZ, hαz]
    simp
  have hR₂pZ : wirtingerZ (fun w => star (p w) * wirtingerBar β w) z = 0 := by
    rw [wirtingerZ_mul hpStarAt hβBarAt, hpStarZ, hβBarZ]
    simp
  have hR₂qZ : wirtingerZ (fun w => star (q w) * β w) z = 0 := by
    rw [wirtingerZ_mul hqStarAt hβAt, hqStarZ, hβz]
    simp
  have hR₁Z : wirtingerZ R₁ z = 0 := by
    dsimp [R₁]
    let A : ℂ → ℂ := fun w => wirtingerBar (fun u => wirtingerBar α u) w
    let B : ℂ → ℂ := fun w => star (p w) * wirtingerBar α w
    let C : ℂ → ℂ := fun w => star (q w) * α w
    change wirtingerZ (fun w => A w + B w - C w) z = 0
    have hshape : (fun w => A w + B w - C w) = (fun w => (A + B) w - C w) := by
      funext w
      rfl
    rw [hshape, wirtingerZ_sub (hαBarBarAt.add hR₁pAt) hR₁qAt]
    change wirtingerZ (fun w => A w + B w) z - wirtingerZ C z = 0
    rw [wirtingerZ_add hαBarBarAt hR₁pAt]
    change wirtingerZ A z + wirtingerZ B z - wirtingerZ C z = 0
    change wirtingerZ B z = 0 at hR₁pZ
    rw [hR₁pZ]
    simp only [add_zero]
    change wirtingerZ A z = 0 at hαBarBarZ
    change wirtingerZ C z = 0 at hR₁qZ
    rw [hαBarBarZ, hR₁qZ]
    simp
  have hR₂Z : wirtingerZ R₂ z = 0 := by
    dsimp [R₂]
    let A : ℂ → ℂ := fun w => wirtingerBar (fun u => wirtingerBar β u) w
    let B : ℂ → ℂ := fun w => star (p w) * wirtingerBar β w
    let C : ℂ → ℂ := fun w => star (q w) * β w
    change wirtingerZ (fun w => A w + B w - C w) z = 0
    have hshape : (fun w => A w + B w - C w) = (fun w => (A + B) w - C w) := by
      funext w
      rfl
    rw [hshape, wirtingerZ_sub (hβBarBarAt.add hR₂pAt) hR₂qAt]
    change wirtingerZ (fun w => A w + B w) z - wirtingerZ C z = 0
    rw [wirtingerZ_add hβBarBarAt hR₂pAt]
    change wirtingerZ A z + wirtingerZ B z - wirtingerZ C z = 0
    change wirtingerZ B z = 0 at hR₂pZ
    rw [hR₂pZ]
    simp only [add_zero]
    change wirtingerZ A z = 0 at hβBarBarZ
    change wirtingerZ C z = 0 at hR₂qZ
    rw [hβBarBarZ, hR₂qZ]
    simp
  have hE := realGaussCramer_conjugate_pde_expansion
    a b c T hT hf hg hODEf hODEg hW z hz
  have hE0 : f z * R₁ z + g z * R₂ z = 0 := by
    simpa [R₁, R₂, α, β, p, q] using hE
  have hfAt := (hf z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  let E : ℂ → ℂ := fun w => f w * R₁ w + g w * R₂ w
  have hEAt : DifferentiableAt ℝ E z := by
    dsimp [E]
    exact ((hfAt.restrictScalars ℝ).mul hR₁At).add
      ((hgAt.restrictScalars ℝ).mul hR₂At)
  have hEzero : E =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
    filter_upwards [gaussCutPlane_isOpen.mem_nhds hz] with w hw
    have h := realGaussCramer_conjugate_pde_expansion
      a b c T hT hf hg hODEf hODEg hW w hw
    simpa [E, R₁, R₂, α, β, p, q] using h
  have hEderiv : wirtingerZ E z = 0 := by
    calc
      wirtingerZ E z = wirtingerZ (fun _ => (0 : ℂ)) z :=
        wirtingerZ_congr_of_eventuallyEq hEAt (differentiableAt_const (0 : ℂ)) hEzero
      _ = 0 := by simp [wirtingerZ]
  have hEderivSum :
      wirtingerZ (fun w => f w * R₁ w + g w * R₂ w) z = 0 := by
    simpa [E] using hEderiv
  have hleftDeriv : wirtingerZ (fun w => f w * R₁ w) z = deriv f z * R₁ z := by
    rw [wirtingerZ_mul (hfAt.restrictScalars ℝ) hR₁At,
      hR₁Z, wirtingerZ_eq_deriv_of_differentiableAt hfAt]
    ring
  have hrightDeriv : wirtingerZ (fun w => g w * R₂ w) z = deriv g z * R₂ z := by
    rw [wirtingerZ_mul (hgAt.restrictScalars ℝ) hR₂At,
      hR₂Z, wirtingerZ_eq_deriv_of_differentiableAt hgAt]
    ring
  have hleftDerivFun : wirtingerZ (f * R₁) z = deriv f z * R₁ z := by
    change wirtingerZ (fun w => f w * R₁ w) z = _
    exact hleftDeriv
  have hrightDerivFun : wirtingerZ (g * R₂) z = deriv g z * R₂ z := by
    change wirtingerZ (fun w => g w * R₂ w) z = _
    exact hrightDeriv
  have hE1 : deriv f z * R₁ z + deriv g z * R₂ z = 0 := by
    change wirtingerZ (fun w => (f * R₁) w + (g * R₂) w) z = 0 at hEderivSum
    rw [wirtingerZ_add
      ((hfAt.restrictScalars ℝ).mul hR₁At)
      ((hgAt.restrictScalars ℝ).mul hR₂At)] at hEderivSum
    calc
      _ = wirtingerZ (f * R₁) z + wirtingerZ (g * R₂) z := by
        rw [hleftDerivFun, hrightDerivFun]
      _ = 0 := hEderivSum
  have hR₁det : gaussCramerWronskian f g z * R₁ z = 0 := by
    dsimp [gaussCramerWronskian]
    linear_combination deriv g z * hE0 - g z * hE1
  have hR₂det : gaussCramerWronskian f g z * R₂ z = 0 := by
    dsimp [gaussCramerWronskian]
    linear_combination f z * hE1 - deriv f z * hE0
  have hR₁zero : R₁ z = 0 := (mul_eq_zero.mp hR₁det).resolve_left (hW z hz)
  have hR₂zero : R₂ z = 0 := (mul_eq_zero.mp hR₂det).resolve_left (hW z hz)
  constructor
  · simpa [R₁, α, p, q] using hR₁zero
  · simpa [R₂, β, p, q] using hR₂zero

/-- Conjugating the Cramer coefficients gives two holomorphic solutions of the original Gauss
ODE on the slit plane. -/
theorem realGaussCramer_conjugates_solve_gauss
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (fun w => star (gaussCramerCoefficient₁ T f g w)) z = 0) ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (fun w => star (gaussCramerCoefficient₂ T f g w)) z = 0) := by
  have hconjAnalytic := realGaussCramer_conjugates_analytic
    a b c T hT hf hg hODEf hODEg hW
  have hres := realGaussCramer_conjugate_residuals_eq_zero
    a b c T hT hf hg hODEf hODEg hW
  constructor
  · intro z hz
    let α : ℂ → ℂ := gaussCramerCoefficient₁ T f g
    let A : ℂ → ℂ := fun w => star (α w)
    have hAanalytic : AnalyticOnNhd ℂ A gaussCutPlane := by
      simpa [A, α] using hconjAnalytic.1
    have hbar : wirtingerBar α z = star (deriv A z) := by
      exact wirtingerBar_eq_star_deriv_of_star_differentiableAt
        (hAanalytic z hz).differentiableAt (by rfl)
    have hbarbar : wirtingerBar (fun w => wirtingerBar α w) z =
        star (deriv (deriv A) z) := by
      exact wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate
        gaussCutPlane_isOpen hAanalytic hz
    have hbarStar : star (wirtingerBar α z) = deriv A z := by
      rw [hbar]
      simp
    have hbarbarStar : star (wirtingerBar (fun w => wirtingerBar α w) z) =
        deriv (deriv A) z := by
      rw [hbarbar]
      simp
    have hnorm : deriv (deriv A) z +
        (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) * deriv A z -
        ((a : ℂ) * b / (z * (1 - z))) * A z = 0 := by
      have hc := congrArg star (hres z hz).1
      simp only [star_add, star_sub, star_mul, star_zero, star_star] at hc
      rw [hbarbarStar, hbarStar] at hc
      convert hc using 1
      ring
    have hden : z * (1 - z) ≠ 0 := by
      have hzReg := gaussCutPlane_subset_regularPlane hz
      exact mul_ne_zero hzReg.1 (sub_ne_zero.mpr (Ne.symm hzReg.2))
    let d : ℂ := z * (1 - z)
    let m : ℂ := (c : ℂ) - z * ((a : ℂ) + b + 1)
    let n : ℂ := (a : ℂ) * b
    have hnorm' : deriv (deriv A) z + (m / d) * deriv A z -
        (n / d) * A z = 0 := by
      simpa [m, n, d] using hnorm
    have hm : d * (m / d) = m := mul_div_cancel₀ m hden
    have hn : d * (n / d) = n := mul_div_cancel₀ n hden
    have hmD : d * ((m / d) * deriv A z) = m * deriv A z := by
      calc
        d * ((m / d) * deriv A z) = (d * (m / d)) * deriv A z := by ring
        _ = m * deriv A z := by rw [hm]
    have hnA : d * ((n / d) * A z) = n * A z := by
      calc
        d * ((n / d) * A z) = (d * (n / d)) * A z := by ring
        _ = n * A z := by rw [hn]
    have hdist : d * (deriv (deriv A) z + (m / d) * deriv A z -
        (n / d) * A z) =
        d * deriv (deriv A) z + m * deriv A z - n * A z := by
      calc
        _ = d * deriv (deriv A) z + d * ((m / d) * deriv A z) -
            d * ((n / d) * A z) := by ring
        _ = _ := by rw [hmD, hnA]
    have hnum : d * deriv (deriv A) z + m * deriv A z - n * A z = 0 := by
      calc
        _ = d * (deriv (deriv A) z + (m / d) * deriv A z - (n / d) * A z) := hdist.symm
        _ = 0 := by rw [hnorm']; simp
    dsimp [gaussHolomorphicOperator]
    convert hnum using 1
    dsimp [d, m, n, A, α]
    ring_nf
  · intro z hz
    let β : ℂ → ℂ := gaussCramerCoefficient₂ T f g
    let B : ℂ → ℂ := fun w => star (β w)
    have hBanalytic : AnalyticOnNhd ℂ B gaussCutPlane := by
      simpa [B, β] using hconjAnalytic.2
    have hbar : wirtingerBar β z = star (deriv B z) := by
      exact wirtingerBar_eq_star_deriv_of_star_differentiableAt
        (hBanalytic z hz).differentiableAt (by rfl)
    have hbarbar : wirtingerBar (fun w => wirtingerBar β w) z =
        star (deriv (deriv B) z) := by
      exact wirtingerBar_wirtingerBar_eq_star_deriv_deriv_of_analytic_conjugate
        gaussCutPlane_isOpen hBanalytic hz
    have hbarStar : star (wirtingerBar β z) = deriv B z := by
      rw [hbar]
      simp
    have hbarbarStar : star (wirtingerBar (fun w => wirtingerBar β w) z) =
        deriv (deriv B) z := by
      rw [hbarbar]
      simp
    have hnorm : deriv (deriv B) z +
        (((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z))) * deriv B z -
        ((a : ℂ) * b / (z * (1 - z))) * B z = 0 := by
      have hc := congrArg star (hres z hz).2
      simp only [star_add, star_sub, star_mul, star_zero, star_star] at hc
      rw [hbarbarStar, hbarStar] at hc
      convert hc using 1
      ring
    have hden : z * (1 - z) ≠ 0 := by
      have hzReg := gaussCutPlane_subset_regularPlane hz
      exact mul_ne_zero hzReg.1 (sub_ne_zero.mpr (Ne.symm hzReg.2))
    let d : ℂ := z * (1 - z)
    let m : ℂ := (c : ℂ) - z * ((a : ℂ) + b + 1)
    let n : ℂ := (a : ℂ) * b
    have hnorm' : deriv (deriv B) z + (m / d) * deriv B z -
        (n / d) * B z = 0 := by
      simpa [m, n, d] using hnorm
    have hm : d * (m / d) = m := mul_div_cancel₀ m hden
    have hn : d * (n / d) = n := mul_div_cancel₀ n hden
    have hmD : d * ((m / d) * deriv B z) = m * deriv B z := by
      calc
        d * ((m / d) * deriv B z) = (d * (m / d)) * deriv B z := by ring
        _ = m * deriv B z := by rw [hm]
    have hnB : d * ((n / d) * B z) = n * B z := by
      calc
        d * ((n / d) * B z) = (d * (n / d)) * B z := by ring
        _ = n * B z := by rw [hn]
    have hdist : d * (deriv (deriv B) z + (m / d) * deriv B z -
        (n / d) * B z) =
        d * deriv (deriv B) z + m * deriv B z - n * B z := by
      calc
        _ = d * deriv (deriv B) z + d * ((m / d) * deriv B z) -
            d * ((n / d) * B z) := by ring
        _ = _ := by rw [hmD, hnB]
    have hnum : d * deriv (deriv B) z + m * deriv B z - n * B z = 0 := by
      calc
        _ = d * (deriv (deriv B) z + (m / d) * deriv B z - (n / d) * B z) := hdist.symm
        _ = 0 := by rw [hnorm']; simp
    dsimp [gaussHolomorphicOperator]
    convert hnum using 1
    dsimp [d, m, n, B, β]
    ring_nf

/-- Each conjugate Cramer coefficient has constant coordinates in any global analytic Gauss
fundamental pair on the slit plane. -/
theorem realGaussCramer_conjugates_have_constant_basis_coordinates
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    ∃ u v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
      star (gaussCramerCoefficient₁ T f g z) = u.1 * f z + u.2 * g z ∧
      star (gaussCramerCoefficient₂ T f g z) = v.1 * f z + v.2 * g z := by
  have hconjAnalytic := realGaussCramer_conjugates_analytic
    a b c T hT hf hg hODEf hODEg hW
  have hconjODE := realGaussCramer_conjugates_solve_gauss
    a b c T hT hf hg hODEf hODEg hW
  obtain ⟨u, hu, _⟩ := gauss_two_solution_span_unique
    (a : ℂ) (b : ℂ) (c : ℂ) f g hf.differentiableOn hg.differentiableOn
    hODEf hODEg (fun z hz => hW z hz)
    (fun z => star (gaussCramerCoefficient₁ T f g z))
    hconjAnalytic.1.differentiableOn hconjODE.1
  obtain ⟨v, hv, _⟩ := gauss_two_solution_span_unique
    (a : ℂ) (b : ℂ) (c : ℂ) f g hf.differentiableOn hg.differentiableOn
    hODEf hODEg (fun z hz => hW z hz)
    (fun z => star (gaussCramerCoefficient₂ T f g z))
    hconjAnalytic.2.differentiableOn hconjODE.2
  refine ⟨u, v, ?_⟩
  intro z hz
  exact ⟨hu z hz, hv z hz⟩

end DOZZ.Proofs
