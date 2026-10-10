/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisSpanning
public import DOZZ.Hypergeom.ClassificationWirtingerC2
import Mathlib.Analysis.Complex.RealDeriv

/-! The Cramer coefficients of a real Gauss PDE solution are antiholomorphic. -/

@[expose] public section

namespace DOZZ.Proofs

noncomputable def gaussCramerWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - deriv f z * g z

noncomputable def gaussCramerNumerator₁ (T : ℂ → ℝ) (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (T z : ℂ) * deriv g z -
    wirtingerZ (fun w => (T w : ℂ)) z * g z

noncomputable def gaussCramerNumerator₂ (T : ℂ → ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * wirtingerZ (fun w => (T w : ℂ)) z - deriv f z * (T z : ℂ)

noncomputable def gaussCramerCoefficient₁ (T : ℂ → ℝ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  gaussCramerNumerator₁ T g z * (gaussCramerWronskian f g z)⁻¹

noncomputable def gaussCramerCoefficient₂ (T : ℂ → ℝ) (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  gaussCramerNumerator₂ T f z * (gaussCramerWronskian f g z)⁻¹

/-- On the regular slit plane, the two Cramer coefficients of a real PDE solution have zero
`∂z` derivative. The proof uses the scalar PDE as a first-order system for `(T, ∂z T)`;
the numerator and the Wronskian then satisfy the same Abel equation. -/
theorem realGaussCramerCoefficients_wirtingerZ_eq_zero
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
      DifferentiableAt ℝ (gaussCramerCoefficient₁ T f g) z ∧
        wirtingerZ (gaussCramerCoefficient₁ T f g) z = 0 ∧
      DifferentiableAt ℝ (gaussCramerCoefficient₂ T f g) z ∧
        wirtingerZ (gaussCramerCoefficient₂ T f g) z = 0 := by
  intro z hz
  have hzReg : z ∈ gaussRegularPlane := gaussCutPlane_subset_regularPlane hz
  let den : ℂ := z * (1 - z)
  have hden : den ≠ 0 := by
    dsimp [den]
    exact mul_ne_zero hzReg.1 (sub_ne_zero.mpr (Ne.symm hzReg.2))
  have hTAtReal : ContDiffAt ℝ 2 T z :=
    (hT.1 z hzReg).contDiffAt (gaussRegularPlane_isOpen.mem_nhds hzReg)
  have hTAt : ContDiffAt ℝ 2 (fun w => (T w : ℂ)) z := by
    change ContDiffAt ℝ 2 (fun w => Complex.ofRealCLM (T w)) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hTAtReal
  let t₀ : ℂ → ℂ := fun w => (T w : ℂ)
  let t₁ : ℂ → ℂ := fun w => wirtingerZ t₀ w
  let t₂ : ℂ → ℂ := fun w => wirtingerZ t₁ w
  have ht₀ : DifferentiableAt ℝ t₀ z := hTAt.differentiableAt (by norm_num)
  have ht₁ : DifferentiableAt ℝ t₁ z :=
    differentiableAt_wirtingerZ_of_contDiffAt_two hTAt
  have ht₀z : wirtingerZ t₀ z = t₁ z := rfl
  have hPDE := hT.2 z hzReg
  let pz : ℂ := (z * ((a : ℂ) + b + 1) - c) / den
  let qz : ℂ := (a * b) / den
  have hPDE' :
      t₂ z + ((c : ℂ) - z * ((a : ℂ) + b + 1)) / den * t₁ z -
        (a * b) / den * t₀ z = 0 := by
    change wirtingerZ (wirtingerZ (fun w => (T w : ℂ))) z +
        ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
          wirtingerZ (fun w => (T w : ℂ)) z -
        (a : ℂ) * b / (z * (1 - z)) * (T z : ℂ) = 0
    exact hPDE
  have ht₂ : t₂ z = pz * t₁ z + qz * t₀ z := by
    have hpz : pz = -(((c : ℂ) - z * ((a : ℂ) + b + 1)) / den) := by
      dsimp [pz]
      ring
    rw [hpz]
    dsimp [qz]
    linear_combination hPDE'
  have hfAt : DifferentiableAt ℂ f z := (hf z hz).differentiableAt
  have hgAt : DifferentiableAt ℂ g z := (hg z hz).differentiableAt
  have hf₁At : DifferentiableAt ℂ (deriv f) z := (hf.deriv z hz).differentiableAt
  have hg₁At : DifferentiableAt ℂ (deriv g) z := (hg.deriv z hz).differentiableAt
  have hODEf' : deriv (deriv f) z = pz * deriv f z + qz * f z := by
    have h := hODEf z hz
    dsimp [gaussHolomorphicOperator] at h
    have hmul : den * deriv (deriv f) z =
        (z * ((a : ℂ) + b + 1) - c) * deriv f z + (a * b) * f z := by
      dsimp [den]
      linear_combination h
    have hscaled : den * (pz * deriv f z + qz * f z) =
        (z * ((a : ℂ) + b + 1) - c) * deriv f z + (a * b) * f z := by
      simp only [pz, qz]
      field_simp [hden]
    apply mul_left_cancel₀ hden
    calc
      den * deriv (deriv f) z =
          (z * ((a : ℂ) + b + 1) - c) * deriv f z + (a * b) * f z := hmul
      _ = den * (pz * deriv f z + qz * f z) := hscaled.symm
  have hODEg' : deriv (deriv g) z = pz * deriv g z + qz * g z := by
    have h := hODEg z hz
    dsimp [gaussHolomorphicOperator] at h
    have hmul : den * deriv (deriv g) z =
        (z * ((a : ℂ) + b + 1) - c) * deriv g z + (a * b) * g z := by
      dsimp [den]
      linear_combination h
    have hscaled : den * (pz * deriv g z + qz * g z) =
        (z * ((a : ℂ) + b + 1) - c) * deriv g z + (a * b) * g z := by
      simp only [pz, qz]
      field_simp [hden]
    apply mul_left_cancel₀ hden
    calc
      den * deriv (deriv g) z =
          (z * ((a : ℂ) + b + 1) - c) * deriv g z + (a * b) * g z := hmul
      _ = den * (pz * deriv g z + qz * g z) := hscaled.symm
  let A : ℂ → ℂ := gaussCramerNumerator₁ T g
  let B : ℂ → ℂ := gaussCramerNumerator₂ T f
  let W : ℂ → ℂ := gaussCramerWronskian f g
  have hAAt : DifferentiableAt ℝ A z := by
    dsimp [A, gaussCramerNumerator₁, t₀, t₁]
    exact (ht₀.mul (hg₁At.restrictScalars ℝ)).sub
      (ht₁.mul (hgAt.restrictScalars ℝ))
  have hBAt : DifferentiableAt ℝ B z := by
    dsimp [B, gaussCramerNumerator₂, t₀, t₁]
    exact ((hfAt.restrictScalars ℝ).mul ht₁).sub
      ((hf₁At.restrictScalars ℝ).mul ht₀)
  have hWAt : DifferentiableAt ℂ W z := by
    dsimp [W, gaussCramerWronskian]
    exact (hfAt.mul hg₁At).sub (hf₁At.mul hgAt)
  have hA_z : wirtingerZ A z = pz * A z := by
    have hA_sub := wirtingerZ_sub
      (ht₀.mul (hg₁At.restrictScalars ℝ))
      (ht₁.mul (hgAt.restrictScalars ℝ))
    have hA_mul₁ : (fun w => t₀ w * deriv g w) = t₀ * deriv g := by
      funext w
      rfl
    have hA_mul₂ : (fun w => t₁ w * g w) = t₁ * g := by
      funext w
      rfl
    calc
      wirtingerZ A z =
          wirtingerZ (fun w => t₀ w * deriv g w) z -
            wirtingerZ (fun w => t₁ w * g w) z := by
        change wirtingerZ (fun w => t₀ w * deriv g w - t₁ w * g w) z = _
        rw [hA_mul₁, hA_mul₂]
        rw [← hA_mul₁, ← hA_mul₂] at hA_sub
        exact hA_sub
      _ = (t₀ z * deriv (deriv g) z + deriv g z * t₁ z) -
            (t₁ z * deriv g z + g z * t₂ z) := by
        rw [wirtingerZ_mul ht₀ (hg₁At.restrictScalars ℝ),
          wirtingerZ_mul ht₁ (hgAt.restrictScalars ℝ), ht₀z,
          wirtingerZ_eq_deriv_of_differentiableAt hg₁At,
          wirtingerZ_eq_deriv_of_differentiableAt hgAt]
      _ = pz * A z := by
        dsimp [A, gaussCramerNumerator₁, t₀, t₁]
        rw [hODEg', ht₂]
        ring
  have hB_z : wirtingerZ B z = pz * B z := by
    have hB_sub := wirtingerZ_sub
      ((hfAt.restrictScalars ℝ).mul ht₁)
      ((hf₁At.restrictScalars ℝ).mul ht₀)
    have hB_mul₁ : (fun w => f w * t₁ w) = f * t₁ := by
      funext w
      rfl
    have hB_mul₂ : (fun w => deriv f w * t₀ w) = deriv f * t₀ := by
      funext w
      rfl
    calc
      wirtingerZ B z =
          wirtingerZ (fun w => f w * t₁ w) z -
            wirtingerZ (fun w => deriv f w * t₀ w) z := by
        change wirtingerZ (fun w => f w * t₁ w - deriv f w * t₀ w) z = _
        rw [hB_mul₁, hB_mul₂]
        rw [← hB_mul₁, ← hB_mul₂] at hB_sub
        exact hB_sub
      _ = (f z * t₂ z + t₁ z * deriv f z) -
            (deriv f z * t₁ z + t₀ z * deriv (deriv f) z) := by
        rw [wirtingerZ_mul (hfAt.restrictScalars ℝ) ht₁,
          wirtingerZ_mul (hf₁At.restrictScalars ℝ) ht₀, ht₀z,
          wirtingerZ_eq_deriv_of_differentiableAt hfAt,
          wirtingerZ_eq_deriv_of_differentiableAt hf₁At]
      _ = pz * B z := by
        dsimp [B, gaussCramerNumerator₂, t₀, t₁]
        rw [ht₂, hODEf']
        ring
  have hWabel := gauss_pair_wronskian_abel (a : ℂ) b c f g hf hg hODEf hODEg z hz
  have hWderiv : deriv W z = pz * W z := by
    have habel : den * deriv W z +
        ((c : ℂ) - ((a : ℂ) + b + 1) * z) * W z = 0 := by
      change z * (1 - z) * deriv W z +
        ((c : ℂ) - ((a : ℂ) + b + 1) * z) * W z = 0
      exact hWabel
    have hmul : den * deriv W z =
        (z * ((a : ℂ) + b + 1) - c) * W z := by
      dsimp [den] at habel ⊢
      linear_combination habel
    have hscaled : den * (pz * W z) =
        (z * ((a : ℂ) + b + 1) - c) * W z := by
      simp only [pz]
      field_simp [hden]
    apply mul_left_cancel₀ hden
    calc
      den * deriv W z =
          (z * ((a : ℂ) + b + 1) - c) * W z := hmul
      _ = den * (pz * W z) := hscaled.symm
  have hWne := hW z hz
  have hInvAt : DifferentiableAt ℂ (fun w => (W w)⁻¹) z := hWAt.inv hWne
  have hαAt : DifferentiableAt ℝ (gaussCramerCoefficient₁ T f g) z := by
    change DifferentiableAt ℝ (fun w => A w * (W w)⁻¹) z
    exact hAAt.mul (hInvAt.restrictScalars ℝ)
  have hβAt : DifferentiableAt ℝ (gaussCramerCoefficient₂ T f g) z := by
    change DifferentiableAt ℝ (fun w => B w * (W w)⁻¹) z
    exact hBAt.mul (hInvAt.restrictScalars ℝ)
  have hαz : wirtingerZ (gaussCramerCoefficient₁ T f g) z = 0 := by
    have hcancel (x : ℂ) :
        A z * (-(W z)⁻¹ ^ 2 * (x * W z)) + (W z)⁻¹ * (x * A z) = 0 := by
      field_simp [hWne]
      ring
    change wirtingerZ (fun w => A w * (W w)⁻¹) z = 0
    rw [wirtingerZ_mul hAAt (hInvAt.restrictScalars ℝ),
      hA_z, wirtingerZ_inv_of_differentiableAt hWAt hWne, hWderiv]
    exact hcancel pz
  have hβz : wirtingerZ (gaussCramerCoefficient₂ T f g) z = 0 := by
    have hcancel (x : ℂ) :
        B z * (-(W z)⁻¹ ^ 2 * (x * W z)) + (W z)⁻¹ * (x * B z) = 0 := by
      field_simp [hWne]
      ring
    change wirtingerZ (fun w => B w * (W w)⁻¹) z = 0
    rw [wirtingerZ_mul hBAt (hInvAt.restrictScalars ℝ),
      hB_z, wirtingerZ_inv_of_differentiableAt hWAt hWne, hWderiv]
    exact hcancel pz
  exact ⟨hαAt, hαz, hβAt, hβz⟩

end DOZZ.Proofs
