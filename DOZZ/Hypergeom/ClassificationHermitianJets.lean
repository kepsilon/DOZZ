/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianUniqueness
public import DOZZ.Hypergeom.ClassificationWirtingerBar
public import DOZZ.Hypergeom.ClassificationWirtingerC2
import Mathlib.Analysis.Calculus.FDeriv.Star

/-! First Wirtinger derivatives and real `C²` regularity of a constant Hermitian tensor. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

/-- A constant-coefficient sesquilinear tensor in two holomorphic functions. -/
noncomputable def hermitianQuadraticTensor (f g : ℂ → ℂ) (A B C D : ℂ) : ℂ → ℂ :=
  fun z => A * f z * star (f z) + B * f z * star (g z) +
    C * g z * star (f z) + D * g z * star (g z)

/-- The `∂z` expression of a constant sesquilinear tensor. -/
noncomputable def hermitianQuadraticTensorZ (f g : ℂ → ℂ) (A B C D : ℂ) : ℂ → ℂ :=
  fun z => A * deriv f z * star (f z) + B * deriv f z * star (g z) +
    C * deriv g z * star (f z) + D * deriv g z * star (g z)

private theorem function_add_apply (f g : ℂ → ℂ) :
    f + g = fun z => f z + g z := by
  funext z
  rfl

private theorem wirtingerBar_star_eq_star_deriv_at {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    wirtingerBar (fun w => star (g w)) z = star (deriv g z) := by
  apply wirtingerBar_eq_star_deriv_of_star_differentiableAt hg
  funext w
  simp

private theorem wirtingerZ_const_mul_star_term (k : ℂ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    wirtingerZ (fun w => k * f w * star (g w)) z =
      k * deriv f z * star (g z) := by
  have hKf : DifferentiableAt ℂ (fun w => k * f w) z :=
    (differentiableAt_const k).mul hf
  have h := wirtingerZ_mul_star_of_differentiableAt hKf hg
  change wirtingerZ (fun w => (k * f w) * star (g w)) z = _
  rw [h]
  rw [deriv_const_mul_field]
  ring

private theorem wirtingerBar_const_mul_star_term (k : ℂ) {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    wirtingerBar (fun w => k * f w * star (g w)) z =
      k * f z * star (deriv g z) := by
  have hKf : DifferentiableAt ℂ (fun w => k * f w) z :=
    (differentiableAt_const k).mul hf
  have h := wirtingerBar_mul (hKf.restrictScalars ℝ)
    ((hg.restrictScalars ℝ).star)
  change wirtingerBar (fun w => (k * f w) * star (g w)) z = _
  rw [h, wirtingerBar_eq_zero_of_differentiableAt hKf,
    wirtingerBar_star_eq_star_deriv_at hg]
  ring

private theorem hermitianTensorTermDiffAt {k : ℂ} {f g : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    DifferentiableAt ℝ (fun w => k * f w * star (g w)) z := by
  exact (((differentiableAt_const k).mul hf).restrictScalars ℝ).mul
    ((hg.restrictScalars ℝ).star)

/-- First `∂z` derivative of the constant Hermitian tensor. -/
theorem hermitianQuadraticTensor_wirtingerZ
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (A B C D : ℂ) {z : ℂ} (hz : z ∈ U) :
    wirtingerZ (hermitianQuadraticTensor f g A B C D) z =
      hermitianQuadraticTensorZ f g A B C D z := by
  have hfAt := (hf z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  let t₁ : ℂ → ℂ := fun w => A * f w * star (f w)
  let t₂ : ℂ → ℂ := fun w => B * f w * star (g w)
  let t₃ : ℂ → ℂ := fun w => C * g w * star (f w)
  let t₄ : ℂ → ℂ := fun w => D * g w * star (g w)
  have hfun : hermitianQuadraticTensor f g A B C D = (t₁ + t₂) + (t₃ + t₄) := by
    funext w
    simp [hermitianQuadraticTensor, t₁, t₂, t₃, t₄]; ring
  have h₁ := hermitianTensorTermDiffAt (k := A) hfAt hfAt
  have h₂ := hermitianTensorTermDiffAt (k := B) hfAt hgAt
  have h₃ := hermitianTensorTermDiffAt (k := C) hgAt hfAt
  have h₄ := hermitianTensorTermDiffAt (k := D) hgAt hgAt
  have hsum₁ : wirtingerZ (t₁ + t₂) z = wirtingerZ t₁ z + wirtingerZ t₂ z := by
    rw [function_add_apply]
    exact wirtingerZ_add h₁ h₂
  have hsum₂ : wirtingerZ (t₃ + t₄) z = wirtingerZ t₃ z + wirtingerZ t₄ z := by
    rw [function_add_apply]
    exact wirtingerZ_add h₃ h₄
  have hsum : wirtingerZ ((t₁ + t₂) + (t₃ + t₄)) z =
      wirtingerZ (t₁ + t₂) z + wirtingerZ (t₃ + t₄) z := by
    rw [function_add_apply]
    exact wirtingerZ_add (h₁.add h₂) (h₃.add h₄)
  calc
    wirtingerZ (hermitianQuadraticTensor f g A B C D) z =
        wirtingerZ ((t₁ + t₂) + (t₃ + t₄)) z := by rw [hfun]
    _ = wirtingerZ (t₁ + t₂) z + wirtingerZ (t₃ + t₄) z := hsum
    _ = wirtingerZ t₁ z + wirtingerZ t₂ z +
          (wirtingerZ t₃ z + wirtingerZ t₄ z) := by rw [hsum₁, hsum₂]
    _ = hermitianQuadraticTensorZ f g A B C D z := by
      rw [show t₁ = fun w => A * f w * star (f w) from rfl,
        show t₂ = fun w => B * f w * star (g w) from rfl,
        show t₃ = fun w => C * g w * star (f w) from rfl,
        show t₄ = fun w => D * g w * star (g w) from rfl]
      rw [wirtingerZ_const_mul_star_term A hfAt hfAt,
        wirtingerZ_const_mul_star_term B hfAt hgAt,
        wirtingerZ_const_mul_star_term C hgAt hfAt,
        wirtingerZ_const_mul_star_term D hgAt hgAt]
      simp [hermitianQuadraticTensorZ]
      ring

/-- First `∂bar` derivative of the constant Hermitian tensor. -/
theorem hermitianQuadraticTensor_wirtingerBar
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (A B C D : ℂ) {z : ℂ} (hz : z ∈ U) :
    wirtingerBar (hermitianQuadraticTensor f g A B C D) z =
      A * f z * star (deriv f z) + B * f z * star (deriv g z) +
      C * g z * star (deriv f z) + D * g z * star (deriv g z) := by
  have hfAt := (hf z hz).differentiableAt
  have hgAt := (hg z hz).differentiableAt
  let t₁ : ℂ → ℂ := fun w => A * f w * star (f w)
  let t₂ : ℂ → ℂ := fun w => B * f w * star (g w)
  let t₃ : ℂ → ℂ := fun w => C * g w * star (f w)
  let t₄ : ℂ → ℂ := fun w => D * g w * star (g w)
  have hfun : hermitianQuadraticTensor f g A B C D = (t₁ + t₂) + (t₃ + t₄) := by
    funext w
    simp [hermitianQuadraticTensor, t₁, t₂, t₃, t₄]; ring
  have h₁ := hermitianTensorTermDiffAt (k := A) hfAt hfAt
  have h₂ := hermitianTensorTermDiffAt (k := B) hfAt hgAt
  have h₃ := hermitianTensorTermDiffAt (k := C) hgAt hfAt
  have h₄ := hermitianTensorTermDiffAt (k := D) hgAt hgAt
  have hsum₁ : wirtingerBar (t₁ + t₂) z = wirtingerBar t₁ z + wirtingerBar t₂ z := by
    rw [function_add_apply]
    exact wirtingerBar_add h₁ h₂
  have hsum₂ : wirtingerBar (t₃ + t₄) z = wirtingerBar t₃ z + wirtingerBar t₄ z := by
    rw [function_add_apply]
    exact wirtingerBar_add h₃ h₄
  have hsum : wirtingerBar ((t₁ + t₂) + (t₃ + t₄)) z =
      wirtingerBar (t₁ + t₂) z + wirtingerBar (t₃ + t₄) z := by
    rw [function_add_apply]
    exact wirtingerBar_add (h₁.add h₂) (h₃.add h₄)
  calc
    wirtingerBar (hermitianQuadraticTensor f g A B C D) z =
        wirtingerBar ((t₁ + t₂) + (t₃ + t₄)) z := by rw [hfun]
    _ = wirtingerBar (t₁ + t₂) z + wirtingerBar (t₃ + t₄) z := hsum
    _ = wirtingerBar t₁ z + wirtingerBar t₂ z +
          (wirtingerBar t₃ z + wirtingerBar t₄ z) := by rw [hsum₁, hsum₂]
    _ = A * f z * star (deriv f z) + B * f z * star (deriv g z) +
          C * g z * star (deriv f z) + D * g z * star (deriv g z) := by
      rw [show t₁ = fun w => A * f w * star (f w) from rfl,
        show t₂ = fun w => B * f w * star (g w) from rfl,
        show t₃ = fun w => C * g w * star (f w) from rfl,
        show t₄ = fun w => D * g w * star (g w) from rfl]
      rw [wirtingerBar_const_mul_star_term A hfAt hfAt,
        wirtingerBar_const_mul_star_term B hfAt hgAt,
        wirtingerBar_const_mul_star_term C hgAt hfAt,
        wirtingerBar_const_mul_star_term D hgAt hgAt]
      ring

/-- A constant Hermitian tensor is twice continuously real-differentiable wherever its two
holomorphic factors are analytic. -/
theorem hermitianQuadraticTensor_contDiffAt_two
    {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (A B C D : ℂ) {z : ℂ} (hz : z ∈ U) :
    ContDiffAt ℝ 2 (hermitianQuadraticTensor f g A B C D) z := by
  have hfAt : ContDiffAt ℝ 2 f z := (hf z hz).contDiffAt.restrict_scalars ℝ
  have hgAt : ContDiffAt ℝ 2 g z := (hg z hz).contDiffAt.restrict_scalars ℝ
  have hstarF : ContDiffAt ℝ 2 (fun w => star (f w)) z := by
    rw [show (fun w => star (f w)) = Complex.conjCLE ∘ f by
      funext w; rfl]
    exact Complex.conjCLE.contDiff.contDiffAt.comp z hfAt
  have hstarG : ContDiffAt ℝ 2 (fun w => star (g w)) z := by
    rw [show (fun w => star (g w)) = Complex.conjCLE ∘ g by
      funext w; rfl]
    exact Complex.conjCLE.contDiff.contDiffAt.comp z hgAt
  have ht₁ : ContDiffAt ℝ 2 (fun w => A * f w * star (f w)) z :=
    (contDiffAt_const.mul hfAt).mul hstarF
  have ht₂ : ContDiffAt ℝ 2 (fun w => B * f w * star (g w)) z :=
    (contDiffAt_const.mul hfAt).mul hstarG
  have ht₃ : ContDiffAt ℝ 2 (fun w => C * g w * star (f w)) z :=
    (contDiffAt_const.mul hgAt).mul hstarF
  have ht₄ : ContDiffAt ℝ 2 (fun w => D * g w * star (g w)) z :=
    (contDiffAt_const.mul hgAt).mul hstarG
  change ContDiffAt ℝ 2
    (fun w => A * f w * star (f w) + B * f w * star (g w) +
      C * g w * star (f w) + D * g w * star (g w)) z
  convert (ht₁.add ht₂).add (ht₃.add ht₄) using 1
  ext w
  ring_nf

end DOZZ.Proofs
