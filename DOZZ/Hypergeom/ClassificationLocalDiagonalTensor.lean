/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationWirtinger

/-! Local regularity and PDE closure for diagonal Hermitian tensors. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A real diagonal Hermitian tensor of two analytic Gauss solutions is C² and satisfies the
real PDE locally on the regular part of its open analytic domain. -/
theorem realGaussDiagonalTensor_solutionOn
    (a b c v₁ v₂ : ℝ) {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hODEf : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f w = 0)
    (hODEg : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g w = 0) :
    ContDiffOn ℝ 2 (fun z => v₁ * Complex.normSq (f z) + v₂ * Complex.normSq (g z)) U ∧
      ∀ z ∈ U, z ∈ gaussRegularPlane →
        wirtingerZ (wirtingerZ (fun w =>
          ((v₁ * Complex.normSq (f w) + v₂ * Complex.normSq (g w) : ℝ) : ℂ))) z +
          ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
            wirtingerZ (fun w =>
              ((v₁ * Complex.normSq (f w) + v₂ * Complex.normSq (g w) : ℝ) : ℂ)) z -
          (a : ℂ) * b / (z * (1 - z)) *
            ((v₁ * Complex.normSq (f z) + v₂ * Complex.normSq (g z) : ℝ) : ℂ) = 0 := by
  let T : ℂ → ℝ := fun z => v₁ * Complex.normSq (f z) + v₂ * Complex.normSq (g z)
  have hTdiff : ContDiffOn ℝ 2 T U := by
    intro z hz
    have hfAt : ContDiffAt ℝ 2 f z := (hf z hz).contDiffAt.restrict_scalars ℝ
    have hgAt : ContDiffAt ℝ 2 g z := (hg z hz).contDiffAt.restrict_scalars ℝ
    have hnormf : ContDiffAt ℝ 2 (fun w => Complex.normSq (f w)) z := by
      have hre : ContDiffAt ℝ 2 (fun w => (f w).re) z := by
        rw [show (fun w => (f w).re) = Complex.reCLM ∘ f by rfl]
        exact Complex.reCLM.contDiff.contDiffAt.comp z hfAt
      have him : ContDiffAt ℝ 2 (fun w => (f w).im) z := by
        rw [show (fun w => (f w).im) = Complex.imCLM ∘ f by rfl]
        exact Complex.imCLM.contDiff.contDiffAt.comp z hfAt
      have hrep : (fun w => Complex.normSq (f w)) =
          (fun w => (f w).re ^ 2 + (f w).im ^ 2) := by
        funext w
        simp [Complex.normSq_apply, pow_two]
      rw [hrep]
      exact (hre.pow 2).add (him.pow 2)
    have hnormg : ContDiffAt ℝ 2 (fun w => Complex.normSq (g w)) z := by
      have hre : ContDiffAt ℝ 2 (fun w => (g w).re) z := by
        rw [show (fun w => (g w).re) = Complex.reCLM ∘ g by rfl]
        exact Complex.reCLM.contDiff.contDiffAt.comp z hgAt
      have him : ContDiffAt ℝ 2 (fun w => (g w).im) z := by
        rw [show (fun w => (g w).im) = Complex.imCLM ∘ g by rfl]
        exact Complex.imCLM.contDiff.contDiffAt.comp z hgAt
      have hrep : (fun w => Complex.normSq (g w)) =
          (fun w => (g w).re ^ 2 + (g w).im ^ 2) := by
        funext w
        simp [Complex.normSq_apply, pow_two]
      rw [hrep]
      exact (hre.pow 2).add (him.pow 2)
    have hTAt : ContDiffAt ℝ 2 T z := by
      dsimp [T]
      fun_prop
    exact hTAt.contDiffWithinAt
  have hfv : AnalyticOnNhd ℂ (fun w => (v₁ : ℂ) * f w) U := by
    intro w hw
    exact analyticAt_const.mul (hf w hw)
  have hgv : AnalyticOnNhd ℂ (fun w => (v₂ : ℂ) * g w) U := by
    intro w hw
    exact analyticAt_const.mul (hg w hw)
  have hODEfv : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (fun x => (v₁ : ℂ) * f x) w = 0 := by
    intro w hw
    have h := hODEf w hw
    dsimp [gaussHolomorphicOperator] at h ⊢
    simp only [deriv_const_mul_field']
    linear_combination (v₁ : ℂ) * h
  have hODEgv : ∀ w ∈ U,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (fun x => (v₂ : ℂ) * g x) w = 0 := by
    intro w hw
    have h := hODEg w hw
    dsimp [gaussHolomorphicOperator] at h ⊢
    simp only [deriv_const_mul_field']
    linear_combination (v₂ : ℂ) * h
  have hcast (z : ℂ) : (T z : ℂ) =
      (v₁ : ℂ) * f z * star (f z) + (v₂ : ℂ) * g z * star (g z) := by
    dsimp [T]
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    ring
  have hfun : (fun z => (T z : ℂ)) =
      (fun z => (v₁ : ℂ) * f z * star (f z) + (v₂ : ℂ) * g z * star (g z)) :=
    funext hcast
  refine ⟨hTdiff, ?_⟩
  intro z hz hzReg
  rw [hfun, hcast z]
  simpa [T] using realGaussTensor_pde_add_of_holomorphicSolutions a b c hU
    hfv hf hODEfv hgv hg hODEgv hz hzReg

end DOZZ.Proofs
