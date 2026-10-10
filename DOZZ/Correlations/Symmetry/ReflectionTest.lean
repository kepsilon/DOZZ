/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionKernel
public import DOZZ.Statements.Defs.Distr
public import Mathlib.Analysis.Distribution.TestFunction
@[expose] public section
open Set TopologicalSpace
open scoped Distributions
namespace DOZZ.Proofs

/-- The affine interchange of the two finite insertions as a homeomorphism. -/
noncomputable def symmetryReflectionHomeomorph : ℂ ≃ₜ ℂ where
  toFun x := 1 - x
  invFun x := 1 - x
  left_inv := symmetryReflection_involutive
  right_inv := symmetryReflection_involutive
  continuous_toFun := continuous_const.sub continuous_id
  continuous_invFun := continuous_const.sub continuous_id

/-- Pullback of a test density through the unit-Jacobian reflection. -/
noncomputable def symmetryReflectionTest (f : TestFn) : TestFn :=
  ⟨fun x => f (1 - x), f.contDiff.comp (contDiff_const.sub contDiff_id),
    f.hasCompactSupport.comp_homeomorph symmetryReflectionHomeomorph, subset_univ _⟩

/-- Reflection preserves every uniform derivative norm. -/
theorem norm_iteratedFDeriv_symmetryReflection (f : ℂ → ℝ) (i : ℕ) (x : ℂ) :
    ‖iteratedFDeriv ℝ i (fun y => f (1 - y)) x‖ = ‖iteratedFDeriv ℝ i f (1 - x)‖ := by
  have hn := (LinearIsometryEquiv.neg ℝ : ℂ ≃ₗᵢ[ℝ] ℂ).norm_iteratedFDeriv_comp_right (fun y => f (1 + y)) x i
  have ht : iteratedFDeriv ℝ i (fun y => f (1 + y)) (-x) =
      iteratedFDeriv ℝ i f (1 - x) := by
    simp only [← iteratedFDerivWithin_univ]
    simpa only [vadd_eq_add, image_add_left, add_univ, vadd_set_univ, sub_eq_add_neg] using
      iteratedFDerivWithin_comp_add_left (𝕜 := ℝ) (f := f) (s := univ) i (1 : ℂ) (-x)
  simp only [LinearIsometryEquiv.coe_neg] at hn
  rw [ht] at hn
  simpa only [Function.comp_def, LinearIsometryEquiv.coe_neg, sub_eq_add_neg] using hn

/-- Pullback on a fixed compact support, with its derivative seminorm bounds. -/
noncomputable def symmetryReflectionSupportedCLM (K : Compacts ℂ) :
    𝓓_{K}(ℂ, ℝ) →L[ℝ] 𝓓_{K.map symmetryReflectionHomeomorph symmetryReflectionHomeomorph.continuous}(ℂ, ℝ) := by
  apply ContDiffMapSupportedIn.mkCLM ℝ (fun f x => f (1 - x))
  · intro f g x; rfl
  · intro c f x; rfl
  · intro f; exact f.contDiff.comp (contDiff_const.sub contDiff_id)
  · intro f x hx
    apply f.zero_on_compl
    intro h
    apply hx
    exact ⟨1 - x, h, symmetryReflection_involutive x⟩
  · intro i _hi
    refine ⟨{i}, 1, zero_le_one, fun f x _hx => ?_⟩
    rw [norm_iteratedFDeriv_symmetryReflection]
    simpa only [Finset.sup_singleton, one_mul] using
      ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top (𝕜 := ℝ)
        (f := f) (x := 1 - x)

/-- The test pullback is continuous for the actual test-function topology. -/
noncomputable def symmetryReflectionTestCLM : TestFn →L[ℝ] TestFn := by
  apply TestFunction.mkCLM ℝ symmetryReflectionTest
  · intro f g; ext x; rfl
  · intro c f; ext x; rfl
  · intro K hK
    have he : symmetryReflectionTest ∘ TestFunction.ofSupportedIn hK =
        TestFunction.ofSupportedIn (subset_univ _) ∘ symmetryReflectionSupportedCLM K := by
      funext f
      ext x
      rfl
    rw [he]
    exact (TestFunction.continuous_ofSupportedIn (subset_univ _)).comp
      (symmetryReflectionSupportedCLM K).continuous
end DOZZ.Proofs
