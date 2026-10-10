/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceOuterMoments
import Mathlib.Tactic
/-! Finiteness of the literal full dual kernel on the supplied ordinary chaos. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- For every distinct moving insertion, ordinary subcritical charges make the full actual
kernel mass finite on the supplied GMC. This also gives finiteness of all spatial submasses. -/
theorem dual_full_kernel_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∀ᵐ ω ∂P, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω) < ⊤ := by
  have hinj : Function.Injective (![z,0,1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hcharges : ∀ i : Fin 3, (![-2/γ,α₁,α₂] : Fin 3 → ℝ) i < Q γ := by
    intro i
    fin_cases i
    · change -2/γ < Q γ
      rw [neg_div]
      unfold Q
      have hinv : 0 < 2/γ := div_pos (by norm_num) hγ
      have hhalf : 0 < γ/2 := half_pos hγ
      linarith only [hinv,hhalf]
    · exact hα₁
    · exact hα₂
  have hfull := reflected_coulombMass_ae_finite P X hX γ hγ hγ₂ M hM
    ![z,0,1] hinj ![-2/γ,α₁,α₂] α₃ hcharges hα₃
  filter_upwards [hfull,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM z,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω hf hz h0 h1
  rw [dual_kernel_integral_eq_coulombMass γ α₁ α₂ α₃ hγ.ne' z (M ω) hz h0 h1]
  exact hf

end DOZZ.Proofs
