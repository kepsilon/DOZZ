/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.GMC.Moments.RhoCoulomb
import Mathlib.Tactic

/-! # Finiteness of the supplied limiting Coulomb mass

A small positive moment exists when every finite and infinite charge is below
`Q`. No total-charge condition is needed for almost-sure mass finiteness.
-/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Small positive GMC moments imply finiteness for every subcritical root configuration. -/
theorem reflected_coulombMass_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (hα : ∀ k, α k < Q γ) (hαinf : αinf < Q γ) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf < ⊤ := by
  have h4 : (0 : ℝ) < 4 / γ ^ 2 := by positivity
  have hi : 0 < 2 / γ * (Q γ - αinf) :=
    mul_pos (div_pos (by norm_num) hγ) (sub_pos.mpr hαinf)
  have hk : ∀ k, 0 < 2 / γ * (Q γ - α k) := fun k =>
    mul_pos (div_pos (by norm_num) hγ) (sub_pos.mpr (hα k))
  have e1 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioo 0 (4 / γ ^ 2) := Ioo_mem_nhdsGT h4
  have e2 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t ∈ Ioo 0 (2 / γ * (Q γ - αinf)) :=
    Ioo_mem_nhdsGT hi
  have e3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), ∀ k, t ∈ Ioo 0 (2 / γ * (Q γ - α k)) :=
    eventually_all.mpr fun k => Ioo_mem_nhdsGT (hk k)
  obtain ⟨t, ht⟩ := (e1.and (e2.and e3)).exists
  have hmoment := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ₂ M hM
    z hz α αinf t ht.1.1 ht.1.2 (fun k => (ht.2.2 k).2) ht.2.1.2
  have hm := gmc_coulombMass_aemeasurable P X hX γ hγ hγ₂ M hM α z αinf
  filter_upwards [ae_lt_top' (hm.pow_const t) hmoment.ne] with ω hω
  by_contra hn
  rw [not_lt_top_iff.mp hn, ENNReal.top_rpow_of_pos ht.1.1] at hω
  exact lt_irrefl _ hω

/-- The literal rho mass is almost surely finite whenever its three charges are below `Q`. -/
theorem reflected_rho_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, rho γ (M ω) α₁ α₂ α₃ < ⊤ := by
  have hz : Function.Injective (![0, 1] : Fin 2 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hcharges : ∀ k : Fin 2, (![α₁, α₂] : Fin 2 → ℝ) k < Q γ := by
    intro k
    fin_cases k
    · exact hα₁
    · exact hα₂
  filter_upwards [reflected_coulombMass_ae_finite P X hX γ hγ hγ₂ M hM
    ![0, 1] hz ![α₁, α₂] α₃ hcharges hα₃,
    gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃] with ω hf he
  rw [he]
  exact hf

end DOZZ.Proofs
