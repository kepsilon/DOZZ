/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CoulombMassPositiveFinite
public import DOZZ.FourPoint.Fusion.Kernel

/-! # Positive finite unrooted masses in the punctured fusion chart -/

@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

theorem fusion_gammaHalfMass_pos_finite_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ≠ 0 ∧
      coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ≠ ⊤ := by
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, norm_one] at hz4
    norm_num at hz4
  have hzinj : Function.Injective (![z, 0, 1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have ha : ∀ j : Fin 3, (![-γ / 2, α₁, α₂] : Fin 3 → ℝ) j < Q γ := by
    intro j
    fin_cases j
    · change -γ / 2 < Q γ
      unfold Q
      have : 0 < 2 / γ := by positivity
      linarith
    · change α₁ < Q γ
      unfold Q
      linarith
    · exact hα₂
  exact coulomb_mass_pos_finite_ae P X hX γ hγ hγ2 M hM ![z, 0, 1] hzinj
    ![-γ / 2, α₁, α₂] α₃ ha hα₃

end DOZZ.Proofs
