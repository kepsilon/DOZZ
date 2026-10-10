/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RootedIdentity
import Mathlib.Tactic
/-! Positive finite retained source masses for the signed Pareto expectations. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual retained source mass is positive and finite on one full-measure event. -/
theorem dual_source_outerMass_positive_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1)
    (hr : ‖z‖^(1-ξ) ≤ 1) :
    ∀ᵐ ω ∂P, 0 < dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ∧
      dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ < ⊤ := by
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
      linarith only [hhalf,hinv]
    · exact hα₁
    · exact hα₂
  have hfull := reflected_coulombMass_ae_finite P X hX γ hγ hγ₂ M hM
    ![z,0,1] hinj ![-2/γ,α₁,α₂] α₃ hcharges hα₃
  have hmeas : AEMeasurable (fun ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ) P :=
    (dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  obtain ⟨C, _, hb⟩ := dual_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ 1 (by norm_num)
  have hInv : (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-(1 : ℝ)) ∂P) < ⊤ :=
    (hb z ξ hz hr).trans_lt ENNReal.ofReal_lt_top
  filter_upwards [hfull, ae_lt_top' (hmeas.pow_const (-(1 : ℝ))) hInv.ne] with ω hf hi
  constructor
  · apply pos_iff_ne_zero.mpr
    intro he
    rw [he, ENNReal.zero_rpow_of_neg (by norm_num : -(1 : ℝ) < 0)] at hi
    exact lt_irrefl _ hi
  · have hle : dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ≤
        coulombMass γ (M ω) ![-2/γ,α₁,α₂] ![z,0,1] α₃ := by
      unfold dualOuterMass coulombMass
      exact lintegral_mono' Measure.restrict_le_self le_rfl
    exact hle.trans_lt hf

end DOZZ.Proofs
