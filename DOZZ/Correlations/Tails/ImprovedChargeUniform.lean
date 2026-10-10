/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ImprovedChargeMoment
public import DOZZ.Correlations.Tails.WeightedMomentModelLaw

/-! Uniform improved-charge moments, retaining the actual correlated multiplier. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Uniform envelope and weighted-mass moments give one bound before the translated
GFF/GMC model is selected. Hölder handles their possible correlation. -/
theorem uniform_correlated_improved_charge_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (A g : ℝ) (hg : 0 < g)
    (p q : ℝ) (hpq : p.HolderConjugate q) (L : ℝ≥0∞) (hL : L < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (Y : Ω → Distr) (N : Ω → Measure ℂ),
      IsEquatorGFF P Y → IsGMCOf P Y γ N →
      ∀ α r : ℝ, |α-1/γ| ≤ A → 0 < r → r*q+g ≤ 4/γ^2 →
        r*q+g ≤ 2/γ*(Q γ-(α-1/γ)) →
        ∀ E : Ω → ℝ≥0∞, AEMeasurable E P → (∫⁻ ω, E ω^(r*p) ∂P) ≤ L →
          (∫⁻ ω, (E ω*weightedGmcBallMass γ (N ω) (α-1/γ) 0 ρ)^r ∂P) ≤ C := by
  obtain ⟨D,hD,hmodels⟩ := weighted_moment_uniform_models
    P X hX γ hγ hγ2 M hM ρ hρ hρ1 A g hg
  let C := L^(1/p)*D^(1/q)
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hpq.pos.le) hL.ne)
    (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hpq.symm.pos.le) hD.ne)
  refine ⟨C,hC,?_⟩
  intro Y N hY hN α r hα hr hbulk hins E hE hEm
  have hW := gmc_weighted_mass_aemeasurable P Y hY γ hγ hγ2 N hN (α-1/γ) 0 ρ
  have hWbound := hmodels P Y N hY hN (α-1/γ) (r*q) hα (mul_pos hr hpq.symm.pos) hbulk hins
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hE.pow_const r) (hW.pow_const r)
  change (∫⁻ ω, E ω^r*weightedGmcBallMass γ (N ω) (α-1/γ) 0 ρ ^ r ∂P) ≤ _ at hh
  simp only [← ENNReal.rpow_mul] at hh
  have he := ENNReal.rpow_le_rpow hEm (div_nonneg zero_le_one hpq.pos.le)
  have hw := ENNReal.rpow_le_rpow hWbound (div_nonneg zero_le_one hpq.symm.pos.le)
  have hb := hh.trans (mul_le_mul' he hw)
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hr.le] using hb


end DOZZ.Proofs
