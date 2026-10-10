/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.SingularMassMeasurability
public import DOZZ.GMC.SharpMoments.WeightedLocalRange
public import DOZZ.Statements.Brownian.ReflectionExponent
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! The improved-drift moment range for the spatial error in the one-insertion tail estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- A first-order spatial error reduces the insertion charge by `1 / γ`. Correlation
with a random envelope having every positive moment does not shrink the strict range. -/
theorem correlated_improved_charge_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : ℝ) (hα : α < Q γ) (r : ℝ) (hr : 0 < r)
    (hrange : r < min (reflectionExponent γ α + 2 / γ^2) (4 / γ^2))
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (E : Ω → ℝ≥0∞) (hE : AEMeasurable E P)
    (hEm : ∀ s : ℝ, 0 < s → (∫⁻ ω, E ω ^ s ∂P) < ⊤) :
    (∫⁻ ω, (E ω * weightedGmcBallMass γ (M ω) (α-1/γ) z ρ)^r ∂P) < ⊤ := by
  have hα' : α-1/γ < Q γ := by have := one_div_pos.mpr hγ; linarith
  have hshift : 2/γ*(Q γ-(α-1/γ)) = reflectionExponent γ α+2/γ^2 := by
    unfold reflectionExponent
    field_simp
    ring
  obtain ⟨s, hrs, hs⟩ := exists_between hrange
  have hs0 : 0 < s := hr.trans hrs
  let q := s/r
  have hq : 1 < q := (one_lt_div hr).mpr hrs
  let p := Real.conjExponent q
  have hpq : p.HolderConjugate q := (Real.HolderConjugate.conjExponent hq).symm
  have hrq : r*q = s := by dsimp [q]; field_simp
  have hWm := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM (α-1/γ) z ρ
  have hWs : (∫⁻ ω, weightedGmcBallMass γ (M ω) (α-1/γ) z ρ ^ s ∂P) < ⊤ := by
    apply (equatorGFF_GMC_weighted_local_moment_range P X hX γ hγ hγ2 M hM
      (α-1/γ) hα' s hs0 z ρ hρ).mpr
    simpa only [hshift, min_comm] using hs
  have hEp : (∫⁻ ω, (E ω ^ r)^p ∂P) < ⊤ := by
    simpa only [← ENNReal.rpow_mul] using hEm (r*p) (mul_pos hr hpq.pos)
  have hWq : (∫⁻ ω, (weightedGmcBallMass γ (M ω) (α-1/γ) z ρ ^ r)^q ∂P) < ⊤ := by
    simpa only [← ENNReal.rpow_mul, hrq] using hWs
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hE.pow_const r) (hWm.pow_const r)
  have hfin : (∫⁻ ω, E ω ^ r * weightedGmcBallMass γ (M ω) (α-1/γ) z ρ ^ r ∂P) < ⊤ :=
    lt_of_le_of_lt hholder (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hpq.pos.le) hEp.ne)
      (ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hpq.symm.pos.le) hWq.ne))
  simpa only [ENNReal.mul_rpow_of_nonneg _ _ hr.le] using hfin


end DOZZ.Proofs
