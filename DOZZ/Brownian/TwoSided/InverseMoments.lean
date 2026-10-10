/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.Moments

/-! Initial-block inverse bounds with a common radial constant for all subcritical charges. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The initial positive unit block is retained in the full two-sided mass, including its
endpoint convention. -/
theorem twosided_initial_block_le_mass {Ω : Type*} (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    initialUnitBlockMass γ (B ω).1 (Z ω) ≤ twoSidedReflectionMass γ B Z ω := by
  unfold initialUnitBlockMass twoSidedReflectionMass
  apply lintegral_mono
  intro t
  by_cases ht : 0 ≤ t ∧ t ≤ 1
  · simp only [ht, dite_true, twoSidedConditionedValue]
    rfl
  · simp only [ht, dite_false, ENNReal.ofReal_zero]
    exact zero_le

/-- A bounded drift range and one uniform lateral inverse moment give a uniform inverse
moment of the full mass. Its radial factor uses only the first half-path. -/
theorem twosided_inverse_moment_uniform_from_lateral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν : Set ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (p N : ℝ) (hp : p < 0) (hνN : ∀ ν ∈ Kν, ν ≤ N)
    (L : ℝ≥0∞) (hL : L < ⊤)
    (hUnit : ∀ γ ∈ Kγ, (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ p ∂P) ≤ L) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) p ∂P) ≤ C := by
  let θ : ℝ := (-p) * 2
  have hθ : 0 ≤ θ := mul_nonneg (neg_nonneg.mpr hp.le) (by norm_num)
  obtain ⟨C, hC, hOsc⟩ := isNegativeConditionedBrownianLaw_unitIncrement_exp_le θ N hθ
  refine ⟨C * L, ENNReal.mul_lt_top hC hL, ?_⟩
  intro γ hγ ν hν
  obtain ⟨hB, hZ, hi⟩ := hData γ hγ ν hν
  let X : Ω → BrownianPath := fun ω => (B ν ω).1
  have hX : IsNegativeConditionedBrownianProcess P X ν := hB.1
  let f : BrownianPath → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath 0 p)))
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Icc 0 1)) ^ p
  have hshift : Continuous (fun p : BrownianPath => brownianShiftPath 0 p) :=
    continuous_brownianShiftPath.comp (continuous_const.prodMk continuous_id)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_brownianUnitNorm.comp hshift).measurable))
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Icc)
  have hiX : IndepFun X (Z γ) P := hi.comp measurable_fst measurable_id
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hX.1) (hg.comp_aemeasurable hZ.2.2.2.1) (hiX.comp hf hg)
  change (∫⁻ ω, f (X ω) * g (Z γ ω) ∂P) =
    (∫⁻ ω, f (X ω) ∂P) * (∫⁻ ω, g (Z γ ω) ∂P) at hprod
  have hzero : ∀ᵐ ω ∂P, X ω 0 = 0 := ae_of_ae_map hX.1 hX.2.2.2.1
  have hfX : (∫⁻ ω, f (X ω) ∂P) ≤ C := by
    rw [← lintegral_map' hf.aemeasurable hX.1]
    exact hOsc ν (hνN ν hν) _ hX.2 0
  have hUnit' : (∫⁻ ω, g (Z γ ω) ∂P) ≤ L := by
    change (∫⁻ ω, (Z γ ω (Icc 0 1)) ^ p ∂P) ≤ L
    rw [lateralGMC_Icc_moment_eq_Ioc P γ (Z γ) hZ 0 1 p (by norm_num)]
    exact hUnit γ hγ
  calc (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) p ∂P)
      ≤ ∫⁻ ω, f (X ω) * g (Z γ ω) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hzero, hZ.2.2.2.2.1] with ω h0 hfin
        have hlow := (initialUnitBlockMass_ge γ hZ.1.le (X ω) (Z γ ω)).trans
          (twosided_initial_block_le_mass γ (B ν) (Z γ) ω)
        rw [h0, zero_sub] at hlow
        have h := ennreal_rpow_antitone_nonpos _ _ p hlow hp.le
        rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hfin 0 1).ne,
          ennreal_exp_rpow] at h
        have he : γ * -brownianUnitNorm (brownianShiftPath 0 (X ω)) * p =
            (-p) * γ * brownianUnitNorm (brownianShiftPath 0 (X ω)) := by ring
        rw [he] at h
        apply h.trans
        apply mul_le_mul_left
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZ.2.1.le (neg_nonneg.mpr hp.le)) (norm_nonneg _)
    _ = (∫⁻ ω, f (X ω) ∂P) * (∫⁻ ω, g (Z γ ω) ∂P) := hprod
    _ ≤ C * L := mul_le_mul' hfX hUnit'

end DOZZ.Proofs
