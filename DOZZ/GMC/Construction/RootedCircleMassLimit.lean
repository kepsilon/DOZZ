/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCircleKernel
public import DOZZ.GMC.Construction.GMCIntensityAdapter
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! The single-circle inserted measure converges to the singular rooted measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Exact intensity rules out an atom at every fixed deterministic root. -/
theorem gmc_atomless_at_root_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (u : ℂ) :
    ∀ᵐ ω ∂P, M ω {u} = 0 := by
  have hmeas := gmc_set_mass_aemeasurable_of_isGMCOf
    P X hX γ hγ hγ2 M hM {u} (measurableSet_singleton u)
  have href : gmcReferenceMeasure {u} = 0 := by
    exact (withDensity_absolutelyContinuous volume
      (fun x : ℂ => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)))) (measure_singleton u)
  exact (lintegral_eq_zero_iff' hmeas).mp
    ((equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM {u}
      (measurableSet_singleton u)).trans href)

/-- Finiteness of the point insertion and absence of a root atom give convergence of every
measurable-set mass of the circle insertion. The chaos measure itself is fixed throughout. -/
theorem circleRootedMeasure_mass_tendsto
    (γ : ℝ) (u : ℂ) (μ : Measure ℂ) (hAtom : μ {u} = 0)
    (hRoot : IsFiniteMeasure (gmcRootedMeasure γ u μ))
    (A : Set ℂ) (hA : MeasurableSet A) :
    Tendsto (fun n : ℕ =>
      (μ.withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))))) A)
      atTop (𝓝 (gmcRootedMeasure γ u μ A)) := by
  let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x))
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * Real.log 2))
  let F : ℕ → ℂ → ℝ≥0∞ := fun n x => A.indicator (fun x => ENNReal.ofReal
    (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ)))) x
  have hw : Measurable w := ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp (measurable_const.mul (CirclePotential.measurable_gffKernel u)))
  have hF (n : ℕ) : Measurable (F n) := by
    exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (continuous_circleKernelPotential u (n : ℝ)).measurable))).indicator hA
  have hne : ∀ᵐ x ∂μ, x ≠ u := by
    apply ae_iff.mpr
    simpa using hAtom
  have hbound (n : ℕ) : F n ≤ᵐ[μ] fun x => C * w x := by
    filter_upwards [hne] with x hxu
    have hpot := circleRootPotential_le_point_add_log_two u x (n : ℝ)
      (Nat.cast_nonneg n) hxu
    have hexp : Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ)) ≤
        Real.exp (γ ^ 2 * Real.log 2) * Real.exp (γ ^ 2 * gffKernel u x) := by
      calc
        _ ≤ Real.exp (γ ^ 2 * (gffKernel u x + Real.log 2)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpot (sq_nonneg γ))
        _ = _ := by rw [mul_add, Real.exp_add, mul_comm]
    have he : ENNReal.ofReal
        (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))) ≤ C * w x := by
      have h := ENNReal.ofReal_le_ofReal hexp
      simpa only [ENNReal.ofReal_mul (Real.exp_nonneg _), C, w] using h
    by_cases hx : x ∈ A
    · simpa [F, hx] using he
    · simp [F, hx]
  have hfin : (∫⁻ x, C * w x ∂μ) ≠ ⊤ := by
    let _ := hRoot
    have hm : (∫⁻ x, w x ∂μ) ≠ ⊤ := by
      have h := measure_ne_top (gmcRootedMeasure γ u μ) Set.univ
      simpa only [gmcRootedMeasure, withDensity_apply _ MeasurableSet.univ,
        Measure.restrict_univ, w] using h
    rw [lintegral_const_mul C hw]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (A.indicator w x)) := by
    filter_upwards [hne] with x hxu
    have hpot := (circleRootPotential_tendsto u x hxu).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have h : Tendsto (fun n : ℕ => ENNReal.ofReal
        (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ)))) atTop
        (𝓝 (w x)) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_exp.continuousAt.tendsto.comp (hpot.const_mul (γ ^ 2)))
    by_cases hx : x ∈ A
    · simpa only [F, Set.indicator_of_mem hx, w] using h
    · simp only [F, Set.indicator_of_notMem hx]
      exact tendsto_const_nhds
  have ht := tendsto_lintegral_of_dominated_convergence (fun x => C * w x) hF hbound hfin hlim
  simpa only [F, gmcRootedMeasure, withDensity_apply _ hA,
    ← lintegral_indicator hA, w] using ht

end DOZZ.Proofs
