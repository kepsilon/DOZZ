/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.Statements.GMC.RegularizedLogChaosTestMass
public import DOZZ.GMC.CircleAverage
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Identify the admissible cutoff integral with the circle GMC measure integral. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Under a circle witness, the admissible logarithmic cutoff and the circle GMC
`DOZZ.regularizedGMC` have the same test integral at matching logarithmic scale. -/
theorem circleCutoff_testMass_eq_regularizedGMC
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) :
    regularizedLogChaosTestMass P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f =
      ∫ x, f x ∂regularizedGMC P Xc γ r ω := by
  classical
  let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  have hVmeas : Measurable V := by
    let _ := hX.1
    let q : ℂ → Ω → ℝ := fun x ω' => Xc ω' x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase : Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r) :=
        (hXc.1 r).comp measurable_swap
      have hEq : (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) =
          fun p => Xc p.2 p.1 r * Xc p.2 p.1 r := by
        funext p
        ring
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [hEq]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω', q x ω' ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  have hweightMeas : Measurable (fun x : ℂ => normPlus x ^ (-4 : ℝ)) := by
    unfold normPlus
    fun_prop
  let d₀ : ℂ → ℝ := fun x => normPlus x ^ (-4 : ℝ)
  let d₁ : ℂ → ℝ := fun x =>
    Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ)
  let e₀ : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (d₀ x)
  let e₁ : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (d₁ x)
  have hd₀ : Measurable d₀ := hweightMeas
  have hd₁ : Measurable d₁ := by
    have hfield : Measurable (fun x : ℂ => Xc ω x r) :=
      (hXc.1 r).comp (measurable_const.prodMk measurable_id)
    dsimp [d₁]
    fun_prop
  have he₀ : Measurable e₀ := ENNReal.measurable_ofReal.comp hd₀
  have he₁ : Measurable e₁ := ENNReal.measurable_ofReal.comp hd₁
  have he₀top : ∀ᵐ x ∂volume, e₀ x < ∞ :=
    ae_of_all _ (fun x => ENNReal.ofReal_lt_top)
  have he₁top : ∀ᵐ x ∂volume, e₁ x < ∞ :=
    ae_of_all _ (fun x => ENNReal.ofReal_lt_top)
  have hd₀nonneg (x : ℂ) : 0 ≤ d₀ x := by
    dsimp [d₀]
    exact Real.rpow_nonneg (le_of_lt (by simp [normPlus])) _
  have hd₁nonneg (x : ℂ) : 0 ≤ d₁ x := by
    dsimp [d₁]
    exact mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg (le_of_lt (by simp [normPlus])) _)
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    rw [one_div, Real.log_inv, Real.log_exp]
    ring
  have hleft :
      regularizedLogChaosTestMass P Set.univ d₀
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f =
        ∫ x, (e₀ x).toReal * (f x * Real.exp
          (γ * Xc ω x r - γ ^ 2 / 2 * V x)) ∂volume := by
    rw [regularizedLogChaosTestMass, logRegularizationReference, Measure.restrict_univ]
    rw [integral_withDensity_eq_integral_toReal_smul he₀ he₀top]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hlog]
    simp [e₀, d₀, V, smul_eq_mul]
  have hright :
      (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
        ∫ x, (e₁ x).toReal * f x ∂volume := by
    rw [regularizedGMC]
    rw [integral_withDensity_eq_integral_toReal_smul he₁ he₁top]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [e₁, d₁, ENNReal.toReal_ofReal (hd₁nonneg x), smul_eq_mul]
  calc
    _ = ∫ x, (e₀ x).toReal * (f x * Real.exp
          (γ * Xc ω x r - γ ^ 2 / 2 * V x)) ∂volume := hleft
    _ = ∫ x, (e₁ x).toReal * f x ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (ENNReal.ofReal (normPlus x ^ (-4 : ℝ))).toReal *
          (f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x)) =
        (ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) *
          normPlus x ^ (-4 : ℝ))).toReal * f x
      rw [ENNReal.toReal_ofReal (hd₀nonneg x),
        ENNReal.toReal_ofReal (hd₁nonneg x)]
      ring
    _ = _ := hright.symm

end DOZZ.Proofs
