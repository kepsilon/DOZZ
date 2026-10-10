/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CircleField
public import DOZZ.GMC.SharpMoments.PaleyZygmund
public import DOZZ.GMC.Annulus.HigherScales
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure

/-! # Laplace transforms of cutoff masses and their small-value tails

The small-deviation recursion for the cutoff reference mass is run on its Laplace transform
`x ↦ E exp (-eˣ M_r(A))`, which is bounded by one and antitone in `x`. This file records its basic
properties, the conversion between Laplace transforms, small-value probabilities and negative
moments, and the a-priori bound strictly below one that Paley–Zygmund gives uniformly in the
cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Laplace transform of the cutoff mass of `A` at level `exp x`. -/
noncomputable def cutoffLaplace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (A : Set ℂ) (x : ℝ) : ℝ :=
  ∫ ω, Real.exp (-(Real.exp x) * (regularizedGMC P Xc γ r ω A).toReal) ∂P

theorem measurable_regularizedGMC_apply_toReal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) :
    Measurable (fun ω => (regularizedGMC P Xc γ r ω A).toReal) :=
  ENNReal.measurable_toReal.comp
    ((Measure.measurable_coe hA).comp (regularizedGMC_measurable P X hX Xc hXc γ r))

theorem cutoffLaplace_integrand_le_one (s m : ℝ) (hs : 0 ≤ s) (hm : 0 ≤ m) :
    Real.exp (-s * m) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith)

theorem integrable_cutoffLaplace_integrand
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => Real.exp (-s * (regularizedGMC P Xc γ r ω A).toReal)) P := by
  let _ : IsProbabilityMeasure P := hX.1
  refine Integrable.of_bound (C := 1) ?_ (Eventually.of_forall fun ω => ?_)
  · exact (Real.measurable_exp.comp ((measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r
      A hA).const_mul (-s))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact cutoffLaplace_integrand_le_one s _ hs ENNReal.toReal_nonneg

theorem cutoffLaplace_nonneg
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (A : Set ℂ) (x : ℝ) :
    0 ≤ cutoffLaplace P Xc γ r A x :=
  integral_nonneg fun _ => (Real.exp_pos _).le

theorem cutoffLaplace_le_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (A : Set ℂ) (x : ℝ) :
    cutoffLaplace P Xc γ r A x ≤ 1 := by
  let _ : IsProbabilityMeasure P := hX.1
  unfold cutoffLaplace
  calc (∫ ω, Real.exp (-(Real.exp x) * (regularizedGMC P Xc γ r ω A).toReal) ∂P)
      ≤ ∫ _ω, (1 : ℝ) ∂P := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => (Real.exp_pos _).le)
          (integrable_const 1) (Eventually.of_forall fun ω => ?_)
        exact cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le ENNReal.toReal_nonneg
    _ = 1 := by simp

theorem cutoffLaplace_antitone
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) :
    Antitone (cutoffLaplace P Xc γ r A) := by
  intro x y hxy
  unfold cutoffLaplace
  refine integral_mono (integrable_cutoffLaplace_integrand P X hX Xc hXc γ r A hA _
    (Real.exp_pos y).le) (integrable_cutoffLaplace_integrand P X hX Xc hXc γ r A hA _
    (Real.exp_pos x).le) (fun ω => ?_)
  apply Real.exp_le_exp.mpr
  have hm : 0 ≤ (regularizedGMC P Xc γ r ω A).toReal := ENNReal.toReal_nonneg
  have he : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
  nlinarith

/-- Small values of a nonnegative random variable cost at most `e` times its Laplace transform at
the reciprocal level. -/
theorem measure_toReal_le_le_exp_mul_laplace
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (m : Ω → ℝ) (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω) (x : ℝ) :
    P {ω | m ω ≤ Real.exp (-x)} ≤
      ENNReal.ofReal (Real.exp 1 * ∫ ω, Real.exp (-(Real.exp x) * m ω) ∂P) := by
  have hint : Integrable (fun ω => Real.exp (-(Real.exp x) * m ω)) P := by
    refine Integrable.of_bound (C := 1) (Real.measurable_exp.comp
      (hm.const_mul _)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le (hm0 ω)
  have hset : MeasurableSet {ω | m ω ≤ Real.exp (-x)} := measurableSet_le hm measurable_const
  have hpoint : ∀ ω, ({ω | m ω ≤ Real.exp (-x)}.indicator 1 ω) ≤
      Real.exp 1 * Real.exp (-(Real.exp x) * m ω) := by
    intro ω
    by_cases hω : m ω ≤ Real.exp (-x)
    · rw [Set.indicator_of_mem (show ω ∈ {ω | m ω ≤ Real.exp (-x)} from hω), Pi.one_apply]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hmul : Real.exp x * m ω ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_left hω (Real.exp_pos x).le
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at hmul
      linarith
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | m ω ≤ Real.exp (-x)} from hω)]
      exact mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hP : P {ω | m ω ≤ Real.exp (-x)} =
      ENNReal.ofReal (∫ ω, {ω | m ω ≤ Real.exp (-x)}.indicator 1 ω ∂P) := by
    rw [integral_indicator_one hset, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hP, ← integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  exact integral_mono ((integrable_const 1).indicator hset) (hint.const_mul _) hpoint

/-- Gaussian-type negative moments give Gaussian small-value tails (Chernoff). -/
theorem measure_le_exp_neg_of_negMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → ℝ≥0∞) (hY : AEMeasurable Y P) (a b : ℝ) (hb : 0 < b)
    (hmom : ∀ q : ℝ, 0 < q → ∫⁻ ω, Y ω ^ (-q) ∂P ≤ ENNReal.ofReal (Real.exp (a * q + b * q ^ 2)))
    (t : ℝ) (ht : a < t) :
    P {ω | Y ω ≤ ENNReal.ofReal (Real.exp (-t))} ≤
      ENNReal.ofReal (Real.exp (-(t - a) ^ 2 / (4 * b))) := by
  set q : ℝ := (t - a) / (2 * b) with hqdef
  have hq : 0 < q := div_pos (by linarith) (by linarith)
  have hYq : AEMeasurable (fun ω => Y ω ^ (-q)) P :=
    hY.pow_const (-q)
  have hlevel : ∀ ω, Y ω ≤ ENNReal.ofReal (Real.exp (-t)) →
      ENNReal.ofReal (Real.exp (q * t)) ≤ Y ω ^ (-q) := by
    intro ω hω
    have h1 : (ENNReal.ofReal (Real.exp (-t))) ^ (-q) ≤ Y ω ^ (-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hω hq.le)
    have h2 : (ENNReal.ofReal (Real.exp (-t))) ^ (-q) = ENNReal.ofReal (Real.exp (q * t)) := by
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
      congr 2
      ring
    rwa [h2] at h1
  have hsub : {ω | Y ω ≤ ENNReal.ofReal (Real.exp (-t))} ⊆
      {ω | ENNReal.ofReal (Real.exp (q * t)) ≤ Y ω ^ (-q)} := fun ω hω => hlevel ω hω
  have hmarkov := mul_meas_ge_le_lintegral₀ hYq (ENNReal.ofReal (Real.exp (q * t)))
  have hpos : ENNReal.ofReal (Real.exp (q * t)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hfin : ENNReal.ofReal (Real.exp (q * t)) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc P {ω | Y ω ≤ ENNReal.ofReal (Real.exp (-t))}
      ≤ P {ω | ENNReal.ofReal (Real.exp (q * t)) ≤ Y ω ^ (-q)} := measure_mono hsub
    _ ≤ (∫⁻ ω, Y ω ^ (-q) ∂P) / ENNReal.ofReal (Real.exp (q * t)) := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hfin), mul_comm]
        exact hmarkov
    _ ≤ ENNReal.ofReal (Real.exp (a * q + b * q ^ 2)) / ENNReal.ofReal (Real.exp (q * t)) := by
        gcongr
        exact hmom q hq
    _ = ENNReal.ofReal (Real.exp (-(t - a) ^ 2 / (4 * b))) := by
        rw [← ENNReal.ofReal_div_of_pos (Real.exp_pos _), ← Real.exp_sub]
        congr 2
        rw [hqdef]
        field_simp
        ring

end DOZZ.Proofs
