/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.LaplaceTail
public import DOZZ.GMC.Annulus.ReferenceIntensity

/-! # A uniform a-priori bound on cutoff Laplace transforms

The cutoff reference mass has exact mean `σ(D)` and a `p`-th moment bounded uniformly in the
cutoff for some `1 < p < 4/γ²`. Paley–Zygmund then gives a fixed positive probability that the
mass exceeds `σ(D)/2`, so its Laplace transform stays a fixed amount below one at large levels,
uniformly in the cutoff. This is the a-priori input that starts the small-deviation recursion. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The expected cutoff mass of a measurable set is its reference mass. -/
theorem regularizedGMC_lintegral_apply_eq_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (A : Set ℂ) (hA : MeasurableSet A) :
    ∫⁻ ω, regularizedGMC P Xc γ r ω A ∂P = gmcReferenceMeasure A := by
  have h := regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r
    (A.indicator 1) (measurable_one.indicator hA)
  simp only [lintegral_indicator_one hA] at h
  exact h

/-- With a uniform `p`-th moment bound, the cutoff mass of a set exceeds half its reference mass
with probability bounded below uniformly in the cutoff. -/
theorem regularizedGMC_half_mass_prob_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ p : ℝ) (hp : 1 < p)
    (A : Set ℂ) (hA : MeasurableSet A) (hA0 : gmcReferenceMeasure A ≠ 0)
    (hAtop : gmcReferenceMeasure A ≠ ⊤) (C : ℝ≥0∞) (hC : C < ⊤) :
    ∃ π₀ : ℝ, 0 < π₀ ∧ ∀ r : ℝ,
      gmcMassMoment P (regularizedGMC P Xc γ r) A p ≤ C →
      ENNReal.ofReal π₀ ≤
        P {ω | ENNReal.ofReal ((1 / 2) * (gmcReferenceMeasure A).toReal) <
          regularizedGMC P Xc γ r ω A} := by
  let _ : IsProbabilityMeasure P := hX.1
  set σ : ℝ := (gmcReferenceMeasure A).toReal with hσdef
  have hσ : 0 < σ := ENNReal.toReal_pos hA0 hAtop
  set K : ℝ := C.toReal + 1 with hKdef
  have hK : 0 < K := by positivity
  refine ⟨((1 - 1 / 2) * σ) ^ (p / (p - 1)) / K ^ (1 / (p - 1)), ?_, fun r hr => ?_⟩
  · apply div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hK _)
  · have hZ : AEMeasurable (fun ω => regularizedGMC P Xc γ r ω A) P :=
      ((Measure.measurable_coe hA).comp (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable
    have hmean : ENNReal.ofReal σ ≤ ∫⁻ ω, regularizedGMC P Xc γ r ω A ∂P := by
      rw [regularizedGMC_lintegral_apply_eq_reference P X hX Xc hXc γ r A hA, hσdef,
        ENNReal.ofReal_toReal hAtop]
    have hmom : ∫⁻ ω, regularizedGMC P Xc γ r ω A ^ p ∂P ≤ ENNReal.ofReal K := by
      calc ∫⁻ ω, regularizedGMC P Xc γ r ω A ^ p ∂P = gmcMassMoment P
            (regularizedGMC P Xc γ r) A p := rfl
        _ ≤ C := hr
        _ = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hC.ne).symm
        _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (by linarith)
    exact paley_zygmund_lintegral P (fun ω => regularizedGMC P Xc γ r ω A) hZ p (1 / 2) σ K hp
      (by norm_num) (by norm_num) hσ hK hmean hmom

/-- Uniformly in the cutoff, the Laplace transform of a reference-ball mass stays a fixed amount
below one up to a doubly exponentially small error. -/
theorem cutoffLaplace_apriori
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (R : ℝ) (hR : 0 < R) (hRsmall : R ≤ 1 / 8) :
    ∃ π₀ : ℝ, 0 < π₀ ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : ℝ,
      cutoffLaplace P Xc γ r (Metric.ball 0 R) x ≤
        1 - π₀ + Real.exp (-(Real.exp x) *
          ((1 / 2) * (gmcReferenceMeasure (Metric.ball (0 : ℂ) R)).toReal)) := by
  let _ : IsProbabilityMeasure P := hX.1
  set D : Set ℂ := Metric.ball (0 : ℂ) R with hDdef
  have hD : MeasurableSet D := Metric.isOpen_ball.measurableSet
  have hD0 : gmcReferenceMeasure D ≠ 0 :=
    (gmc_reference_ball_intensity_pos hR (by linarith)).ne'
  have hDtop : gmcReferenceMeasure D ≠ ⊤ :=
    ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
  obtain ⟨p, hp, hpc⟩ := gmc_subcritical_higher_order_exists hγ hγ2
  obtain ⟨C, hC, hCbound⟩ := regularizedGMC_reference_positive_moment_uniform P X hX Xc hXc γ p
    hγ hp hpc hR hRsmall
  obtain ⟨π₀, hπ₀, hprob⟩ := regularizedGMC_half_mass_prob_lower P X hX Xc hXc γ p hp D hD hD0
    hDtop C hC
  refine ⟨π₀, hπ₀, fun r hr x => ?_⟩
  set h : ℝ := (1 / 2) * (gmcReferenceMeasure D).toReal with hhdef
  let m : Ω → ℝ := fun ω => (regularizedGMC P Xc γ r ω D).toReal
  have hm : Measurable m := measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ r D hD
  let E : Set Ω := {ω | h < m ω}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hm
  -- the ENNReal event is contained in `E` up to the null set where the mass is infinite
  have hfin := regularizedGMC_finite_ae P X hX Xc hXc γ r
  have hsubset : {ω | ENNReal.ofReal h < regularizedGMC P Xc γ r ω D} ≤ᵐ[P] E := by
    filter_upwards [hfin] with ω hω hlt
    have hne : regularizedGMC P Xc γ r ω D ≠ ⊤ := measure_ne_top _ _
    change h < (regularizedGMC P Xc γ r ω D).toReal
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hne).mp hlt
    exact this
  have hPE : ENNReal.ofReal π₀ ≤ P E :=
    (hprob r (hCbound r hr)).trans (measure_mono_ae hsubset)
  have hPEreal : π₀ ≤ P.real E := by
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hPE
  have hpoint : ∀ ω, Real.exp (-(Real.exp x) * m ω) ≤
      Eᶜ.indicator 1 ω + Real.exp (-(Real.exp x) * h) := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hω), zero_add]
      apply Real.exp_le_exp.mpr
      have : h ≤ m ω := le_of_lt hω
      nlinarith [Real.exp_pos x]
    · rw [Set.indicator_of_mem (Set.mem_compl hω), Pi.one_apply]
      have h1 : Real.exp (-(Real.exp x) * m ω) ≤ 1 :=
        cutoffLaplace_integrand_le_one _ _ (Real.exp_pos x).le ENNReal.toReal_nonneg
      linarith [Real.exp_pos (-(Real.exp x) * h)]
  have hint : Integrable (fun ω => Real.exp (-(Real.exp x) * m ω)) P :=
    integrable_cutoffLaplace_integrand P X hX Xc hXc γ r D hD _ (Real.exp_pos x).le
  have hint2 : Integrable (fun ω => Eᶜ.indicator (1 : Ω → ℝ) ω +
      Real.exp (-(Real.exp x) * h)) P :=
    ((integrable_const 1).indicator hE.compl).add (integrable_const _)
  calc cutoffLaplace P Xc γ r D x = ∫ ω, Real.exp (-(Real.exp x) * m ω) ∂P := rfl
    _ ≤ ∫ ω, (Eᶜ.indicator (1 : Ω → ℝ) ω + Real.exp (-(Real.exp x) * h)) ∂P :=
        integral_mono hint hint2 hpoint
    _ = P.real Eᶜ + Real.exp (-(Real.exp x) * h) := by
        rw [integral_add ((integrable_const 1).indicator hE.compl) (integrable_const _),
          integral_indicator_one hE.compl, integral_const, probReal_univ, one_smul]
    _ = 1 - P.real E + Real.exp (-(Real.exp x) * h) := by
        rw [probReal_compl_eq_one_sub hE]
    _ ≤ 1 - π₀ + Real.exp (-(Real.exp x) * h) := by linarith

end DOZZ.Proofs
