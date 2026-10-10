/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.LocationTransfer
public import DOZZ.GMC.Moments.CircleScale
public import DOZZ.GMC.FieldGaussianCommonScalar
public import DOZZ.GMC.FieldChaosConcavePower
public import DOZZ.GMC.FieldChaosConvexPower

/-! # Exact scaling of cutoff chaos outside the unit disk

Outside the unit disk the equator kernel gains `log c` under the dilation `x ↦ c x` with `c ≥ 1`,
and so does the covariance of circle averages whose circles stay outside the unit disk, with the
cutoff shifted by `log c`. Comparing the dilated cutoff field with the shifted cutoff field plus
an independent Gaussian scalar of variance `log c`, the two covariances agree, so Kahane's
inequalities in both directions give an exact identity for every moment of exterior cutoff
masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Outside the unit disk the regular part of the circle potential gains `log c` under a
dilation by `c ≥ 1`. -/
theorem circleLogPotential_pin_scale_of_outside {c : ℝ} (hc : 1 ≤ c) {x : ℂ} {r : ℝ}
    (hout : 1 + Real.exp (-r) ≤ ‖x‖) :
    circleLogPotential ‖(c : ℂ) * x‖₊ ⟨Real.exp (-(r - Real.log c)), Real.exp_pos _⟩
        ⟨1, by norm_num⟩ =
      Real.log c + circleLogPotential ‖x‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ := by
  have hc0 : 0 < c := by linarith
  have hlogc : Continuous fun z : ℂ => Real.log (normPlus z) := continuous_log_normPlus
  rw [← integral_log_normPlus_circleMeasure_eq_closed, ← integral_log_normPlus_circleMeasure_eq_closed,
    circleMeasure_scale hc0 x r,
    integral_map (by fun_prop : Measurable fun z : ℂ => (c : ℂ) * z).aemeasurable
      hlogc.measurable.aestronglyMeasurable]
  have hae : (fun z => Real.log (normPlus ((c : ℂ) * z))) =ᵐ[circleMeasure x r]
      fun z => Real.log c + Real.log (normPlus z) := by
    filter_upwards [ae_mem_sphere_circleMeasure x r] with z hz
    rw [mem_sphere_iff_norm] at hz
    have hz1 : 1 ≤ ‖z‖ := by
      have := norm_sub_norm_le x z
      rw [norm_sub_rev] at this
      linarith
    have hnz : normPlus z = ‖z‖ := max_eq_right hz1
    have hncz : normPlus ((c : ℂ) * z) = c * ‖z‖ := by
      rw [normPlus, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
      exact max_eq_right (by nlinarith)
    rw [hncz, hnz, Real.log_mul hc0.ne' (by linarith)]
  have hint : Integrable (fun z => Real.log (normPlus z)) (circleMeasure x r) :=
    integrable_circleMeasure_of_circleIntegrable x r hlogc.measurable
      hlogc.continuousOn.circleIntegrable'
  have := circleMeasure_isProbability x r
  rw [integral_congr_ae hae, integral_add (integrable_const _) hint, integral_const,
    probReal_univ, one_smul]

/-- Outside the unit disk a common dilation by `c ≥ 1`, with the cutoffs shifted by `log c`,
adds `log c` to the covariance of two circle averages. -/
theorem circleField_covariance_exterior_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {c : ℝ} (hc : 1 ≤ c) (x y : ℂ)
    (r s : ℝ) (hx : 1 + Real.exp (-r) ≤ ‖x‖) (hy : 1 + Real.exp (-s) ≤ ‖y‖) :
    ∫ ω, Xc ω ((c : ℂ) * x) (r - Real.log c) * Xc ω ((c : ℂ) * y) (s - Real.log c) ∂P =
      ∫ ω, Xc ω x r * Xc ω y s ∂P + Real.log c := by
  have hc0 : 0 < c := by linarith
  have h1 := isCircleAverage_covariance P X hX Xc hXc ((c : ℂ) * x) ((c : ℂ) * y)
    (r - Real.log c) (s - Real.log c)
  have h2 := isCircleAverage_covariance P X hX Xc hXc x y r s
  have h3 := circleAverage_covariance_integral P X Xc hX hXc ((c : ℂ) * x) ((c : ℂ) * y)
    (r - Real.log c) (s - Real.log c)
  have h4 := circleAverage_covariance_integral P X Xc hX hXc x y r s
  have h5 := circleAverage_covariance P X Xc hX hXc ((c : ℂ) * x) ((c : ℂ) * y)
    (r - Real.log c) (s - Real.log c)
  have h6 := circleAverage_covariance P X Xc hX hXc x y r s
  change gaussianCovariance P _ _ = gaussianCovariance P _ _ + Real.log c
  rw [h1, h2, ← h3, ← h4, h5, h6, circleLogPotential_scale hc0 x y r s,
    circleLogPotential_pin_scale_of_outside hc hx, circleLogPotential_pin_scale_of_outside hc hy]
  ring

/-- Circle averages at dilated points form a centered Gaussian field. -/
theorem circleAverage_scale_isCenteredGaussianField
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) (c : ℂ) :
    IsCenteredGaussianField P (fun ω y => Xc ω (c * y) r) :=
  ⟨(hXc.1 r).comp (measurable_fst.prodMk (measurable_snd.const_mul c)),
    fun _ y => circleAverage_finite_family_jointly_gaussian P X hX Xc hXc
      (fun i => (c * y i, r))⟩

/-- Integrals over a planar dilation: `∫ f = c² ∫ f (c ·)`. -/
theorem lintegral_eq_sq_mul_lintegral_comp_dilation {c : ℝ} (hc : 0 < c) (f : ℂ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, f y = ENNReal.ofReal (c ^ 2) * ∫⁻ x, f ((c : ℂ) * x) := by
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hc.ne'
  rw [Complex.finrank_real_complex] at hmap
  have hcomp : (fun x : ℂ => f ((c : ℂ) * x)) = fun x => f (c • x) := by
    funext x
    rw [Complex.real_smul]
  have hlin : ∫⁻ x, f ((c : ℂ) * x) = ENNReal.ofReal (|(c ^ 2)⁻¹|) * ∫⁻ y, f y := by
    rw [hcomp, ← lintegral_map hf (measurable_const_smul c), hmap, lintegral_smul_measure,
      smul_eq_mul]
  rw [hlin, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), abs_of_pos (by positivity),
    mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

/-- An exterior dilated cutoff mass is a scaled continuum Wick mass of the dilated circle
field. -/
theorem cutoff_dilated_mass_eq_fieldChaosMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) {c : ℝ} (hc : 1 ≤ c)
    (A : Set ℂ) (hA : MeasurableSet A) (hA1 : ∀ x ∈ A, 1 ≤ ‖x‖) (w : ℂ → ℝ≥0)
    (hw : Measurable w) (ω : Ω) :
    (∫⁻ y in {y : ℂ | (c : ℂ)⁻¹ * y ∈ A}, (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ r ω) =
      ENNReal.ofReal (c ^ (-2 : ℝ)) *
        fieldChaosMass P (fun ω x => Xc ω ((c : ℂ) * x) r) (gmcReferenceMeasure.restrict A) w γ
          ω := by
  let _ := hX.1
  have hc0 : 0 < c := by linarith
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
  set E : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) * normPlus x ^ (-4 : ℝ))
    with hE
  have hV : Measurable (fun x : ℂ => ∫ ω', Xc ω' x r ^ 2 ∂P) := by
    have hf : Measurable (fun q : ℂ × Ω => Xc q.2 q.1 r ^ 2) :=
      ((hXc.1 r).comp measurable_swap).pow_const 2
    exact hf.stronglyMeasurable.integral_prod_right.measurable
  have hX1 : Measurable (fun x : ℂ => Xc ω x r) :=
    (hXc.1 r).comp (measurable_const.prodMk measurable_id)
  have hEm : Measurable E := by
    rw [hE]
    exact ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      ((hX1.const_mul γ).sub (hV.const_mul _))).mul (measurable_normPlus.pow_const _))
  set S : Set ℂ := {y : ℂ | (c : ℂ)⁻¹ * y ∈ A} with hS
  have hSm : MeasurableSet S := (measurable_const_mul _) hA
  have hwS : Measurable (fun y : ℂ => (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞)) :=
    (hw.comp (measurable_const_mul _)).coe_nnreal_ennreal
  have hlhs : (∫⁻ y in S, (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) =
      ∫⁻ y, S.indicator (fun y => (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞) * E y) y := by
    rw [regularizedGMC, restrict_withDensity hSm, lintegral_withDensity_eq_lintegral_mul _ hEm hwS,
      ← lintegral_indicator hSm]
    have hfun : (E * fun y => (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞)) =
        fun y => (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞) * E y := by
      funext y
      exact mul_comm (E y) (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞)
    rw [hfun]
  have hdens : Measurable fun x : ℂ => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) :=
    ENNReal.measurable_ofReal.comp (measurable_normPlus.pow_const _)
  set W : ℂ → ℝ≥0∞ := fun x => (w x : ℝ≥0∞) * ENNReal.ofReal (Real.exp (γ * Xc ω ((c : ℂ) * x) r -
    γ ^ 2 / 2 * ∫ ω', Xc ω' ((c : ℂ) * x) r ^ 2 ∂P)) with hW
  have hVc : Measurable (fun x : ℂ => ∫ ω', Xc ω' ((c : ℂ) * x) r ^ 2 ∂P) :=
    hV.comp (measurable_const_mul _)
  have hWm : Measurable W := by
    rw [hW]
    exact hw.coe_nnreal_ennreal.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((hX1.comp (measurable_const_mul _)).const_mul γ).sub (hVc.const_mul _))))
  have hrhs : fieldChaosMass P (fun ω x => Xc ω ((c : ℂ) * x) r) (gmcReferenceMeasure.restrict A)
      w γ ω = ∫⁻ x, A.indicator (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) * W x) x := by
    rw [fieldChaosMass, gmcReferenceMeasure, restrict_withDensity hA,
      lintegral_withDensity_eq_lintegral_mul _ hdens hWm, lintegral_indicator hA]
    rfl
  have hpt : ∀ x, S.indicator (fun y => (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞) * E y) ((c : ℂ) * x) =
      ENNReal.ofReal (c ^ (-4 : ℝ)) *
        A.indicator (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) * W x) x := by
    intro x
    have hcx : (c : ℂ)⁻¹ * ((c : ℂ) * x) = x := by field_simp
    by_cases hx : x ∈ A
    · have hxS : (c : ℂ) * x ∈ S := by
        show (c : ℂ)⁻¹ * ((c : ℂ) * x) ∈ A
        rw [hcx]
        exact hx
      have hx1 : 1 ≤ ‖x‖ := hA1 x hx
      have hn : normPlus ((c : ℂ) * x) = c * normPlus x := by
        rw [normPlus, normPlus, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
          max_eq_right hx1, max_eq_right (by nlinarith)]
      have hnx : 0 ≤ normPlus x := le_trans zero_le_one (le_max_left _ _)
      rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hx, hcx, hE]
      simp only []
      rw [hn, Real.mul_rpow hc0.le hnx, hW]
      have he : 0 ≤ Real.exp (γ * Xc ω ((c : ℂ) * x) r -
          γ ^ 2 / 2 * ∫ ω', Xc ω' ((c : ℂ) * x) r ^ 2 ∂P) := (Real.exp_pos _).le
      rw [show Real.exp (γ * Xc ω ((c : ℂ) * x) r -
          γ ^ 2 / 2 * ∫ ω', Xc ω' ((c : ℂ) * x) r ^ 2 ∂P) *
            (c ^ (-4 : ℝ) * normPlus x ^ (-4 : ℝ)) =
          c ^ (-4 : ℝ) * (normPlus x ^ (-4 : ℝ) * Real.exp (γ * Xc ω ((c : ℂ) * x) r -
            γ ^ 2 / 2 * ∫ ω', Xc ω' ((c : ℂ) * x) r ^ 2 ∂P)) by ring,
        ENNReal.ofReal_mul (Real.rpow_nonneg hc0.le _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hnx _)]
      ring
    · have hxS : (c : ℂ) * x ∉ S := by
        show (c : ℂ)⁻¹ * ((c : ℂ) * x) ∉ A
        rw [hcx]
        exact hx
      rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hx, mul_zero]
  have hprod : Measurable (fun y => (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞) * E y) := hwS.mul hEm
  have hprodA : Measurable (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) * W x) :=
    hdens.mul hWm
  rw [hlhs, lintegral_eq_sq_mul_lintegral_comp_dilation hc0 _ (hprod.indicator hSm),
    lintegral_congr hpt, lintegral_const_mul _ (hprodA.indicator hA), hrhs, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [show c ^ 2 = c ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hc0]
  norm_num

/-- Exact scaling of exterior cutoff moments: dilating a set outside the disk of radius two by
`c ≥ 1` multiplies every moment by `c ^ (-2p) e^{γ² log c (p² - p) / 2}` and shifts the cutoff
by `log c`. -/
theorem cutoff_exterior_scale_moment_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) {r : ℝ} (hr : 0 ≤ r)
    {c : ℝ} (hc : 1 ≤ c) (A : Set ℂ) (hA : MeasurableSet A) (hA2 : ∀ x ∈ A, 2 ≤ ‖x‖)
    (w : ℂ → ℝ≥0) (hw : Measurable w) (hwb : ∃ b : ℝ≥0, ∀ x, w x ≤ b) (p : ℝ) :
    ∫⁻ ω, (∫⁻ y in {y : ℂ | (c : ℂ)⁻¹ * y ∈ A}, (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ r ω) ^ p ∂P =
      ENNReal.ofReal (c ^ (-2 * p) * Real.exp (γ ^ 2 * Real.log c / 2 * (p ^ 2 - p))) *
        ∫⁻ ω, (∫⁻ x in A, (w x : ℝ≥0∞) ∂regularizedGMC P Xc γ (r + Real.log c) ω) ^ p ∂P := by
  let _ : IsProbabilityMeasure P := hX.1
  have hc0 : 0 < c := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  set ν : Measure ℂ := gmcReferenceMeasure.restrict A with hν
  set G : Measure ℝ := gaussianReal 0 1 with hG
  set Φ : Ω → ℂ → ℝ := fun ω x => Xc ω ((c : ℂ) * x) r with hΦ
  set Ψ : Ω → ℂ → ℝ := fun ω x => Xc ω x (r + Real.log c) with hΨ
  set Ψ' : Ω × ℝ → ℂ → ℝ := fun ω x => Ψ ω.1 x + Real.sqrt (Real.log c) * ω.2 with hΨ'
  have hΦg : IsCenteredGaussianField P Φ :=
    circleAverage_scale_isCenteredGaussianField P X hX Xc hXc r c
  have hΨg : IsCenteredGaussianField P Ψ :=
    circleAverage_isCenteredGaussianField P X hX Xc hXc (r + Real.log c)
  have hΨ'g : IsCenteredGaussianField (P.prod G) Ψ' :=
    independent_common_scalar_add_isCenteredGaussianField P Ψ hΨg _
  -- the two covariances agree on `A`
  have hcovpt : ∀ x ∈ A, ∀ y ∈ A,
      ∫ ω, Φ ω x * Φ ω y ∂P = ∫ ω, Ψ' ω x * Ψ' ω y ∂(P.prod G) := by
    intro x hx y hy
    have hexp : Real.exp (-(r + Real.log c)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h := circleField_covariance_exterior_scale P X hX Xc hXc hc x y (r + Real.log c)
      (r + Real.log c) (by linarith [hA2 x hx]) (by linarith [hA2 y hy])
    rw [show r + Real.log c - Real.log c = r by ring] at h
    have h2 := gaussianCovariance_field_independent_common_scalar_add P Ψ hΨg
      (Real.sqrt (Real.log c)) x y
    rw [Real.sq_sqrt hlogc] at h2
    change ∫ ω, Φ ω x * Φ ω y ∂P = gaussianCovariance (P.prod G) _ _
    rw [h2]
    exact h
  have hAA : ∀ᵐ q ∂ν.prod ν, q.1 ∈ A ∧ q.2 ∈ A := by
    rw [hν, Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hA.prod hA)] with q hq
    exact hq
  have hAν : ∀ᵐ x ∂ν, x ∈ A := ae_restrict_mem hA
  have hcov₁ : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ ω q.1 * Φ ω q.2 ∂P ≤ ∫ ω, Ψ' ω q.1 * Ψ' ω q.2 ∂(P.prod G) := by
    filter_upwards [hAA] with q hq
    exact (hcovpt q.1 hq.1 q.2 hq.2).le
  have hcov₂ : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Ψ' ω q.1 * Ψ' ω q.2 ∂(P.prod G) ≤ ∫ ω, Φ ω q.1 * Φ ω q.2 ∂P := by
    filter_upwards [hAA] with q hq
    exact (hcovpt q.1 hq.1 q.2 hq.2).ge
  have hdiag₁ : ∀ᵐ x ∂ν, ∫ ω, Φ ω x ^ 2 ∂P ≤ ∫ ω, Ψ' ω x ^ 2 ∂(P.prod G) := by
    filter_upwards [hAν] with x hx
    simpa only [pow_two] using (hcovpt x hx x hx).le
  have hdiag₂ : ∀ᵐ x ∂ν, ∫ ω, Ψ' ω x ^ 2 ∂(P.prod G) ≤ ∫ ω, Φ ω x ^ 2 ∂P := by
    filter_upwards [hAν] with x hx
    simpa only [pow_two] using (hcovpt x hx x hx).ge
  -- Kahane in both directions
  have hmom : ∫⁻ ω, fieldChaosMass P Φ ν w γ ω ^ p ∂P =
      ∫⁻ ω, fieldChaosMass (P.prod G) Ψ' ν w γ ω ^ p ∂(P.prod G) := by
    by_cases hp : p ≤ 0 ∨ 1 ≤ p
    · exact le_antisymm
        (kahane_field_power_convex P (P.prod G) Φ Ψ' hΦg hΨ'g ν w hw hwb γ p hp hcov₁ hdiag₁)
        (kahane_field_power_convex (P.prod G) P Ψ' Φ hΨ'g hΦg ν w hw hwb γ p hp hcov₂ hdiag₂)
    · push Not at hp
      exact le_antisymm
        (kahane_field_power_concave (P.prod G) P Ψ' Φ hΨ'g hΦg ν w hw hwb γ p ⟨hp.1, hp.2⟩
          hcov₂ hdiag₂)
        (kahane_field_power_concave P (P.prod G) Φ Ψ' hΦg hΨ'g ν w hw hwb γ p ⟨hp.1, hp.2⟩
          hcov₁ hdiag₁)
  have hfac := fieldChaosMoment_independent_common_scalar_factor P Ψ hΨg ν w hw hwb γ
    (Real.sqrt (Real.log c)) p
  rw [Real.sq_sqrt hlogc] at hfac
  -- the cutoff masses as chaos masses
  have hlhs : ∀ ω, (∫⁻ y in {y : ℂ | (c : ℂ)⁻¹ * y ∈ A}, (w ((c : ℂ)⁻¹ * y) : ℝ≥0∞)
      ∂regularizedGMC P Xc γ r ω) = ENNReal.ofReal (c ^ (-2 : ℝ)) * fieldChaosMass P Φ ν w γ ω :=
    fun ω => cutoff_dilated_mass_eq_fieldChaosMass P X hX Xc hXc γ r hc A hA
      (fun x hx => le_trans one_le_two (hA2 x hx)) w hw ω
  have hrhs : ∀ ω, (∫⁻ x in A, (w x : ℝ≥0∞) ∂regularizedGMC P Xc γ (r + Real.log c) ω) =
      fieldChaosMass P Ψ ν w γ ω :=
    fun ω => regularizedGMC_weighted_eq_fieldChaosMass P X hX Xc hXc γ (r + Real.log c) A hA w hw
      ω
  have hc2 : ENNReal.ofReal (c ^ (-2 : ℝ)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hc0 _)).ne'
  simp only [hlhs, hrhs]
  rw [lintegral_congr fun ω => ennreal_mul_rpow_of_ne_zero_ne_top _ _ hc2 ENNReal.ofReal_ne_top p,
    lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hc2 ENNReal.ofReal_ne_top), hmom,
    hfac, ← mul_assoc, ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hc0 _),
    ← Real.rpow_mul hc0.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc0.le _)]

end DOZZ.Proofs
