/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.Field
public import DOZZ.GMC.Assembly.AdmissibleGMC
public import DOZZ.GMC.GaussianInputs

/-!
# Orthogonal radial projection of circle cutoffs

The radial part of an off-center circle cutoff is its circle average of the radial
path. Subtracting the radial value only at the center would leave a nonzero covariance
with the radial path at finite cutoff. The Bochner construction here keeps the exact
average in the original Gaussian Hilbert space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Every continuous Banach-valued function is integrable against a fixed circle. -/
theorem integrable_continuous_circleMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℂ) (r : ℝ) (F : ℂ → E) (hF : Continuous F) :
    Integrable F (circleMeasure x r) := by
  unfold circleMeasure
  have hi : Integrable F
      ((volume.restrict (Ioc 0 (2 * Real.pi))).map (circleMap x (Real.exp (-r)))) := by
    rw [integrable_map_measure hF.aestronglyMeasurable
      (measurable_circleMap x _).aemeasurable]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp
      ((hF.comp (continuous_circleMap x _)).intervalIntegrable 0 (2 * Real.pi))
  exact hi.smul_measure (by simp)

/-- Clamp logarithmic radius below a positive distance from the origin. On a circle which
stays above that distance this is exactly the ordinary logarithmic radius. -/
noncomputable def clampedLogRadius (ρ : ℝ) (z : ℂ) : ℝ :=
  -Real.log (max ρ ‖z‖)

/-- The clamped radius is continuous on the whole plane. -/
theorem continuous_clampedLogRadius (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (clampedLogRadius ρ) := by
  exact ((continuous_const.max continuous_norm).log
    (fun z => (hρ.trans_le (le_max_left ρ ‖z‖)).ne')).neg

/-- Above the clamping radius, the coordinate is the genuine logarithmic radius. -/
theorem clampedLogRadius_eq (ρ : ℝ) (z : ℂ) (hz : ρ ≤ ‖z‖) :
    clampedLogRadius ρ z = -Real.log ‖z‖ := by
  rw [clampedLogRadius, max_eq_right hz]

/-- Circle radii bounded away from the origin also bound every point of the circle away
from the origin. This bound is valid without any angular coordinate choice. -/
theorem circle_norm_lower_ae (x : ℂ) (r ρ : ℝ) (hρ : ρ ≤ ‖x‖ - Real.exp (-r)) :
    ∀ᵐ z ∂circleMeasure x r, ρ ≤ ‖z‖ := by
  filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
  have h := norm_sub_norm_le x z
  rw [norm_sub_rev x z, hz] at h
  linarith

/-- The radial coordinate map is continuous in the original Gaussian L² carrier. -/
theorem continuous_clampedRadialCircleL2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (fun z : ℂ => circleAverageL2 hc (0, clampedLogRadius ρ z)) := by
  exact (continuous_circleAverageL2 P X Xc hX hc).comp
    (continuous_const.prodMk (continuous_clampedLogRadius ρ hρ))

/-- The actual circle average of radial variables in L². The clamp is inactive whenever
the circle lies outside its radius. -/
noncomputable def originCircleRadialL2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (ρ : ℝ) (x : ℂ) (r : ℝ) : Lp ℝ 2 P :=
  ∫ z : ℂ, circleAverageL2 hc (0, clampedLogRadius ρ z) ∂circleMeasure x r

/-- Integrability is proved in the Hilbert carrier before choosing scalar representatives. -/
theorem integrable_clampedRadialCircleL2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    Integrable (fun z : ℂ => circleAverageL2 hc (0, clampedLogRadius ρ z))
      (circleMeasure x r) :=
  integrable_continuous_circleMeasure x r _
    (continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ)

/-- The circle radial average belongs to the same closed Gaussian space as the field. -/
theorem originCircleRadialL2_mem_gaussianHilbertSpan
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    originCircleRadialL2 hc ρ x r ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
  let _ := hX.1
  let _ := circleMeasure_isProbability x r
  exact integral_mem_gaussianHilbertSpan (circleMeasure x r) _ _
    (integrable_clampedRadialCircleL2 P X Xc hX hc ρ hρ x r)
    (ae_of_all _ fun z => mem_gaussianHilbertSpan _ (Sum.inl (0, clampedLogRadius ρ z)))

/-- Averaging the centered radial variables keeps zero mean. -/
theorem originCircleRadialL2_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    (∫ ω, originCircleRadialL2 hc ρ x r ω ∂P) = 0 := by
  let _ := hX.1
  rw [originCircleRadialL2, integral_mean_L2_integral _ _
    (integrable_clampedRadialCircleL2 P X Xc hX hc ρ hρ x r)]
  simp_rw [circleAverageL2_integral_eq_zero P X Xc hX hc]
  simp only [integral_zero]


/-- Covariance of the circle radial average is the average of the radial covariances. -/
theorem originCircleRadialL2_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) (V : Lp ℝ 2 P) :
    covariance (originCircleRadialL2 hc ρ x r) V P =
      ∫ z : ℂ, covariance (circleAverageL2 hc (0, clampedLogRadius ρ z)) V P
        ∂circleMeasure x r := by
  let _ := hX.1
  exact covariance_L2_integral_left _ _
    (integrable_clampedRadialCircleL2 P X Xc hX hc ρ hρ x r) V
    (fun z => circleAverageL2_integral_eq_zero P X Xc hX hc _)

/-- The Hilbert average agrees with the literal jointly measurable radial circle integral. -/
theorem originCircleRadialL2_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    (⇑(originCircleRadialL2 hc ρ x r)) =ᵐ[P]
      fun ω => ∫ z : ℂ, Xc ω 0 (clampedLogRadius ρ z) ∂circleMeasure x r := by
  let _ := hX.1
  let _ := circleMeasure_isProbability x r
  apply L2_integral_ae_eq_integral _ _
    (integrable_clampedRadialCircleL2 P X Xc hX hc ρ hρ x r)
  · exact (hm.comp (measurable_snd.prodMk (measurable_const.prodMk
      ((continuous_clampedLogRadius ρ hρ).measurable.comp measurable_fst)))).aestronglyMeasurable
  · intro z
    exact circleAverageL2_ae_eq hc _

/-- The clamp does not change the literal integral on any circle above its radius. -/
theorem originCircleRadialL2_ae_eq_unclamped
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ)
    (hbound : ρ ≤ ‖x‖ - Real.exp (-r)) :
    (⇑(originCircleRadialL2 hc ρ x r)) =ᵐ[P]
      fun ω => ∫ z : ℂ, Xc ω 0 (-Real.log ‖z‖) ∂circleMeasure x r := by
  filter_upwards [originCircleRadialL2_ae_eq P X Xc hX hc hm ρ hρ x r] with ω hω
  rw [hω]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae x r ρ hbound] with z hz
  rw [clampedLogRadius_eq ρ z hz]

/-- A circle cutoff pairs with every origin circle through the radial potential. -/
theorem offCenterCircle_origin_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r s : ℝ)
    (hbound : ρ ≤ ‖x‖ - Real.exp (-r)) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω 0 s) P =
      ∫ z : ℂ, originRadialCovariance s z ∂circleMeasure x r := by
  rw [circleAverage_covariance_integral P X Xc hX hc]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae x r ρ hbound] with z hz
  exact origin_circleKernelPotential_eq s z (norm_pos_iff.mp (hρ.trans_le hz))

/-- The averaged radial part has exactly the same covariance with the full radial family.
This is the cancellation needed for a finite-cutoff independence statement. -/
theorem originCircleRadialL2_origin_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r s : ℝ)
    (hbound : ρ ≤ ‖x‖ - Real.exp (-r)) :
    covariance (originCircleRadialL2 hc ρ x r) (circleAverageL2 hc (0, s)) P =
      ∫ z : ℂ, originRadialCovariance s z ∂circleMeasure x r := by
  rw [originCircleRadialL2_covariance P X Xc hX hc ρ hρ x r]
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae x r ρ hbound] with z hz
  rw [clampedLogRadius_eq ρ z hz, covariance_comm,
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _)]
  exact origin_circle_radial_covariance X Xc hX hc s z

/-- The exact orthogonal lateral part of a circle cutoff, in the Gaussian Hilbert carrier. -/
noncomputable def originCircleLateralL2
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (ρ : ℝ) (x : ℂ) (r : ℝ) : Lp ℝ 2 P :=
  circleAverageL2 hc (x, r) - originCircleRadialL2 hc ρ x r

/-- Subtracting the radial average keeps the cutoff inside the same Gaussian linear space. -/
theorem originCircleLateralL2_mem_gaussianHilbertSpan
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    originCircleLateralL2 hc ρ x r ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
  let _ := hX.1
  exact Submodule.sub_mem _ (mem_gaussianHilbertSpan _ (Sum.inl (x, r)))
    (originCircleRadialL2_mem_gaussianHilbertSpan P X Xc hX hc ρ hρ x r)

/-- The orthogonal cutoff is centered. -/
theorem originCircleLateralL2_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    (∫ ω, originCircleLateralL2 hc ρ x r ω ∂P) = 0 := by
  let _ := hX.1
  rw [originCircleLateralL2, integral_congr_ae (Lp.coeFn_sub _ _)]
  change (∫ ω, circleAverageL2 hc (x, r) ω - originCircleRadialL2 hc ρ x r ω ∂P) = 0
  rw [integral_sub ((Lp.memLp _).integrable (by norm_num))
      ((Lp.memLp _).integrable (by norm_num)),
    circleAverageL2_integral_eq_zero P X Xc hX hc,
    originCircleRadialL2_integral_eq_zero P X Xc hX hc ρ hρ x r, sub_self]

/-- Orthogonal circle cutoffs have zero covariance with every radial time. -/
theorem originCircleLateralL2_origin_covariance_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r s : ℝ)
    (hbound : ρ ≤ ‖x‖ - Real.exp (-r)) :
    covariance (originCircleLateralL2 hc ρ x r) (circleAverageL2 hc (0, s)) P = 0 := by
  let _ := hX.1
  rw [originCircleLateralL2, covariance_congr_ae (Lp.coeFn_sub _ _)
    (EventuallyEq.rfl : (⇑(circleAverageL2 hc (0, s))) =ᵐ[P] _),
    covariance_sub_left (Lp.memLp _) (Lp.memLp _) (Lp.memLp _),
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _),
    offCenterCircle_origin_covariance P X Xc hX hc ρ hρ x r s hbound,
    originCircleRadialL2_origin_covariance P X Xc hX hc ρ hρ x r s hbound, sub_self]

/-- A circle cutoff with a positive lower radius for its distance to the origin. -/
abbrev OriginCircleCutoff := {p : ℝ × (ℂ × ℝ) //
  0 < p.1 ∧ p.1 ≤ ‖p.2.1‖ - Real.exp (-p.2.2)}

/-- Pack the full radial family and every orthogonal circle cutoff into one L² family. -/
noncomputable def originRadialLateralCircleL2Family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) : ℝ ⊕ OriginCircleCutoff → Lp ℝ 2 P :=
  Sum.elim (fun s => circleAverageL2 hc (0, s))
    (fun p => originCircleLateralL2 hc p.val.1 p.val.2.1 p.val.2.2)

/-- Every member of the packed family lies in the original closed Gaussian space. -/
theorem originRadialLateralCircleL2Family_mem_gaussianHilbertSpan
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (j : ℝ ⊕ OriginCircleCutoff) :
    originRadialLateralCircleL2Family hc j ∈
      gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
  let _ := hX.1
  cases j with
  | inl s => exact mem_gaussianHilbertSpan _ (Sum.inl (0, s))
  | inr p =>
    exact originCircleLateralL2_mem_gaussianHilbertSpan
      P X Xc hX hc p.val.1 p.property.1 p.val.2.1 p.val.2.2

/-- The complete radial/circle-cutoff family is jointly Gaussian. -/
theorem originRadialLateralCircleL2Family_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsGaussianProcess (fun j => ⇑(originRadialLateralCircleL2Family hc j)) P := by
  let _ := hX.1
  exact isGaussianProcess_of_mem_gaussianHilbertSpan
    (gffStructureL2Family_isGaussianProcess X Xc hX hc) _
    (originRadialLateralCircleL2Family_mem_gaussianHilbertSpan P X Xc hX hc)


/-- Orthogonal circle cutoffs form a centered Gaussian family at every finite collection. -/
theorem originCircleLateralL2_centeredJointlyGaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (n : ℕ) (p : Fin n → OriginCircleCutoff) :
    IsCenteredJointlyGaussian P
      (fun ω i => originCircleLateralL2 hc (p i).val.1 (p i).val.2.1 (p i).val.2.2 ω) := by
  have hproc := (originRadialLateralCircleL2Family_isGaussianProcess P X Xc hX hc).comp_right
    (fun i : Fin n => Sum.inr (p i))
  exact centeredJointlyGaussian_of_isGaussianProcess P _ hproc
    (fun i => originCircleLateralL2_integral_eq_zero P X Xc hX hc
      (p i).val.1 (p i).property.1 (p i).val.2.1 (p i).val.2.2)

/-- The entire orthogonal circle-cutoff coordinate family is independent of the entire
radial coordinate family, with all valid circles and all radial times included. -/
theorem originCircleLateralL2_radial_indepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IndepFun (fun ω => fun s : ℝ => circleAverageL2 hc (0, s) ω)
      (fun ω => fun p : OriginCircleCutoff =>
        originCircleLateralL2 hc p.val.1 p.val.2.1 p.val.2.2 ω) P := by
  have hproc : IsGaussianProcess
      (Sum.elim (fun s => ⇑(circleAverageL2 hc (0, s)))
        (fun p : OriginCircleCutoff => ⇑(originCircleLateralL2 hc p.val.1 p.val.2.1 p.val.2.2))) P := by
    convert originRadialLateralCircleL2Family_isGaussianProcess P X Xc hX hc using 1
    funext j
    cases j <;> rfl
  apply hproc.indepFun_of_covariance_eq_zero
  · intro s
    exact (Lp.memLp _).aemeasurable
  · intro p
    exact (Lp.memLp _).aemeasurable
  · intro s p
    rw [covariance_comm]
    exact originCircleLateralL2_origin_covariance_zero
      P X Xc hX hc p.val.1 p.property.1 p.val.2.1 p.val.2.2 s p.property.2


/-- Scalar representatives of the cutoff have the exact samplewise subtraction formula. -/
theorem originCircleLateralL2_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ)
    (hbound : ρ ≤ ‖x‖ - Real.exp (-r)) :
    (⇑(originCircleLateralL2 hc ρ x r)) =ᵐ[P]
      fun ω => Xc ω x r - ∫ z : ℂ, Xc ω 0 (-Real.log ‖z‖) ∂circleMeasure x r := by
  filter_upwards [Lp.coeFn_sub (circleAverageL2 hc (x, r)) (originCircleRadialL2 hc ρ x r),
    circleAverageL2_ae_eq hc (x, r),
    originCircleRadialL2_ae_eq_unclamped P X Xc hX hc hm ρ hρ x r hbound]
    with ω hsub hcircle hrad
  rw [originCircleLateralL2, hsub]
  change circleAverageL2 hc (x, r) ω - originCircleRadialL2 hc ρ x r ω = _
  rw [hcircle, hrad]

/-- Once both clamps lie below the circle's distance to the origin, the Hilbert radial
average is independent of the chosen clamp. -/
theorem originCircleRadialL2_eq_of_lower_radii
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (x : ℂ) (r ρ ρ' : ℝ)
    (hρ : ρ ≤ ‖x‖ - Real.exp (-r)) (hρ' : ρ' ≤ ‖x‖ - Real.exp (-r)) :
    originCircleRadialL2 hc ρ x r = originCircleRadialL2 hc ρ' x r := by
  unfold originCircleRadialL2
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae x r ρ hρ,
    circle_norm_lower_ae x r ρ' hρ'] with z hz hz'
  rw [clampedLogRadius_eq ρ z hz, clampedLogRadius_eq ρ' z hz']


/-- Orthogonality to all radial times extends to every averaged radial circle. -/
theorem originCircleLateralL2_radialCircle_covariance_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (x y : ℂ) (r t : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) :
    covariance (originCircleLateralL2 hc ρ x r) (originCircleRadialL2 hc σ y t) P = 0 := by
  rw [covariance_comm, originCircleRadialL2_covariance P X Xc hX hc σ hσ y t]
  have hz : (fun z : ℂ => covariance (circleAverageL2 hc (0, clampedLogRadius σ z))
      (originCircleLateralL2 hc ρ x r) P) = fun _ => (0 : ℝ) := by
    funext z
    rw [covariance_comm,
      originCircleLateralL2_origin_covariance_zero P X Xc hX hc ρ hρ x r _ hx]
  rw [hz, integral_zero]

/-- Subtracting the exact radial projection removes its mixed covariance from two circle
cutoffs. This identity is valid before taking any regularization limit. -/
theorem originCircleLateralL2_covariance_expansion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (x y : ℂ) (r t : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) (hy : σ ≤ ‖y‖ - Real.exp (-t)) :
    covariance (originCircleLateralL2 hc ρ x r) (originCircleLateralL2 hc σ y t) P =
      covariance (circleAverageL2 hc (x, r)) (circleAverageL2 hc (y, t)) P -
        covariance (originCircleRadialL2 hc ρ x r) (originCircleRadialL2 hc σ y t) P := by
  let _ := hX.1
  let Cx := circleAverageL2 hc (x, r)
  let Cy := circleAverageL2 hc (y, t)
  let Rx := originCircleRadialL2 hc ρ x r
  let Ry := originCircleRadialL2 hc σ y t
  have h1 := originCircleLateralL2_radialCircle_covariance_zero
    P X Xc hX hc ρ σ hρ hσ x y r t hx
  have h2 := originCircleLateralL2_radialCircle_covariance_zero
    P X Xc hX hc σ ρ hσ hρ y x t r hy
  change covariance (⇑(Cx - Rx)) Ry P = 0 at h1
  change covariance (⇑(Cy - Ry)) Rx P = 0 at h2
  rw [covariance_congr_ae (Lp.coeFn_sub Cx Rx) (EventuallyEq.rfl : (⇑Ry) =ᵐ[P] _),
    covariance_sub_left (Lp.memLp Cx) (Lp.memLp Rx) (Lp.memLp Ry)] at h1
  rw [covariance_congr_ae (Lp.coeFn_sub Cy Ry) (EventuallyEq.rfl : (⇑Rx) =ᵐ[P] _),
    covariance_sub_left (Lp.memLp Cy) (Lp.memLp Ry) (Lp.memLp Rx),
    covariance_comm Ry Rx, covariance_comm Cy Rx] at h2
  change covariance (⇑(Cx - Rx)) (⇑(Cy - Ry)) P = _
  rw [covariance_congr_ae (Lp.coeFn_sub Cx Rx) (Lp.coeFn_sub Cy Ry),
    covariance_sub_sub (Lp.memLp Cx) (Lp.memLp Rx) (Lp.memLp Cy) (Lp.memLp Ry)]
  linarith only [h1, h2]

/-- The second-moment variance splits into radial and lateral variances exactly. -/
theorem originCircleLateralL2_variance_split
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) :
    gaussianVariance P (circleAverageL2 hc (x, r)) =
      gaussianVariance P (originCircleLateralL2 hc ρ x r) +
        gaussianVariance P (originCircleRadialL2 hc ρ x r) := by
  have h := originCircleLateralL2_covariance_expansion
    P X Xc hX hc ρ ρ hρ hρ x x r r hx hx
  simp only [ProbabilityTheory.covariance,
    circleAverageL2_integral_eq_zero P X Xc hX hc,
    originCircleLateralL2_integral_eq_zero P X Xc hX hc ρ hρ x r,
    originCircleRadialL2_integral_eq_zero P X Xc hX hc ρ hρ x r,
    sub_zero] at h
  unfold gaussianVariance gaussianCovariance
  linarith only [h]

/-- The Wick exponential of a circle cutoff factors into its independent lateral and
radial Wick exponentials. There is no covariance error at finite cutoff. -/
theorem originCircleLateralL2_wick_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r γ : ℝ)
    (hx : ρ ≤ ‖x‖ - Real.exp (-r)) :
    ∀ᵐ ω ∂P,
      Real.exp (γ * circleAverageL2 hc (x, r) ω -
        γ ^ 2 / 2 * gaussianVariance P (circleAverageL2 hc (x, r))) =
      Real.exp (γ * originCircleLateralL2 hc ρ x r ω -
        γ ^ 2 / 2 * gaussianVariance P (originCircleLateralL2 hc ρ x r)) *
      Real.exp (γ * originCircleRadialL2 hc ρ x r ω -
        γ ^ 2 / 2 * gaussianVariance P (originCircleRadialL2 hc ρ x r)) := by
  filter_upwards [Lp.coeFn_sub (circleAverageL2 hc (x, r))
    (originCircleRadialL2 hc ρ x r)] with ω hω
  have hsub : originCircleLateralL2 hc ρ x r ω =
      circleAverageL2 hc (x, r) ω - originCircleRadialL2 hc ρ x r ω := hω
  rw [← Real.exp_add, hsub,
    originCircleLateralL2_variance_split P X Xc hX hc ρ hρ x r hx]
  congr 1
  ring

/-- Shrinking probability circles recover every continuous Banach-valued function at the
center. The estimate uses continuity and the exact support radius, without a coordinate chart. -/
theorem tendsto_integral_circleMeasure_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (F : ℂ → E) (hF : Continuous F) (x : ℂ) :
    Tendsto (fun r : ℝ => ∫ z, F z ∂circleMeasure x r) atTop (𝓝 (F x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := (Metric.continuousAt_iff.mp hF.continuousAt) (ε / 2)
    (half_pos hε)
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((tendsto_order.1 Real.tendsto_exp_neg_atTop_nhds_zero).2 δ hδ)
  refine ⟨R, fun r hr => ?_⟩
  let _ := circleMeasure_isProbability x r
  have hb : ∀ᵐ z ∂circleMeasure x r, ‖F z - F x‖ ≤ ε / 2 := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    rw [← dist_eq_norm]
    exact (hclose (by rw [dist_eq_norm, hz]; exact hR r hr)).le
  have hi := integrable_continuous_circleMeasure x r F hF
  have hnorm := norm_integral_le_of_norm_le_const hb
  rw [show (circleMeasure x r).real univ = 1 by simp, mul_one] at hnorm
  rw [dist_eq_norm]
  have heq : (∫ z, F z ∂circleMeasure x r) - F x =
      ∫ z, F z - F x ∂circleMeasure x r := by
    rw [integral_sub hi (integrable_const (F x)), integral_const]
    simp only [probReal_univ, one_smul]
  rw [heq]
  exact hnorm.trans_lt (half_lt_self hε)

/-- At any fixed nonzero center the projected radial cutoff converges in the Gaussian
Hilbert space to the actual origin circle variable at its logarithmic radius. -/
theorem tendsto_originCircleRadialL2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (hx : ρ ≤ ‖x‖) :
    Tendsto (fun r : ℝ => originCircleRadialL2 hc ρ x r) atTop
      (𝓝 (circleAverageL2 hc (0, -Real.log ‖x‖))) := by
  have h := tendsto_integral_circleMeasure_continuous
    (fun z => circleAverageL2 hc (0, clampedLogRadius ρ z))
    (continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ) x
  rw [clampedLogRadius_eq ρ x hx] at h
  exact h

/-- The radial variances and mixed covariances converge along the same actual cutoff
family, so the deterministic Wick correction also has the correct radial limit. -/
theorem tendsto_originCircleRadialL2_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ) (x y : ℂ)
    (hx : ρ ≤ ‖x‖) (hy : σ ≤ ‖y‖) :
    Tendsto (fun r : ℝ => covariance (originCircleRadialL2 hc ρ x r)
      (originCircleRadialL2 hc σ y r) P) atTop
      (𝓝 (covariance (circleAverageL2 hc (0, -Real.log ‖x‖))
        (circleAverageL2 hc (0, -Real.log ‖y‖)) P)) := by
  let _ := hX.1
  simp_rw [covariance_L2_eq,
    originCircleRadialL2_integral_eq_zero P X Xc hX hc ρ hρ x,
    originCircleRadialL2_integral_eq_zero P X Xc hX hc σ hσ y,
    circleAverageL2_integral_eq_zero P X Xc hX hc, zero_mul, sub_zero]
  exact (tendsto_originCircleRadialL2 P X Xc hX hc ρ hρ x hx).inner
    (tendsto_originCircleRadialL2 P X Xc hX hc σ hσ y hy)

/-- The literal orthogonal cutoff on the raw probability space, indexed by circles which
avoid the origin. Its definition uses the actual radial circle integral. -/
noncomputable def originCircleLateralCutoff
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (p : OriginCircleCutoff) (ω : Ω) : ℝ :=
  Xc ω p.val.2.1 p.val.2.2 -
    ∫ z : ℂ, Xc ω 0 (-Real.log ‖z‖) ∂circleMeasure p.val.2.1 p.val.2.2

/-- The scalar cutoff is an almost-everywhere representative of its Hilbert projection. -/
theorem originCircleLateralCutoff_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (p : OriginCircleCutoff) :
    (⇑(originCircleLateralL2 hc p.val.1 p.val.2.1 p.val.2.2)) =ᵐ[P]
      originCircleLateralCutoff Xc p :=
  originCircleLateralL2_ae_eq P X Xc hX hc hm p.val.1 p.property.1
    p.val.2.1 p.val.2.2 p.property.2

/-- All actual radial coordinates and all actual orthogonal cutoffs are jointly Gaussian
on the supplied raw space. Only coordinatewise modification is used here. -/
theorem originRadialLateralCutoff_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) :
    IsGaussianProcess (Sum.elim (fun s ω => Xc ω 0 s)
      (originCircleLateralCutoff Xc)) P := by
  apply (originRadialLateralCircleL2Family_isGaussianProcess P X Xc hX hc).congr
  intro j
  cases j with
  | inl s => exact circleAverageL2_ae_eq hc (0, s)
  | inr p => exact originCircleLateralCutoff_ae_eq P X Xc hX hc hm p

/-- The literal cutoff family is independent of the entire raw radial family. No common
null event over uncountably many Hilbert representatives is asserted. -/
theorem originCircleLateralCutoff_radial_indepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) :
    IndepFun (fun ω => fun s : ℝ => Xc ω 0 s)
      (fun ω => fun p : OriginCircleCutoff => originCircleLateralCutoff Xc p ω) P := by
  apply (originRadialLateralCutoff_isGaussianProcess P X Xc hX hc hm).indepFun_of_covariance_eq_zero
  · intro s
    exact (hc.2.1 0 s).aemeasurable
  · intro p
    exact (Lp.memLp _).aemeasurable.congr
      (originCircleLateralCutoff_ae_eq P X Xc hX hc hm p)
  · intro s p
    rw [← covariance_congr_ae (circleAverageL2_ae_eq hc (0, s))
      (originCircleLateralCutoff_ae_eq P X Xc hX hc hm p), covariance_comm]
    exact originCircleLateralL2_origin_covariance_zero P X Xc hX hc
      p.val.1 p.property.1 p.val.2.1 p.val.2.2 s p.property.2

/-- The same independence holds with the actual continuous two-sided radial path as the
left carrier, using its evaluation-generated Borel sigma algebra. -/
theorem originRadialPath_circleLateralCutoff_indepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IndepFun (originRadialPath Xc)
      (fun ω => fun p : OriginCircleCutoff => originCircleLateralCutoff Xc p ω) P := by
  have hcoords : IndepFun (fun ω => fun s : ℝ => originRadialPath Xc ω s)
      (fun ω => fun p : OriginCircleCutoff => originCircleLateralCutoff Xc p ω) P := by
    apply (originCircleLateralCutoff_radial_indepFun P X Xc hX hc hm).congr
      _ EventuallyEq.rfl
    filter_upwards [originRadialPath_eval_ae hcont] with ω hω
    exact funext (fun s => (hω s).symm)
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ
  let _ := hDc.to_subtype
  let E : TwoSidedPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval (fun t => ContinuousMap.measurable_eval t.1)
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    exact congrFun (hDd.denseRange_val.equalizer p.continuous q.continuous hpq)
  have hEmb := hmE.measurableEmbedding hinj
  let restrict : (ℝ → ℝ) → (D → ℝ) := fun p t => p t.1
  have hrestrict : Measurable restrict := Measurable.of_eval (fun t => measurable_pi_apply t.1)
  have hi := hcoords.comp hrestrict measurable_id
  change IndepFun (E ∘ originRadialPath Xc)
    (fun ω => fun p : OriginCircleCutoff => originCircleLateralCutoff Xc p ω) P at hi
  rw [IndepFun_iff_Indep, ← MeasurableSpace.comap_comp, hEmb.comap_eq] at hi
  exact (IndepFun_iff_Indep _ _ P).2 hi

/-- The clamped radial circle integral is defined at every center and cutoff parameter,
including circles outside a particular punctured-plane chart. -/
noncomputable def clampedCircleRadialSample
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) (ω : Ω) (x : ℂ) (r : ℝ) : ℝ :=
  ∫ z : ℂ, Xc ω 0 (clampedLogRadius ρ z) ∂circleMeasure x r

/-- Subtract the clamped radial projection on the whole plane. On charts where the circles
avoid the clamping disk, this is the actual lateral cutoff. -/
noncomputable def clampedCircleLateralSample
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) (ω : Ω) (x : ℂ) (r : ℝ) : ℝ :=
  Xc ω x r - clampedCircleRadialSample Xc ρ ω x r

/-- The globally defined scalar regularizer represents its exact L² projection. -/
theorem clampedCircleLateralSample_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) :
    (⇑(originCircleLateralL2 hc ρ x r)) =ᵐ[P]
      fun ω => clampedCircleLateralSample Xc ρ ω x r := by
  filter_upwards [Lp.coeFn_sub (circleAverageL2 hc (x, r)) (originCircleRadialL2 hc ρ x r),
    circleAverageL2_ae_eq hc (x, r),
    originCircleRadialL2_ae_eq P X Xc hX hc hm ρ hρ x r]
    with ω hsub hcircle hrad
  rw [originCircleLateralL2, hsub]
  change circleAverageL2 hc (x, r) ω - originCircleRadialL2 hc ρ x r ω = _
  rw [hcircle, hrad]
  rfl

/-- The global scalar regularizer is a centered jointly Gaussian family at arbitrary
finitely many centers and cutoffs, including centers outside the eventual local chart. -/
theorem clampedCircleLateralSample_centeredJointlyGaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (p : Fin n → ℂ × ℝ) :
    IsCenteredJointlyGaussian P
      (fun ω i => clampedCircleLateralSample Xc ρ ω (p i).1 (p i).2) := by
  let _ := hX.1
  let L : Fin n → Lp ℝ 2 P := fun i => originCircleLateralL2 hc ρ (p i).1 (p i).2
  have hL : IsGaussianProcess (fun i => ⇑(L i)) P :=
    isGaussianProcess_of_mem_gaussianHilbertSpan
      (gffStructureL2Family_isGaussianProcess X Xc hX hc) L
      (fun i => originCircleLateralL2_mem_gaussianHilbertSpan P X Xc hX hc ρ hρ
        (p i).1 (p i).2)
  have hs : IsGaussianProcess (fun i ω => clampedCircleLateralSample Xc ρ ω (p i).1 (p i).2) P :=
    hL.congr (fun i => clampedCircleLateralSample_ae_eq P X Xc hX hc hm ρ hρ (p i).1 (p i).2)
  apply centeredJointlyGaussian_of_isGaussianProcess P _ hs
  intro i
  rw [← integral_congr_ae (clampedCircleLateralSample_ae_eq P X Xc hX hc hm ρ hρ
    (p i).1 (p i).2)]
  exact originCircleLateralL2_integral_eq_zero P X Xc hX hc ρ hρ (p i).1 (p i).2

/-- Joint measurability of the radial circle integral follows by using the same angular
measure for all centers and radii. -/
theorem measurable_clampedCircleRadialSample
    {Ω : Type*} [MeasurableSpace Ω] (Xc : Ω → ℂ → ℝ → ℝ)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (fun p : Ω × (ℂ × ℝ) => clampedCircleRadialSample Xc ρ p.1 p.2.1 p.2.2) := by
  let f : (Ω × (ℂ × ℝ)) × ℝ → ℝ := fun q =>
    Xc q.1.1 0 (clampedLogRadius ρ (circleMap q.1.2.1 (Real.exp (-q.1.2.2)) q.2))
  have hf : Measurable f := by
    change Measurable ((fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2) ∘
      fun q : (Ω × (ℂ × ℝ)) × ℝ =>
        (q.1.1, (0, clampedLogRadius ρ (circleMap q.1.2.1 (Real.exp (-q.1.2.2)) q.2))))
    apply hm.comp
    apply Measurable.prodMk (measurable_fst.comp measurable_fst)
    apply Measurable.prodMk measurable_const
    apply (continuous_clampedLogRadius ρ hρ).measurable.comp
    fun_prop [circleMap]
  have hFi := hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc 0 (2 * Real.pi))) |>.measurable
  have heq : (fun p : Ω × (ℂ × ℝ) => clampedCircleRadialSample Xc ρ p.1 p.2.1 p.2.2) =
      fun p => (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), f (p, θ) := by
    funext p
    rw [clampedCircleRadialSample, integral_circleMeasure_eq_circleAverage]
    · rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
      rfl
    · exact (hm.comp (measurable_const.prodMk (measurable_const.prodMk
        (continuous_clampedLogRadius ρ hρ).measurable)))
  rw [heq]
  exact hFi.const_mul _

/-- The globally defined lateral regularizer is jointly measurable in sample, center and
logarithmic radius, as required by the admissible-GMC construction. -/
theorem measurable_clampedCircleLateralSample
    {Ω : Type*} [MeasurableSpace Ω] (Xc : Ω → ℂ → ℝ → ℝ)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (fun p : Ω × (ℂ × ℝ) => clampedCircleLateralSample Xc ρ p.1 p.2.1 p.2.2) :=
  hm.sub (measurable_clampedCircleRadialSample Xc hm ρ hρ)

/-- A continuous scalar function has a continuous circle integral jointly in center and
logarithmic radius. The fixed angular integral supplies the common compact parameter domain. -/
theorem continuous_circleIntegral_of_continuous (F : ℂ → ℝ) (hF : Continuous F) :
    Continuous (fun p : ℂ × ℝ => ∫ z, F z ∂circleMeasure p.1 p.2) := by
  have hi : Continuous (fun p : ℂ × ℝ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap p.1 (Real.exp (-p.2)) θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    apply hF.comp
    fun_prop [circleMap]
  have heq : (fun p : ℂ × ℝ => ∫ z, F z ∂circleMeasure p.1 p.2) =
      fun p => (2 * Real.pi)⁻¹ *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap p.1 (Real.exp (-p.2)) θ) := by
    funext p
    rw [integral_circleMeasure_eq_circleAverage p.1 p.2 F hF.measurable,
      Real.circleAverage_def]
    rfl
  rw [heq]
  exact hi.const_mul _

/-- Continuity of the actual circle witness yields continuity of the clamped radial
projection in every spatial and cutoff parameter on one common probability-one event. -/
theorem continuous_clampedCircleRadialSample
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ω : Ω)
    (hω : Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    Continuous (fun p : ℂ × ℝ => clampedCircleRadialSample Xc ρ ω p.1 p.2) :=
  continuous_circleIntegral_of_continuous _
    (hω.comp (continuous_const.prodMk (continuous_clampedLogRadius ρ hρ)))

/-- The same common event gives a continuous lateral cutoff family, making its spatial
integrals measurable functionals of a continuous Gaussian process. -/
theorem continuous_clampedCircleLateralSample
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ) (ω : Ω)
    (hω : Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    Continuous (fun p : ℂ × ℝ => clampedCircleLateralSample Xc ρ ω p.1 p.2) :=
  hω.sub (continuous_clampedCircleRadialSample Xc ρ hρ ω hω)


/-- Shrinking circles recover a continuous Banach-valued function uniformly on a compact
set of centers. This is the uniform estimate needed for the local covariance limits. -/
theorem integral_circleMeasure_uniform_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℂ → E) (hF : Continuous F) (K : Set ℂ) (hK : IsCompact K)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, Real.exp (-r) ≤ δ → ∀ x ∈ K,
      ‖(∫ z, F z ∂circleMeasure x r) - F x‖ < η := by
  obtain ⟨S, hS⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let R := max S 0 + 1
  have hUC := (isCompact_closedBall (0 : ℂ) R).uniformContinuousOn_of_continuous
    hF.continuousOn
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC (η / 2) (half_pos hη)
  refine ⟨min (δ / 2) 1, lt_min (half_pos hδ) zero_lt_one, ?_⟩
  intro r hr x hx
  let _ := circleMeasure_isProbability x r
  have hxS : ‖x‖ ≤ max S 0 := (hS (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hxR : x ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hxS.trans (le_add_of_nonneg_right zero_le_one)
  have hb : ∀ᵐ z ∂circleMeasure x r, ‖F z - F x‖ ≤ η / 2 := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    have hzR : z ∈ Metric.closedBall 0 R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
           _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
           _ = ‖x‖ + Real.exp (-r) := by rw [hz, add_comm]
           _ ≤ max S 0 + 1 := add_le_add hxS (hr.trans (min_le_right _ _))
    rw [← dist_eq_norm]
    apply (hclose z hzR x hxR ?_).le
    rw [dist_eq_norm, hz]
    exact (hr.trans (min_le_left _ _)).trans_lt (half_lt_self hδ)
  have hnorm := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one] at hnorm
  have heq : (∫ z, F z ∂circleMeasure x r) - F x =
      ∫ z, F z - F x ∂circleMeasure x r := by
    rw [integral_sub (integrable_continuous_circleMeasure x r F hF) (integrable_const (F x)),
      integral_const]
    simp only [probReal_univ, one_smul]
  rw [heq]
  exact hnorm.trans_lt (half_lt_self hη)

end DOZZ.Proofs
