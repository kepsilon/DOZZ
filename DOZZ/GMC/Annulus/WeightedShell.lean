/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.PositiveExponent
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.FieldChaosMultiNegativePower

/-!
# Weighted annulus comparisons

An annulus excludes its center, so its radial weight is bounded above and below at every
real insertion exponent. The same deterministic comparison must reverse when taking a
negative moment. The Gaussian scale exponent retains the actual moment order throughout.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The open annulus used by `DOZZ.equatorGFF_GMC_annulus_moment_bound`. -/
def gmcOpenAnnulus (z : ℂ) (ε : ℝ) : Set ℂ :=
  {x | ε < ‖x - z‖ ∧ ‖x - z‖ < 2 * ε}

/-- The insertion-weighted mass on that precise open annulus. -/
noncomputable def gmcWeightedAnnulusMass (μ : Measure ℂ) (z : ℂ) (ε β : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in gmcOpenAnnulus z ε, ENNReal.ofReal (‖x - z‖ ^ β) ∂μ

/-- The fixed-shape distortion factor is finite and at least one. -/
noncomputable def gmcAnnulusWeightFactor (β : ℝ) : ℝ := (2 : ℝ) ^ |β|

theorem gmcAnnulusWeightFactor_pos (β : ℝ) : 0 < gmcAnnulusWeightFactor β :=
  Real.rpow_pos_of_pos (by norm_num) _

theorem one_le_gmcAnnulusWeightFactor (β : ℝ) : 1 ≤ gmcAnnulusWeightFactor β := by
  exact Real.one_le_rpow (by norm_num) (abs_nonneg _)

/-- The annular carrier is Borel for every radius, including empty nonpositive radii. -/
theorem measurableSet_gmcOpenAnnulus (z : ℂ) (ε : ℝ) : MeasurableSet (gmcOpenAnnulus z ε) :=
  (isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet.inter
    (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet



/-- The annulus is contained in its outer open ball. -/
theorem gmcOpenAnnulus_subset_outer_ball (z : ℂ) (ε : ℝ) :
    gmcOpenAnnulus z ε ⊆ Metric.ball z (2 * ε) := by
  intro x hx
  exact Metric.mem_ball.mpr (by simpa only [dist_eq_norm] using hx.2)

/-- Every positive-radius annulus contains a ball with radius one quarter of the annular scale.
The center moves by three halves of that scale along the real direction. -/
theorem gmcOpenAnnulus_contains_ball (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Metric.ball (z + ((3 * ε / 2 : ℝ) : ℂ)) (ε / 4) ⊆ gmcOpenAnnulus z ε := by
  intro x hx
  have hx' : ‖x - (z + ((3 * ε / 2 : ℝ) : ℂ))‖ < ε / 4 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hc : ‖((3 * ε / 2 : ℝ) : ℂ)‖ = 3 * ε / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hupper : ‖x - z‖ ≤ ‖x - (z + ((3 * ε / 2 : ℝ) : ℂ))‖ + 3 * ε / 2 := by
    calc
      ‖x - z‖ = ‖(x - (z + ((3 * ε / 2 : ℝ) : ℂ))) + ((3 * ε / 2 : ℝ) : ℂ)‖ := by
        congr 1
        ring
      _ ≤ _ := by
        simpa only [hc] using norm_add_le
          (x - (z + ((3 * ε / 2 : ℝ) : ℂ))) ((3 * ε / 2 : ℝ) : ℂ)
  have hlower : 3 * ε / 2 ≤ ‖x - z‖ + ‖x - (z + ((3 * ε / 2 : ℝ) : ℂ))‖ := by
    calc
      3 * ε / 2 = ‖((3 * ε / 2 : ℝ) : ℂ)‖ := hc.symm
      _ = ‖(x - z) - (x - (z + ((3 * ε / 2 : ℝ) : ℂ)))‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  exact ⟨by linarith, by linarith⟩

/-- A fixed-shape radial weight is bounded above at its true scale, for either exponent sign. -/
theorem annulus_radial_weight_upper {ε d : ℝ} (hε : 0 < ε)
    (hdlo : ε ≤ d) (hdhi : d ≤ 2 * ε) (β : ℝ) :
    d ^ β ≤ gmcAnnulusWeightFactor β * ε ^ β := by
  by_cases hβ : 0 ≤ β
  · have hpow := Real.rpow_le_rpow (hε.trans_le hdlo).le hdhi hβ
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le] at hpow
    exact hpow.trans_eq (by rw [gmcAnnulusWeightFactor, abs_of_nonneg hβ])
  · have hβn : β ≤ 0 := le_of_not_ge hβ
    have hpow := Real.rpow_le_rpow_of_nonpos hε hdlo hβn
    exact hpow.trans (le_mul_of_one_le_left (Real.rpow_nonneg hε.le β)
      (one_le_gmcAnnulusWeightFactor β))

/-- The matching lower weight bound preserves positivity and supports inverse moments. -/
theorem annulus_radial_weight_lower {ε d : ℝ} (hε : 0 < ε)
    (hdlo : ε ≤ d) (hdhi : d ≤ 2 * ε) (β : ℝ) :
    (gmcAnnulusWeightFactor β)⁻¹ * ε ^ β ≤ d ^ β := by
  have hd : 0 < d := hε.trans_le hdlo
  have h := annulus_radial_weight_upper hε hdlo hdhi (-β)
  have he : gmcAnnulusWeightFactor (-β) = gmcAnnulusWeightFactor β := by
    simp only [gmcAnnulusWeightFactor, abs_neg]
  rw [he, Real.rpow_neg hd.le, Real.rpow_neg hε.le] at h
  have hεp := Real.rpow_pos_of_pos hε β
  have hdp := Real.rpow_pos_of_pos hd β
  have hk := gmcAnnulusWeightFactor_pos β
  have hp : ε ^ β ≤ gmcAnnulusWeightFactor β * d ^ β := by
    have hm := mul_le_mul_of_nonneg_right h (mul_pos hεp hdp).le
    field_simp [hεp.ne', hdp.ne'] at hm
    nlinarith only [hm]
  have hdiv := (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using hp)
  simpa only [div_eq_mul_inv, mul_comm] using hdiv

/-- Integrating the upper weight comparison gives a bound by the unweighted annulus mass. -/
theorem gmcWeightedAnnulusMass_le (μ : Measure ℂ) (z : ℂ) {ε : ℝ}
    (hε : 0 < ε) (β : ℝ) :
    gmcWeightedAnnulusMass μ z ε β ≤
      ENNReal.ofReal (gmcAnnulusWeightFactor β * ε ^ β) * μ (gmcOpenAnnulus z ε) := by
  calc
    _ ≤ ∫⁻ _x in gmcOpenAnnulus z ε,
        ENNReal.ofReal (gmcAnnulusWeightFactor β * ε ^ β) ∂μ := by
      apply setLIntegral_mono' (measurableSet_gmcOpenAnnulus z ε)
      intro x hx
      exact ENNReal.ofReal_le_ofReal (annulus_radial_weight_upper hε hx.1.le hx.2.le β)
    _ = _ := by simp only [lintegral_const, Measure.restrict_apply_univ]

/-- The lower integrated weight comparison remains valid at zero and infinite masses. -/
theorem le_gmcWeightedAnnulusMass (μ : Measure ℂ) (z : ℂ) {ε : ℝ}
    (hε : 0 < ε) (β : ℝ) :
    ENNReal.ofReal ((gmcAnnulusWeightFactor β)⁻¹ * ε ^ β) * μ (gmcOpenAnnulus z ε) ≤
      gmcWeightedAnnulusMass μ z ε β := by
  calc
    _ = ∫⁻ _x in gmcOpenAnnulus z ε,
        ENNReal.ofReal ((gmcAnnulusWeightFactor β)⁻¹ * ε ^ β) ∂μ := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := by
      apply setLIntegral_mono' (measurableSet_gmcOpenAnnulus z ε)
      intro x hx
      exact ENNReal.ofReal_le_ofReal (annulus_radial_weight_lower hε hx.1.le hx.2.le β)



/-- Upper weighted moments are controlled by the outer ball for nonnegative orders. -/
theorem gmcWeightedAnnulusMass_rpow_le_outer_ball
    (μ : Measure ℂ) [IsFiniteMeasure μ] (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    (β p : ℝ) (hp : 0 ≤ p) :
    (gmcWeightedAnnulusMass μ z ε β) ^ p ≤
      ENNReal.ofReal ((gmcAnnulusWeightFactor β * ε ^ β) ^ p) *
        (μ (Metric.ball z (2 * ε))) ^ p := by
  have hu := (gmcWeightedAnnulusMass_le μ z hε β).trans
    (mul_le_mul' le_rfl (measure_mono (gmcOpenAnnulus_subset_outer_ball z ε)))
  have h := ENNReal.rpow_le_rpow hu hp
  rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _) p,
    ENNReal.ofReal_rpow_of_pos (mul_pos (gmcAnnulusWeightFactor_pos β)
      (Real.rpow_pos_of_pos hε β))] at h
  exact h

/-- For nonpositive orders, retaining the annulus's inner ball gives the upper moment bound.
Zero masses retain the extended-power convention instead of being discarded. -/
theorem gmcWeightedAnnulusMass_rpow_le_inner_ball
    (μ : Measure ℂ) [IsFiniteMeasure μ] (z : ℂ) {ε : ℝ} (hε : 0 < ε)
    (β p : ℝ) (hp : p ≤ 0) :
    (gmcWeightedAnnulusMass μ z ε β) ^ p ≤
      ENNReal.ofReal (((gmcAnnulusWeightFactor β)⁻¹ * ε ^ β) ^ p) *
        (μ (Metric.ball (z + ((3 * ε / 2 : ℝ) : ℂ)) (ε / 4))) ^ p := by
  have hl := (mul_le_mul' (le_refl (ENNReal.ofReal ((gmcAnnulusWeightFactor β)⁻¹ * ε ^ β)))
    (measure_mono (gmcOpenAnnulus_contains_ball z hε))).trans
      (le_gmcWeightedAnnulusMass μ z hε β)
  have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hl (neg_nonneg.mpr hp))
  simp only [← ENNReal.rpow_neg, neg_neg] at h
  rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _) p,
    ENNReal.ofReal_rpow_of_pos (mul_pos (inv_pos.mpr (gmcAnnulusWeightFactor_pos β))
      (Real.rpow_pos_of_pos hε β))] at h
  exact h

/-- The positive-order weight prefactor has precisely the insertion exponent `βp`. -/
theorem gmcAnnulus_upper_weight_power (β p : ℝ) {ε : ℝ} (hε : 0 < ε) (hp : 0 ≤ p) :
    (gmcAnnulusWeightFactor β * ε ^ β) ^ p =
      (2 : ℝ) ^ (|β| * |p|) * ε ^ (β * p) := by
  rw [Real.mul_rpow (gmcAnnulusWeightFactor_pos β).le (Real.rpow_nonneg hε.le β),
    gmcAnnulusWeightFactor, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul hε.le, abs_of_nonneg hp]

/-- The inverse-order weight prefactor has the same insertion exponent and a finite shape
constant. The sign reversal changes only that shape constant. -/
theorem gmcAnnulus_lower_weight_power (β p : ℝ) {ε : ℝ} (hε : 0 < ε) (hp : p ≤ 0) :
    ((gmcAnnulusWeightFactor β)⁻¹ * ε ^ β) ^ p =
      (2 : ℝ) ^ (|β| * |p|) * ε ^ (β * p) := by
  rw [Real.mul_rpow (inv_pos.mpr (gmcAnnulusWeightFactor_pos β)).le
      (Real.rpow_nonneg hε.le β),
    gmcAnnulusWeightFactor, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hε.le,
    abs_of_nonpos hp]
  congr 2
  ring

/-- Weighted annulus mass is a measurable functional of the full random-measure carrier. -/
theorem measurable_gmcWeightedAnnulusMass (z : ℂ) (ε β : ℝ) :
    Measurable (fun μ : Measure ℂ => gmcWeightedAnnulusMass μ z ε β) := by
  have hw : Measurable (fun x : ℂ => ENNReal.ofReal (‖x - z‖ ^ β)) := by fun_prop
  have hi := Measure.measurable_lintegral (hw.indicator (measurableSet_gmcOpenAnnulus z ε))
  simpa only [gmcWeightedAnnulusMass, lintegral_indicator (measurableSet_gmcOpenAnnulus z ε)] using hi


/-- The insertion weight contributes `-γαp` to the genuine Gaussian scaling exponent. -/
theorem weightedAnnulus_exponent_eq (γ α p : ℝ) :
    gmcScaleExponent γ p + (-γ * α) * p =
      γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 := by
  unfold gmcScaleExponent
  ring


/-- The positive-order random weighted annulus moment is bounded by the outer-ball moment. -/
theorem gmcWeightedAnnulusMoment_le_outer_ball
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : ∀ ω, IsFiniteMeasure (M ω))
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (β p : ℝ) (hp : 0 ≤ p) :
    (∫⁻ ω, (gmcWeightedAnnulusMass (M ω) z ε β) ^ p ∂P) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (|β| * |p|) * ε ^ (β * p)) *
        gmcMassMoment P M (Metric.ball z (2 * ε)) p := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal ((gmcAnnulusWeightFactor β * ε ^ β) ^ p) *
        (M ω (Metric.ball z (2 * ε))) ^ p ∂P := by
      apply lintegral_mono
      intro ω
      let _ := hM ω
      exact gmcWeightedAnnulusMass_rpow_le_outer_ball (M ω) z hε β p hp
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        gmcAnnulus_upper_weight_power β p hε hp]
      rfl

/-- Negative weighted moments are bounded by the shifted inner-ball inverse moment; no
almost sure positivity hypothesis is needed for this extended-valued inequality. -/
theorem gmcWeightedAnnulusMoment_le_inner_ball
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : ∀ ω, IsFiniteMeasure (M ω))
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (β p : ℝ) (hp : p ≤ 0) :
    (∫⁻ ω, (gmcWeightedAnnulusMass (M ω) z ε β) ^ p ∂P) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (|β| * |p|) * ε ^ (β * p)) *
        gmcMassMoment P M (Metric.ball (z + ((3 * ε / 2 : ℝ) : ℂ)) (ε / 4)) p := by
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (((gmcAnnulusWeightFactor β)⁻¹ * ε ^ β) ^ p) *
        (M ω (Metric.ball (z + ((3 * ε / 2 : ℝ) : ℂ)) (ε / 4))) ^ p ∂P := by
      apply lintegral_mono
      intro ω
      let _ := hM ω
      exact gmcWeightedAnnulusMass_rpow_le_inner_ball (M ω) z hε β p hp
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        gmcAnnulus_lower_weight_power β p hε hp]
      rfl



/-- The true Gaussian scale exponent equals the polynomial in the merged exact moment law. -/
theorem gmcScaleExponent_eq_polynomial (γ p : ℝ) (hγ : γ ≠ 0) :
    gmcScaleExponent γ p = 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
  unfold gmcScaleExponent Q
  field_simp [hγ]







end DOZZ.Proofs
