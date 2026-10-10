/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CircleField
public import DOZZ.GMC.FieldChaosConstantTrick
public import DOZZ.GMC.FieldChaosConstantTrickConcave

/-! # Transfer of cutoff moments between locations

On a bounded chart the circle covariance at two translated pairs of points differs by at most
twice the chart remainder, since both are `log (1 / max ‖x - y‖ e^{-r})` up to that remainder.
The continuum constant trick (convex and concave) therefore compares every real moment of a
weighted cutoff mass on `B(z, ρ)` with the same moment on `B(z₀, ρ)`, at the same cutoff, up to
the explicit factor `exp (γ² C |p² - p| / 2) (1 + R)^{4|p|}`; the last factor accounts for the
reference density `‖x‖₊^{-4}`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The circle field translated by `z` is a jointly measurable centered Gaussian field. -/
theorem circleAverage_translate_isCenteredGaussianField
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) (z : ℂ) :
    IsCenteredGaussianField P (fun ω y => Xc ω (y + z) r) :=
  ⟨(hXc.1 r).comp (measurable_fst.prodMk (measurable_snd.add_const z)),
    fun _ y => circleAverage_finite_family_jointly_gaussian P X hX Xc hXc
      (fun i => (y i + z, r))⟩

/-- The translated weight: the bounded weight times the reference density at the translated
point. -/
noncomputable def translatedWeight (w : ℂ → ℝ≥0) (z : ℂ) (y : ℂ) : ℝ≥0 :=
  w y * (normPlus (y + z) ^ (-4 : ℝ)).toNNReal

theorem measurable_normPlus : Measurable normPlus :=
  measurable_const.max measurable_norm

theorem measurable_translatedWeight (w : ℂ → ℝ≥0) (hw : Measurable w) (z : ℂ) :
    Measurable (translatedWeight w z) := by
  unfold translatedWeight
  have h : Measurable (fun y : ℂ => normPlus (y + z) ^ (-4 : ℝ)) :=
    (measurable_normPlus.comp (measurable_id.add_const z)).pow_const _
  exact hw.mul h.real_toNNReal

theorem one_le_normPlus (x : ℂ) : 1 ≤ normPlus x := le_max_left _ _

theorem normPlus_rpow_neg_four_le_one (x : ℂ) : normPlus x ^ (-4 : ℝ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (one_le_normPlus x) (by norm_num)

theorem translatedWeight_le (w : ℂ → ℝ≥0) (c : ℝ≥0) (hc : ∀ y, w y ≤ c) (z y : ℂ) :
    translatedWeight w z y ≤ c := by
  unfold translatedWeight
  calc w y * (normPlus (y + z) ^ (-4 : ℝ)).toNNReal ≤ c * 1 := by
        gcongr
        · exact hc y
        · exact Real.toNNReal_le_one.mpr (normPlus_rpow_neg_four_le_one _)
    _ = c := mul_one c

/-- A translated weighted cutoff mass is the continuum Wick mass of the translated circle field. -/
theorem translated_cutoff_mass_eq_fieldChaosMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (z : ℂ) (ρ : ℝ) (w : ℂ → ℝ≥0) (hw : Measurable w) (ω : Ω) :
    (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) =
      fieldChaosMass P (fun ω y => Xc ω (y + z) r) (volume.restrict (Metric.ball 0 ρ))
        (translatedWeight w z) γ ω := by
  let _ := hX.1
  set E : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) * normPlus x ^ (-4 : ℝ))
    with hE
  have hEm : Measurable E := by
    have hV : Measurable (fun x : ℂ => ∫ ω', Xc ω' x r ^ 2 ∂P) := by
      have hf : Measurable (fun q : ℂ × Ω => Xc q.2 q.1 r ^ 2) :=
        ((hXc.1 r).comp measurable_swap).pow_const 2
      exact hf.stronglyMeasurable.integral_prod_right.measurable
    have hX1 : Measurable (fun x : ℂ => Xc ω x r) :=
      (hXc.1 r).comp (measurable_const.prodMk measurable_id)
    rw [hE]
    exact ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      ((hX1.const_mul γ).sub (hV.const_mul _))).mul (measurable_normPlus.pow_const _))
  have hball : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
  have hball0 : MeasurableSet (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball.measurableSet
  have hwz : Measurable (fun x : ℂ => (w (x - z) : ℝ≥0∞)) :=
    (hw.comp (measurable_id.sub_const z)).coe_nnreal_ennreal
  -- unfold the cutoff measure as a density against Lebesgue measure
  have hlhs : (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) =
      ∫⁻ x, (Metric.ball z ρ).indicator (fun x => (w (x - z) : ℝ≥0∞) * E x) x := by
    rw [regularizedGMC, restrict_withDensity hball, lintegral_withDensity_eq_lintegral_mul _ hEm hwz,
      ← lintegral_indicator hball]
    have hfun : (E * fun x => (w (x - z) : ℝ≥0∞)) = fun x => (w (x - z) : ℝ≥0∞) * E x := by
      funext x
      exact mul_comm (E x) (w (x - z) : ℝ≥0∞)
    rw [hfun]
  rw [hlhs, ← lintegral_add_right_eq_self _ z, fieldChaosMass, ← lintegral_indicator hball0]
  apply lintegral_congr
  intro y
  have hmem : y + z ∈ Metric.ball z ρ ↔ y ∈ Metric.ball (0 : ℂ) ρ := by
    simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
  by_cases hy : y ∈ Metric.ball (0 : ℂ) ρ
  · rw [Set.indicator_of_mem (hmem.mpr hy), Set.indicator_of_mem hy]
    simp only [hE, add_sub_cancel_right, translatedWeight, ENNReal.coe_mul]
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
      show ((normPlus (y + z) ^ (-4 : ℝ)).toNNReal : ℝ≥0∞) =
        ENNReal.ofReal (normPlus (y + z) ^ (-4 : ℝ)) from rfl]
    ring
  · rw [Set.indicator_of_notMem (fun h => hy (hmem.mp h)), Set.indicator_of_notMem hy]

/-- Multiplying by a positive finite constant commutes with every real power. -/
theorem ennreal_mul_rpow_of_ne_zero_ne_top (a y : ℝ≥0∞) (ha0 : a ≠ 0) (hat : a ≠ ⊤) (z : ℝ) :
    (a * y) ^ z = a ^ z * y ^ z := by
  rw [ENNReal.mul_rpow_eq_ite]
  simp [ha0, hat]

/-- Real powers with nonpositive exponent are antitone on `ℝ≥0∞`. -/
theorem ennreal_rpow_antitone_of_nonpos {u v : ℝ≥0∞} (huv : u ≤ v) {z : ℝ} (hz : z ≤ 0) :
    v ^ z ≤ u ^ z := by
  have h : v ^ z = (v ^ (-z))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
  have h' : u ^ z = (u ^ (-z))⁻¹ := by rw [← ENNReal.rpow_neg, neg_neg]
  rw [h, h']
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow huv (by linarith))

/-- Two-sided comparison up to a factor `a ≥ 1` transfers to every real power, with factor
`a ^ |p|`. -/
theorem ennreal_rpow_le_of_two_sided (a x y : ℝ≥0∞) (ha : 1 ≤ a) (hat : a ≠ ⊤)
    (h1 : x ≤ a * y) (h2 : y ≤ a * x) (p : ℝ) : x ^ p ≤ a ^ |p| * y ^ p := by
  have ha0 : a ≠ 0 := (lt_of_lt_of_le zero_lt_one ha).ne'
  rcases le_or_gt 0 p with hp | hp
  · rw [abs_of_nonneg hp, ← ennreal_mul_rpow_of_ne_zero_ne_top a y ha0 hat p]
    exact ENNReal.rpow_le_rpow h1 hp
  · rw [abs_of_neg hp]
    have hax : a ^ p * x ^ p ≤ y ^ p := by
      rw [← ennreal_mul_rpow_of_ne_zero_ne_top a x ha0 hat p]
      exact ennreal_rpow_antitone_of_nonpos h2 hp.le
    have hone : a ^ (-p) * a ^ p = 1 := by
      rw [← ENNReal.rpow_add _ _ ha0 hat, neg_add_cancel, ENNReal.rpow_zero]
    calc x ^ p = a ^ (-p) * (a ^ p * x ^ p) := by rw [← mul_assoc, hone, one_mul]
      _ ≤ a ^ (-p) * y ^ p := by gcongr

/-- The circle covariance at two pairs of points with the same difference differs by at most
twice the chart remainder. -/
theorem translated_covariance_abs_sub_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (R r : ℝ) (hR : 0 ≤ R) (hr : 0 ≤ r)
    (z z₀ y y' : ℂ) (hy : ‖y + z‖ ≤ R) (hy' : ‖y' + z‖ ≤ R) (hy₀ : ‖y + z₀‖ ≤ R)
    (hy₀' : ‖y' + z₀‖ ≤ R) :
    |(∫ ω, Xc ω (y + z) r * Xc ω (y' + z) r ∂P) -
        (∫ ω, Xc ω (y + z₀) r * Xc ω (y' + z₀) r ∂P)| ≤
      2 * (Real.log 3 + 2 * Real.log (1 + R)) := by
  have h1 := circleField_covariance_le_log P X hX Xc hXc R r hR hr _ _ hy hy'
  have h2 := circleField_covariance_ge_log P X hX Xc hXc R r hR hr _ _ hy hy'
  have h3 := circleField_covariance_le_log P X hX Xc hXc R r hR hr _ _ hy₀ hy₀'
  have h4 := circleField_covariance_ge_log P X hX Xc hXc R r hR hr _ _ hy₀ hy₀'
  have hd : (y + z) - (y' + z) = (y + z₀) - (y' + z₀) := by ring
  rw [hd] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- A pointwise weight comparison passes to continuum Wick masses. -/
theorem fieldChaosMass_le_const_mul_of_weight {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (P : Measure Ω) (Φ : Ω → S → ℝ) (ν : Measure S) (h₁ h₂ : S → ℝ≥0)
    (γ : ℝ) (a : ℝ≥0∞) (ha : a ≠ ⊤) (h : ∀ᵐ x ∂ν, (h₁ x : ℝ≥0∞) ≤ a * h₂ x) (ω : Ω) :
    fieldChaosMass P Φ ν h₁ γ ω ≤ a * fieldChaosMass P Φ ν h₂ γ ω := by
  unfold fieldChaosMass
  rw [← lintegral_const_mul' _ _ ha]
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right hx zero_le

theorem normPlus_le_one_add (x : ℂ) {R : ℝ} (hR : 0 ≤ R) (hx : ‖x‖ ≤ R) : normPlus x ≤ 1 + R :=
  max_le (by linarith) (by linarith)

/-- On a bounded chart the translated weights at two centers are comparable. -/
theorem translatedWeight_le_mul (w : ℂ → ℝ≥0) (z z₀ y : ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hy : ‖y + z₀‖ ≤ R) :
    (translatedWeight w z y : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + R) ^ 4) * translatedWeight w z₀ y := by
  unfold translatedWeight
  have hn : 1 ≤ normPlus (y + z₀) := one_le_normPlus _
  have hnR : normPlus (y + z₀) ≤ 1 + R := normPlus_le_one_add _ hR hy
  have hpos : 0 < normPlus (y + z₀) := lt_of_lt_of_le zero_lt_one hn
  have hlow : 1 ≤ (1 + R) ^ 4 * normPlus (y + z₀) ^ (-4 : ℝ) := by
    rw [Real.rpow_neg hpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_left₀ hpos.le hnR 4
  have hz : normPlus (y + z) ^ (-4 : ℝ) ≤ 1 := normPlus_rpow_neg_four_le_one _
  rw [ENNReal.coe_mul, ENNReal.coe_mul, ← mul_assoc, mul_comm (ENNReal.ofReal _) (w y : ℝ≥0∞),
    mul_assoc]
  apply mul_le_mul_of_nonneg_left _ zero_le
  rw [show ((normPlus (y + z) ^ (-4 : ℝ)).toNNReal : ℝ≥0∞) =
      ENNReal.ofReal (normPlus (y + z) ^ (-4 : ℝ)) from rfl,
    show ((normPlus (y + z₀) ^ (-4 : ℝ)).toNNReal : ℝ≥0∞) =
      ENNReal.ofReal (normPlus (y + z₀) ^ (-4 : ℝ)) from rfl,
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (hz.trans hlow)

/-- Location transfer of every real moment of a weighted cutoff mass at a fixed cutoff. -/
theorem cutoff_translate_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (hr : 0 ≤ r)
    (z z₀ : ℂ) (ρ R : ℝ) (hR : 0 ≤ R) (hzR : ‖z‖ + ρ ≤ R) (hz₀R : ‖z₀‖ + ρ ≤ R)
    (w : ℂ → ℝ≥0) (hw : Measurable w) (c : ℝ≥0) (hwc : ∀ y, w y ≤ c) (p : ℝ) :
    ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) ^ p ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
          |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
        ∫⁻ ω, (∫⁻ x in Metric.ball z₀ ρ, (w (x - z₀) : ℝ≥0∞)
          ∂regularizedGMC P Xc γ r ω) ^ p ∂P := by
  let _ := hX.1
  set C : ℝ := 2 * (Real.log 3 + 2 * Real.log (1 + R)) with hCdef
  have hC : 0 ≤ C := by
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have hR1 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
    rw [hCdef]
    positivity
  set ν : Measure ℂ := volume.restrict (Metric.ball 0 ρ) with hνdef
  have hνfin : IsFiniteMeasure ν := by
    rw [hνdef]
    exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  set Φ : Ω → ℂ → ℝ := fun ω y => Xc ω (y + z) r with hΦdef
  set Ψ : Ω → ℂ → ℝ := fun ω y => Xc ω (y + z₀) r with hΨdef
  have hΦ : IsCenteredGaussianField P Φ :=
    circleAverage_translate_isCenteredGaussianField P X hX Xc hXc r z
  have hΨ : IsCenteredGaussianField P Ψ :=
    circleAverage_translate_isCenteredGaussianField P X hX Xc hXc r z₀
  have hmz : ∀ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) =
      fieldChaosMass P Φ ν (translatedWeight w z) γ ω :=
    fun ω => translated_cutoff_mass_eq_fieldChaosMass P X hX Xc hXc γ r z ρ w hw ω
  have hmz₀ : ∀ ω, (∫⁻ x in Metric.ball z₀ ρ, (w (x - z₀) : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) =
      fieldChaosMass P Ψ ν (translatedWeight w z₀) γ ω :=
    fun ω => translated_cutoff_mass_eq_fieldChaosMass P X hX Xc hXc γ r z₀ ρ w hw ω
  simp only [hmz, hmz₀]
  have hh : Measurable (translatedWeight w z) := measurable_translatedWeight w hw z
  have hhb : ∃ c' : ℝ≥0, ∀ y, translatedWeight w z y ≤ c' :=
    ⟨c, fun y => translatedWeight_le w c hwc z y⟩
  -- points of the reference ball stay in the chart after either translation
  have hin : ∀ y : ℂ, ‖y‖ < ρ → ‖y + z‖ ≤ R ∧ ‖y + z₀‖ ≤ R := by
    intro y hy
    exact ⟨(norm_add_le _ _).trans (by linarith), (norm_add_le _ _).trans (by linarith)⟩
  have hball : ∀ᵐ y ∂ν, ‖y‖ < ρ := by
    rw [hνdef]
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
    simpa using hy
  have hcov : ∀ᵐ q ∂ν.prod ν,
      |(∫ ω, Φ ω q.1 * Φ ω q.2 ∂P) - (∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂P)| ≤ C := by
    have hprod : ν.prod ν = (volume.prod volume).restrict
        (Metric.ball (0 : ℂ) ρ ×ˢ Metric.ball (0 : ℂ) ρ) := by
      rw [hνdef, Measure.prod_restrict]
    rw [hprod]
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.prod
      Metric.isOpen_ball.measurableSet)] with q hq
    have h1 := hin q.1 (by simpa using hq.1)
    have h2 := hin q.2 (by simpa using hq.2)
    exact translated_covariance_abs_sub_le P X hX Xc hXc R r hR hr z z₀ q.1 q.2 h1.1 h2.1 h1.2 h2.2
  have hdiag : ∀ᵐ y ∂ν, |(∫ ω, Φ ω y ^ 2 ∂P) - (∫ ω, Ψ ω y ^ 2 ∂P)| ≤ C := by
    filter_upwards [hball] with y hy
    have h1 := hin y hy
    have := translated_covariance_abs_sub_le P X hX Xc hXc R r hR hr z z₀ y y h1.1 h1.1 h1.2 h1.2
    simpa [pow_two] using this
  -- Kahane constant trick with the common weight `translatedWeight w z`
  have hstep1 : (∫⁻ ω, fieldChaosMass P Φ ν (translatedWeight w z) γ ω ^ p ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * |p ^ 2 - p|)) *
        ∫⁻ ω, fieldChaosMass P Ψ ν (translatedWeight w z) γ ω ^ p ∂P := by
    by_cases hp : p ≤ 0 ∨ 1 ≤ p
    · have hk := (kahane_field_constant_trick P P Φ Ψ hΦ hΨ ν (translatedWeight w z) hh hhb γ C
        p hC hp hcov hdiag).2
      have habs : |p ^ 2 - p| = p ^ 2 - p := by
        apply abs_of_nonneg
        rcases hp with hp | hp <;> nlinarith
      rw [habs]
      exact hk
    · push Not at hp
      have hk := (kahane_field_constant_trick_concave P P Φ Ψ hΦ hΨ ν (translatedWeight w z) hh
        hhb γ C p hC ⟨hp.1, hp.2⟩ hcov hdiag).2
      have habs : |p ^ 2 - p| = p - p ^ 2 := by
        rw [abs_of_neg (by nlinarith)]
        ring
      rw [habs]
      exact hk
  -- the weight change from `z` to `z₀`
  have hcmp1 : ∀ ω, fieldChaosMass P Ψ ν (translatedWeight w z) γ ω ≤
      ENNReal.ofReal ((1 + R) ^ 4) * fieldChaosMass P Ψ ν (translatedWeight w z₀) γ ω := by
    intro ω
    refine fieldChaosMass_le_const_mul_of_weight P Ψ ν _ _ γ _ ENNReal.ofReal_ne_top ?_ ω
    filter_upwards [hball] with y hy
    exact translatedWeight_le_mul w z z₀ y hR (hin y hy).2
  have hcmp2 : ∀ ω, fieldChaosMass P Ψ ν (translatedWeight w z₀) γ ω ≤
      ENNReal.ofReal ((1 + R) ^ 4) * fieldChaosMass P Ψ ν (translatedWeight w z) γ ω := by
    intro ω
    refine fieldChaosMass_le_const_mul_of_weight P Ψ ν _ _ γ _ ENNReal.ofReal_ne_top ?_ ω
    filter_upwards [hball] with y hy
    exact translatedWeight_le_mul w z₀ z y hR (hin y hy).1
  have hone : 1 ≤ ENNReal.ofReal ((1 + R) ^ 4) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))
  have hstep2 : (∫⁻ ω, fieldChaosMass P Ψ ν (translatedWeight w z) γ ω ^ p ∂P) ≤
      ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
        ∫⁻ ω, fieldChaosMass P Ψ ν (translatedWeight w z₀) γ ω ^ p ∂P := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p)
      ENNReal.ofReal_ne_top)]
    apply lintegral_mono
    intro ω
    exact ennreal_rpow_le_of_two_sided _ _ _ hone ENNReal.ofReal_ne_top (hcmp1 ω) (hcmp2 ω) p
  calc _ ≤ _ := hstep1
    _ ≤ ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * |p ^ 2 - p|)) *
        (ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
          ∫⁻ ω, fieldChaosMass P Ψ ν (translatedWeight w z₀) γ ω ^ p ∂P) := by gcongr
    _ = _ := by rw [mul_assoc]

end DOZZ.Proofs
