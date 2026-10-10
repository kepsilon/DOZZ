/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.WeightedShell
public import DOZZ.GMC.Moments.SubunitSet

/-!
# Exact local ball scaling and its finite subunit bounds

The affine law on the logarithmic unit chart is an identity at every real order. The
reference moment is retained as an extended value; only actual moment estimates permit
replacing it by a finite constant. The proved subunit input already supplies sharp upper
bounds, with the true Gaussian exponent, uniformly in charge and moment order.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Exact scaling expressed using the radius itself, with the Gaussian exponent
`gmcScaleExponent`. -/
theorem gmc_local_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hR1 : R < 1) (hzr : ‖z‖ + r < 1) (p : ℝ) :
    gmcMassMoment P M (Metric.ball z r) p =
      ENNReal.ofReal ((r / R) ^ gmcScaleExponent γ p) *
        gmcMassMoment P M (Metric.ball 0 R) p := by
  have he : r / R * R = r := div_mul_cancel₀ _ hR.ne'
  have h := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (a := z) (c := r / R) (R := R) (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hR hR1 (by rw [he]; exact hzr) p
  rw [he, ← gmcScaleExponent_eq_polynomial γ p hγ.ne'] at h
  exact h

/-- The ratio law keeps the true radius exponent and puts reference radius dependence in a
strictly positive finite scalar. -/
theorem gmc_local_ball_moment_radius_factor
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hR1 : R < 1) (hzr : ‖z‖ + r < 1) (p : ℝ) :
    gmcMassMoment P M (Metric.ball z r) p =
      ENNReal.ofReal (R ^ (-gmcScaleExponent γ p)) *
        ENNReal.ofReal (r ^ gmcScaleExponent γ p) *
        gmcMassMoment P M (Metric.ball 0 R) p := by
  rw [gmc_local_ball_moment_scale P X hX γ hγ hγ2 M hM z hr hR hrR hR1 hzr p]
  have hf : (r / R) ^ gmcScaleExponent γ p =
      R ^ (-gmcScaleExponent γ p) * r ^ gmcScaleExponent γ p := by
    rw [div_eq_mul_inv, Real.mul_rpow hr.le (inv_pos.mpr hR).le,
      Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]
    exact mul_comm _ _
  rw [hf, ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _)]

/-- Local scaling preserves infinite moments as well as finite ones. -/
theorem gmc_local_ball_moment_finite_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hR1 : R < 1) (hzr : ‖z‖ + r < 1) (p : ℝ) :
    gmcMassMoment P M (Metric.ball z r) p < ⊤ ↔
      gmcMassMoment P M (Metric.ball 0 R) p < ⊤ := by
  have he : r / R * R = r := div_mul_cancel₀ _ hR.ne'
  simpa only [he] using gmc_affine_openBall_moment_finite_iff P X hX γ hγ hγ2 M hM
    (a := z) (c := r / R) (R := R) (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hR hR1 (by rw [he]; exact hzr) p



/-- The subunit Gaussian exponent is nonnegative and bounded by four throughout `(0,2)`. -/
theorem gmcScaleExponent_subunit_bounds {γ p : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ gmcScaleExponent γ p ∧ gmcScaleExponent γ p ≤ 4 := by
  rw [gmcScaleExponent_eq_polynomial γ p hγ.ne']
  have hpp : 0 ≤ p * (1 - p) := mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hpp1 : p * (1 - p) ≤ 1 := by nlinarith only [sq_nonneg p, hp0, hp1]
  have hγsq : γ ^ 2 ≤ 4 := by nlinarith only [hγ, hγ2]
  have hm := mul_le_mul hγsq hpp1 hpp (by norm_num : (0 : ℝ) ≤ 4)
  have hn := mul_nonneg (sq_nonneg γ) hpp
  constructor <;> nlinarith only [hm, hn, hp0, hp1]

/-- A single finite coefficient controls all reference subunit moments and charges. -/
noncomputable def gmcSubunitReferenceConstant : ℝ≥0∞ :=
  1 + gmcReferenceMeasure Set.univ

theorem gmcSubunitReferenceConstant_lt_top : gmcSubunitReferenceConstant < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, gmcReferenceMeasure_univ_ne_top.lt_top⟩

/-- The radius-normalization factor at reference radius one half is uniformly bounded. -/
theorem gmc_half_reference_factor_le_sixteen {γ p : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 / 2 : ℝ) ^ (-gmcScaleExponent γ p) ≤ 16 := by
  have he : (1 / 2 : ℝ) ^ (-gmcScaleExponent γ p) =
      (2 : ℝ) ^ gmcScaleExponent γ p := by
    rw [one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv]
  rw [he]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (gmcScaleExponent_subunit_bounds hγ hγ2 hp0 hp1).2
  exact h.trans_eq (by norm_num)

/-- Sharp local ball upper bounds at every subunit order, with a common coefficient independent
of the charge and the moment order. This uses the actual proved subunit reference estimate. -/
theorem gmc_local_ball_subunit_sharp_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hzr : ‖z‖ + r < 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gmcMassMoment P M (Metric.ball z r) p ≤
      (16 * gmcSubunitReferenceConstant) * ENNReal.ofReal (r ^ gmcScaleExponent γ p) := by
  rw [gmc_local_ball_moment_radius_factor P X hX γ hγ hγ2 M hM z hr
    (by norm_num : (0 : ℝ) < 1 / 2) hrhalf (by norm_num) hzr p]
  have hfactor : ENNReal.ofReal ((1 / 2 : ℝ) ^ (-gmcScaleExponent γ p)) ≤ 16 := by
    exact (ENNReal.ofReal_le_ofReal (gmc_half_reference_factor_le_sixteen hγ hγ2 hp0 hp1)).trans_eq
      (by norm_num)
  have hRef := gmc_mass_subunit_moment_bound P X hX γ M hM (Metric.ball 0 (1 / 2)) hp0 hp1
  have h := mul_le_mul' (mul_le_mul' hfactor (le_refl (ENNReal.ofReal
    (r ^ gmcScaleExponent γ p)))) hRef
  exact h.trans_eq (by unfold gmcSubunitReferenceConstant; ring)


/-- Coarse radii have a common positive lower bound for their subunit scale power. -/
theorem gmc_coarse_subunit_radius_factor {γ p r : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1) :
    1 ≤ 16 * r ^ gmcScaleExponent γ p := by
  have hrp : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hξ := gmcScaleExponent_subunit_bounds hγ hγ2 hp0 hp1
  have h1 : (1 / 2 : ℝ) ^ (4 : ℝ) ≤ r ^ (4 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hr (by norm_num)
  have h2 : r ^ (4 : ℝ) ≤ r ^ gmcScaleExponent γ p :=
    Real.rpow_le_rpow_of_exponent_ge hrp hr1 hξ.2
  have h3 := h1.trans h2
  norm_num only [Real.rpow_natCast, one_div, inv_pow, pow_succ, pow_zero] at h3
  linarith only [h3]

/-- Combining exact fine-scale scaling with the coarse first-moment bound covers every ball
contained in the logarithmic chart, uniformly in all subunit charges and orders. -/
theorem gmc_unit_chart_ball_subunit_sharp_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hzr : ‖z‖ + r < 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gmcMassMoment P M (Metric.ball z r) p ≤
      (16 * gmcSubunitReferenceConstant) * ENNReal.ofReal (r ^ gmcScaleExponent γ p) := by
  by_cases hrhalf : r ≤ 1 / 2
  · exact gmc_local_ball_subunit_sharp_upper P X hX γ hγ hγ2 M hM z hr hrhalf hzr p hp0 hp1
  · have href := gmc_mass_subunit_moment_bound P X hX γ M hM (Metric.ball z r) hp0 hp1
    have hf : (1 : ℝ≥0∞) ≤ 16 * ENNReal.ofReal (r ^ gmcScaleExponent γ p) := by
      have h := ENNReal.ofReal_le_ofReal (gmc_coarse_subunit_radius_factor
        hγ hγ2 hp0 hp1 (le_of_not_ge hrhalf) hr1)
      simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
        ENNReal.ofReal_ofNat] using h
    have hm := mul_le_mul' (le_refl gmcSubunitReferenceConstant) hf
    simp only [mul_one] at hm
    exact href.trans (hm.trans_eq (by unfold gmcSubunitReferenceConstant; ring))

/-- The common subunit reference coefficient is strictly positive as well as finite. -/
theorem gmcSubunitReferenceConstant_pos : 0 < gmcSubunitReferenceConstant := by
  exact zero_lt_one.trans_le (le_add_right le_rfl)

/-- Converting the common extended coefficient to a real number preserves it exactly. -/
noncomputable def gmcSubunitSharpConstant : ℝ := 16 * gmcSubunitReferenceConstant.toReal

theorem gmcSubunitSharpConstant_pos : 0 < gmcSubunitSharpConstant :=
  mul_pos (by norm_num) (ENNReal.toReal_pos gmcSubunitReferenceConstant_pos.ne'
    gmcSubunitReferenceConstant_lt_top.ne)

theorem ofReal_gmcSubunitSharpConstant :
    ENNReal.ofReal gmcSubunitSharpConstant = 16 * gmcSubunitReferenceConstant := by
  rw [gmcSubunitSharpConstant, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ENNReal.ofReal_toReal gmcSubunitReferenceConstant_lt_top.ne]
  norm_num

/-- A real constant independent of the center, charge, and subunit order gives the upper-ball
expression of `DOZZ.equatorGFF_GMC_ball_moment_bound` throughout the exact local chart. -/
theorem gmc_unit_chart_ball_subunit_sharp_upper_real
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hzr : ‖z‖ + r < 1) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    gmcMassMoment P M (Metric.ball z r) p ≤
      ENNReal.ofReal (gmcSubunitSharpConstant * r ^ gmcScaleExponent γ p) := by
  rw [ENNReal.ofReal_mul gmcSubunitSharpConstant_pos.le, ofReal_gmcSubunitSharpConstant]
  exact gmc_unit_chart_ball_subunit_sharp_upper P X hX γ hγ hγ2 M hM z hr hr1 hzr p hp0 hp1


/-- The exact local ball moment is independent of its center while its translated disk stays
inside the unit logarithmic chart. This is equality of actual GMC moments at every real order. -/
theorem gmc_local_ball_moment_center_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z w : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hR1 : R < 1) (hzr : ‖z‖ + r < 1) (hwr : ‖w‖ + r < 1) (p : ℝ) :
    gmcMassMoment P M (Metric.ball z r) p = gmcMassMoment P M (Metric.ball w r) p := by
  rw [gmc_local_ball_moment_scale P X hX γ hγ hγ2 M hM z hr hR hrR hR1 hzr p,
    gmc_local_ball_moment_scale P X hX γ hγ hγ2 M hM w hr hR hrR hR1 hwr p]

/-- On the exact local chart, a positive finite reference moment is equivalent to the full
two-sided scaling estimate at that order. Finiteness of the reference moment is one side of the
equivalence, not an assumption, at every order including the inverse ones. -/
theorem gmc_local_twoSided_ball_scaling_iff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (R p : ℝ) (hR : 0 < R) (hR1 : R < 1) :
    (0 < gmcMassMoment P M (Metric.ball 0 R) p ∧
        gmcMassMoment P M (Metric.ball 0 R) p < ⊤) ↔
      ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ r : ℝ, 0 < r → r ≤ R → ‖z‖ + r < 1 →
        ENNReal.ofReal (C⁻¹ * r ^ gmcScaleExponent γ p) ≤
            gmcMassMoment P M (Metric.ball z r) p ∧
          gmcMassMoment P M (Metric.ball z r) p ≤
            ENNReal.ofReal (C * r ^ gmcScaleExponent γ p) := by
  let B := gmcMassMoment P M (Metric.ball 0 R) p
  let ξ := gmcScaleExponent γ p
  constructor
  · rintro ⟨hBp, hBf⟩
    have hBreal : 0 < B.toReal := ENNReal.toReal_pos hBp.ne' hBf.ne
    let D : ℝ := R ^ (-ξ) * B.toReal
    have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos hR _) hBreal
    let C : ℝ := max D D⁻¹
    have hC : 0 < C := hD.trans_le (le_max_left _ _)
    have hDC : D ≤ C := le_max_left _ _
    have hCD : C⁻¹ ≤ D := by
      have hi := (inv_le_inv₀ hC (inv_pos.mpr hD)).mpr
        (show D⁻¹ ≤ C from le_max_right _ _)
      simpa only [inv_inv] using hi
    refine ⟨C, hC, ?_⟩
    intro z r hr hrR hzr
    have he : gmcMassMoment P M (Metric.ball z r) p = ENNReal.ofReal (D * r ^ ξ) := by
      rw [gmc_local_ball_moment_radius_factor P X hX γ hγ hγ2 M hM z hr hR hrR hR1 hzr p]
      have hB : B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBf.ne).symm
      change ENNReal.ofReal (R ^ (-ξ)) * ENNReal.ofReal (r ^ ξ) * B = _
      rw [hB, ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hR.le _)
          (Real.rpow_nonneg hr.le _))]
      congr 1
      dsimp [D]
      ring
    rw [he]
    exact ⟨ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCD
        (Real.rpow_nonneg hr.le ξ)),
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hDC
        (Real.rpow_nonneg hr.le ξ))⟩
  · rintro ⟨C, hC, hBound⟩
    have hb := hBound 0 R hR le_rfl (by simpa only [norm_zero, zero_add] using hR1)
    have hpref : 0 < ENNReal.ofReal (C⁻¹ * R ^ ξ) :=
      ENNReal.ofReal_pos.mpr (mul_pos (inv_pos.mpr hC) (Real.rpow_pos_of_pos hR ξ))
    exact ⟨hpref.trans_le hb.1, hb.2.trans_lt ENNReal.ofReal_lt_top⟩



/-- A compact center set contained in the logarithmic unit disk has a common positive radius
on which every translated ball remains in that exact chart. -/
theorem gmc_unit_chart_compact_radius (K : Set ℂ) (hK : IsCompact K)
    (hunit : ∀ z ∈ K, ‖z‖ < 1) :
    ∃ R : ℝ, 0 < R ∧ R ≤ 1 / 2 ∧ ∀ z ∈ K, ‖z‖ + R < 1 := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨z₀, hz₀, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    let R : ℝ := min (1 / 2) ((1 - ‖z₀‖) / 2)
    have hR : 0 < R := lt_min (by norm_num) (by linarith [hunit z₀ hz₀])
    refine ⟨R, hR, min_le_left _ _, ?_⟩
    intro z hz
    have hm := hmax hz
    change ‖z‖ ≤ ‖z₀‖ at hm
    have hRle : R ≤ (1 - ‖z₀‖) / 2 := min_le_right _ _
    linarith [hunit z₀ hz₀]
  · refine ⟨1 / 2, by norm_num, le_rfl, ?_⟩
    intro z hz
    exact (hne ⟨z, hz⟩).elim





end DOZZ.Proofs
