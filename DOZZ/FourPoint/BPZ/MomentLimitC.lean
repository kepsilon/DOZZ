/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentLimitB

/-! # Ingredients for the limits of the moment fields

* the almost sure properties of the GMC measure used at a regular root `z₀`;
* an integrable lower bound `Y = c M(B)` of the softened mass, uniform in bounded roots and in the
  softening, with `B` a fixed ball far from the roots;
* the real form of the near-root expectation bound, for roots near `z₀`;
* dominated convergence of the expectations of the zeroth moment and of the far parts of the
  moment fields along `(εₙ, zₙ) → (0, z₀)`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- Almost surely the GMC measure has no atoms, integrates the base weight, and integrates the
four-point weight with root `z₀`. -/
theorem bpz_moment_good_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {z₀ : ℂ} (hz0 : z₀ ≠ 0) (hz1 : z₀ ≠ 1) :
    ∀ᵐ ω ∂P, (∀ x, M ω {x} = 0) ∧ Integrable (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) ∧
      Integrable (fun x => Complex.normSq (x - z₀) ^ (γ * χ / 2) *
        bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) := by
  filter_upwards [gmc_noAtoms_ae P X hX γ hγ hγ2 M hM hMm,
    bpz_fourPoint_integrable_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ hz0 hz1,
    bpzMass_lt_top_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ 1 z₀ hz0 hz1] with ω h0 h1 h2
  refine ⟨h0, ?_, ?_⟩
  · have hI1 : Integrable (bpzSoftWeight γ χ α₁ α₂ α₃ 1 z₀) (M ω) := by
      refine ⟨(measurable_bpzSoftWeight 1 z₀).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (bpzSoftWeight_nonneg 1 z₀))]
      exact h2
    refine hI1.mono' measurable_bpzBaseWeight.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (bpzBaseWeight_nonneg x)]
    have h1le : 1 ≤ (Complex.normSq (x - z₀) + 1 ^ 2) ^ (γ * χ / 2) := by
      refine Real.one_le_rpow ?_ (by positivity)
      rw [one_pow]
      exact le_add_of_nonneg_left (Complex.normSq_nonneg _)
    exact le_mul_of_one_le_left (bpzBaseWeight_nonneg x) h1le
  · have e : bpzSoftWeight γ χ α₁ α₂ α₃ 0 z₀ = fun x => Complex.normSq (x - z₀) ^ (γ * χ / 2) *
        bpzBaseWeight γ χ α₁ α₂ α₃ x := by
      funext x
      simp only [bpzSoftWeight, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero]
    rw [← e]
    exact h1

/-- An integrable lower bound of the softened mass, uniform in bounded roots and in the
softening. -/
theorem bpz_farBall_lower {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) {R : ℝ} (hR : 0 ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ (∀ᵐ ω ∂P, 0 < Y ω) ∧ Integrable (fun ω => Y ω ^ (-s)) P ∧
      ∀ ω (z : ℂ), ‖z‖ ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
        Integrable (fun x => (Complex.normSq (x - z) + ε ^ 2) ^ (γ * χ / 2) *
          bpzBaseWeight γ χ α₁ α₂ α₃ x) (M ω) →
        Y ω ≤ bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z := by
  obtain ⟨c, hc, hcle⟩ := bpzMass_ge_farBall (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) R hR
  have hBm : Measurable fun ω => M ω (bpzFarBall R) :=
    (Measure.measurable_coe (bpzFarBall_measurableSet R)).comp hMm
  refine ⟨fun ω => c * (M ω (bpzFarBall R)).toReal, hBm.ennreal_toReal.const_mul c, ?_, ?_, ?_⟩
  · -- positivity: the far ball has positive finite mass almost surely
    have h1 := bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM R 1 zero_le_one
    have hfin := ae_lt_top' (hBm.pow_const (-1 : ℝ)).aemeasurable h1.ne
    filter_upwards [hfin] with ω hω
    have hne : M ω (bpzFarBall R) ≠ 0 := by
      intro h0
      rw [h0, ENNReal.zero_rpow_of_neg (by norm_num)] at hω
      exact lt_irrefl _ hω
    have hlt : M ω (bpzFarBall R) ≠ ⊤ := by
      have := hM.1 ω
      exact measure_ne_top _ _
    exact mul_pos hc (ENNReal.toReal_pos hne hlt)
  · -- integrability of `Y^{-s}`
    have hs1 := bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM R 1 zero_le_one
    have hfin := ae_lt_top' (hBm.pow_const (-1 : ℝ)).aemeasurable hs1.ne
    have hY : Measurable fun ω => (c * (M ω (bpzFarBall R)).toReal) ^ (-s) :=
      (hBm.ennreal_toReal.const_mul c).pow_const _
    refine ⟨hY.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω =>
      Real.rpow_nonneg (mul_nonneg hc.le ENNReal.toReal_nonneg) _)]
    have heq : (fun ω => ENNReal.ofReal ((c * (M ω (bpzFarBall R)).toReal) ^ (-s))) =ᵐ[P]
        fun ω => ENNReal.ofReal (c ^ (-s)) * M ω (bpzFarBall R) ^ (-s) := by
      filter_upwards [hfin] with ω hω
      have hne : M ω (bpzFarBall R) ≠ 0 := by
        intro h0
        rw [h0, ENNReal.zero_rpow_of_neg (by norm_num)] at hω
        exact lt_irrefl _ hω
      have hlt : M ω (bpzFarBall R) ≠ ⊤ := by
        have := hM.1 ω
        exact measure_ne_top _ _
      have ht : 0 < (M ω (bpzFarBall R)).toReal := ENNReal.toReal_pos hne hlt
      rw [Real.mul_rpow hc.le ht.le, ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
        ← ENNReal.ofReal_rpow_of_pos ht, ENNReal.ofReal_toReal hlt]
    rw [lintegral_congr_ae heq, lintegral_const_mul _ (hBm.pow_const _)]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (bpz_farBall_negMoment_lt_top P X hX hγ hγ2 M hM R s hs)
  · intro ω z hz ε hε0 hε1 hint
    have hb : bpzMass γ χ α₁ α₂ α₃ ε (M ω) z ≠ ⊤ := hint.lintegral_lt_top.ne
    have h := ENNReal.toReal_mono hb (hcle z hz ε hε0 hε1 (M ω))
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le, ← bpzSoftI_eq_toReal] at h
    exact h

/-- The real form of the near-root expectation bound, for roots near a regular root `z₀`. -/
theorem bpz_near_real_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z₀ : ℂ} (hz0 : z₀ ≠ 0)
    (hz1 : z₀ ≠ 1) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ → ∀ z : ℂ,
      ‖z - z₀‖ ≤ r / 2 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ β : ℝ, -2 < β →
        Integrable (fun ω => bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃)
          (M ω) z ^ (-(s + 1)) * ∫ x, (if ‖x - z₀‖ < r then bpzBaseWeight γ χ α₁ α₂ α₃ x
            else 0) * ‖x - z‖ ^ β ∂M ω) P ∧
        ∫ ω, bpzSoftMassReal (γ * χ / 2) ε (bpzBaseWeight γ χ α₁ α₂ α₃) (M ω) z ^ (-(s + 1)) *
          ∫ x, (if ‖x - z₀‖ < r then bpzBaseWeight γ χ α₁ α₂ α₃ x else 0) * ‖x - z‖ ^ β ∂M ω
            ∂P ≤ C * (2 * Real.pi * (2 * r) ^ (β + 2) / (β + 2)) ∧
        ∀ᵐ ω ∂P, Integrable (fun x => (if ‖x - z₀‖ < r then bpzBaseWeight γ χ α₁ α₂ α₃ x
          else 0) * ‖x - z‖ ^ β) (M ω) := by
  obtain ⟨r₁, hr₁, C, hC0, hC⟩ := bpz_near_expect_bound (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) P X hX hγ hγ2 M hM (p := s + 1) (by linarith) hz0 hz1
  have h0 : 0 < ‖z₀‖ := norm_pos_iff.mpr hz0
  have h1 : 0 < ‖z₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  refine ⟨min r₁ (min ‖z₀‖ ‖z₀ - 1‖), lt_min hr₁ (lt_min h0 h1), C, hC0,
    fun r hr hrr z hz ε hε0 hε1 β hβ => ?_⟩
  have hrr₁ : r ≤ r₁ := hrr.trans (min_le_left _ _)
  have hr0 : r ≤ ‖z₀‖ := hrr.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr1 : r ≤ ‖z₀ - 1‖ := hrr.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hzne0 : z ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hz
    linarith
  have hzne1 : z ≠ 1 := by
    intro h
    rw [h, norm_sub_rev] at hz
    linarith
  have hB := hC r hr hrr₁ z hz ε hε0 hε1 β hβ
  have hpos : 0 ≤ 2 * Real.pi * (2 * r) ^ (β + 2) / (β + 2) := by
    have : 0 < β + 2 := by linarith
    positivity
  have hf : Measurable fun x => bpzNearWeight γ χ α₁ α₂ α₃ z₀ r x * ‖x - z‖ ^ β :=
    (measurable_bpzNearWeight z₀ r).mul ((measurable_id.sub measurable_const).norm.pow_const _)
  have hf0 : ∀ x, 0 ≤ bpzNearWeight γ χ α₁ α₂ α₃ z₀ r x * ‖x - z‖ ^ β := fun x =>
    mul_nonneg (bpzNearWeight_nonneg z₀ r x) (Real.rpow_nonneg (norm_nonneg _) _)
  exact bpz_real_bound_of_lintegral P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hε0 hε1 hzne0 hzne1
    hf hf0 (mul_nonneg hC0 hpos) hB

/-- A small radius making `K (2r)^p` small. -/
theorem bpz_exists_small_radius {K p r₁ η : ℝ} (hp : 0 < p) (hr₁ : 0 < r₁) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ r ≤ r₁ ∧ K * (2 * r) ^ p ≤ η := by
  have hc : Tendsto (fun r : ℝ => K * (2 * r) ^ p) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => 2 * r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have : Tendsto (fun r : ℝ => 2 * r) (𝓝 (0 : ℝ)) (𝓝 (2 * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have := (h2.rpow_const_nhds_zero hp).const_mul K
    rwa [mul_zero] at this
  obtain ⟨r, hr1, hr2⟩ := ((hc.eventually (gt_mem_nhds hη)).and (Ioc_mem_nhdsGT hr₁)).exists
  exact ⟨r, hr2.1, hr2.2, hr1.le⟩

/-! ### Dominated convergence for the zeroth moment and for the far parts -/

/-- The almost sure data used in the dominated convergence arguments. -/
theorem bpz_tendsto_mom0 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℂ} (hMm : Measurable M) {a s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s)
    {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ}
    {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hgood : ∀ᵐ ω ∂P, 0 < Y ω ∧ Integrable w (M ω) ∧
      Integrable (fun x => Complex.normSq (x - z₀) ^ a * w x) (M ω) ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → Y ω ≤ bpzSoftMassReal a ε w (M ω) z)
    {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1) (hε : Tendsto εs atTop (𝓝 0))
    {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ ω, bpzSoftMassReal a (εs n) w (M ω) (zs n) ^ (-s) ∂P) atTop
      (𝓝 (∫ ω, bpzSoftMassReal a 0 w (M ω) z₀ ^ (-s) ∂P)) := by
  have hnear : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ 1 :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually (ge_mem_nhds one_pos)
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => Y ω ^ (-s)) ?_ ?_ hYint ?_
  · exact Eventually.of_forall fun n =>
      (((bpz_measurable_softMassReal a (εs n) hw (zs n)).comp hMm).pow_const _).aestronglyMeasurable
  · filter_upwards [hnear] with n hn
    filter_upwards [hgood] with ω hω
    obtain ⟨hY, -, -, hlow⟩ := hω
    have hYI := hlow (zs n) hn (εs n) (hε0 n) (hε1 n)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hY.le.trans hYI) _)]
    exact bpzRpow_neg_le hs hY hYI
  · filter_upwards [hgood] with ω hω
    obtain ⟨hY, hintw, hint, hlow⟩ := hω
    have hI := bpz_tendsto_softMassReal ha ha1 hw hw0 hint hintw hε0 hε1 hε hz
    have hpos : 0 < bpzSoftMassReal a 0 w (M ω) z₀ :=
      hY.trans_le (hlow z₀ (by simp) 0 le_rfl zero_le_one)
    exact hI.rpow_const (Or.inl hpos.ne')

/-- Dominated convergence for the far part of the first moment field. -/
theorem bpz_tendsto_momField1_far {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℂ} (hMm : Measurable M) {a s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s)
    {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hgood : ∀ᵐ ω ∂P, 0 < Y ω ∧ Integrable w (M ω) ∧
      Integrable (fun x => Complex.normSq (x - z₀) ^ a * w x) (M ω) ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → Y ω ≤ bpzSoftMassReal a ε w (M ω) z)
    {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1) (hε : Tendsto εs atTop (𝓝 0))
    {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ ω, bpzMomField1 a s (εs n) w
        (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) (zs n) ∂P) atTop
      (𝓝 (∫ ω, bpzMomField1 a s 0 w (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z₀ ∂P)) := by
  have hnear : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ min 1 (r / 2) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually
      (ge_mem_nhds (lt_min one_pos (half_pos hr)))
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => s * (4 * a / r) * Y ω ^ (-s)) ?_ ?_ (hYint.const_mul _) ?_
  · exact Eventually.of_forall fun n => (bpz_stronglyMeasurable_momField1 hMm a s (εs n) hw
      (bpz_measurable_farPart hw z₀ r) (zs n)).aestronglyMeasurable
  · filter_upwards [hnear] with n hn
    filter_upwards [hgood] with ω hω
    obtain ⟨hY, hintw, hint, hlow⟩ := hω
    have hz1 : ‖zs n - z₀‖ ≤ 1 := hn.trans (min_le_left _ _)
    have hz2 : ‖zs n - z₀‖ ≤ r / 2 := hn.trans (min_le_right _ _)
    have hintz := bpzSoft_integrable_near ha ha1 (hε0 n) (hε1 n) hw hw0 hint hintw hz1
    have hYI := hlow (zs n) hz1 (εs n) (hε0 n) (hε1 n)
    have hDf := norm_bpzSoftMassDeriv_far_le ha hw0 hr hz2 hintz
    exact norm_bpzMomentField_le hs hY hYI (by positivity) hDf
  · filter_upwards [hgood] with ω hω
    obtain ⟨hY, hintw, hint, hlow⟩ := hω
    have hI := bpz_tendsto_softMassReal ha ha1 hw hw0 hint hintw hε0 hε1 hε hz
    have hD := bpz_tendsto_softMassDeriv_far ha ha1 hw hw0 hint hintw hε0 hε1 hε hz hr
    have hpos : 0 < bpzSoftMassReal a 0 w (M ω) z₀ :=
      hY.trans_le (hlow z₀ (by simp) 0 le_rfl zero_le_one)
    unfold bpzMomField1
    exact (tendsto_const_nhds.mul (hI.rpow_const (Or.inl hpos.ne'))).smul hD

/-- Dominated convergence for the far part of the second moment field. -/
theorem bpz_tendsto_momField2_far {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℂ} (hMm : Measurable M) {a s : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 ≤ s)
    {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {z₀ : ℂ} {r : ℝ} (hr : 0 < r)
    {Y : Ω → ℝ} (hYint : Integrable (fun ω => Y ω ^ (-s)) P)
    (hgood : ∀ᵐ ω ∂P, 0 < Y ω ∧ Integrable w (M ω) ∧
      Integrable (fun x => Complex.normSq (x - z₀) ^ a * w x) (M ω) ∧
      ∀ z : ℂ, ‖z - z₀‖ ≤ 1 → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → Y ω ≤ bpzSoftMassReal a ε w (M ω) z)
    {εs : ℕ → ℝ} (hε0 : ∀ n, 0 ≤ εs n) (hε1 : ∀ n, εs n ≤ 1) (hε : Tendsto εs atTop (𝓝 0))
    {zs : ℕ → ℂ} (hz : Tendsto zs atTop (𝓝 z₀)) :
    Tendsto (fun n => ∫ ω, bpzMomField2 a s (εs n) w
        (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) (zs n) ∂P) atTop
      (𝓝 (∫ ω, bpzMomField2 a s 0 w (fun x => if r ≤ ‖x - z₀‖ then w x else 0) (M ω) z₀ ∂P)) := by
  have hnear : ∀ᶠ n in atTop, ‖zs n - z₀‖ ≤ min 1 (r / 2) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hz).eventually
      (ge_mem_nhds (lt_min one_pos (half_pos hr)))
  have hK : 0 ≤ 4 * (4 * a * (1 - a) + 2 * a) / r ^ 2 := by
    have : 0 ≤ 1 - a := sub_nonneg.mpr ha1
    positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => (s * (s + 1) * (4 * a / r) ^ 2 + s * (4 * (4 * a * (1 - a) + 2 * a) / r ^ 2)) *
      Y ω ^ (-s)) ?_ ?_ (hYint.const_mul _) ?_
  · exact Eventually.of_forall fun n => (bpz_stronglyMeasurable_momField2 hMm a s (εs n) hw
      (bpz_measurable_farPart hw z₀ r) (zs n)).aestronglyMeasurable
  · filter_upwards [hnear] with n hn
    filter_upwards [hgood] with ω hω
    obtain ⟨hY, hintw, hint, hlow⟩ := hω
    have hz1 : ‖zs n - z₀‖ ≤ 1 := hn.trans (min_le_left _ _)
    have hz2 : ‖zs n - z₀‖ ≤ r / 2 := hn.trans (min_le_right _ _)
    have hintz := bpzSoft_integrable_near ha ha1 (hε0 n) (hε1 n) hw hw0 hint hintw hz1
    have hYI := hlow (zs n) hz1 (εs n) (hε0 n) (hε1 n)
    have hDf := norm_bpzSoftMassDeriv_far_le ha hw0 hr hz2 hintz
    have hD2f := norm_bpzSoftMassDeriv2_far_le ha ha1 hw0 hr hz2 hintz
    exact norm_bpzMomentField2_le hs hY hYI (by positivity) hDf hD2f
  · filter_upwards [hgood] with ω hω
    obtain ⟨hY, hintw, hint, hlow⟩ := hω
    have hI := bpz_tendsto_softMassReal ha ha1 hw hw0 hint hintw hε0 hε1 hε hz
    have hD := bpz_tendsto_softMassDeriv_far ha ha1 hw hw0 hint hintw hε0 hε1 hε hz hr
    have hD2 := bpz_tendsto_softMassDeriv2_far ha ha1 hw hw0 hint hintw hε0 hε1 hε hz hr
    have hpos : 0 < bpzSoftMassReal a 0 w (M ω) z₀ :=
      hY.trans_le (hlow z₀ (by simp) 0 le_rfl zero_le_one)
    have hc : Continuous (fun L : ℂ →L[ℝ] ℝ => L.smulRight L) :=
      (ContinuousLinearMap.smulRightL ℝ ℂ (ℂ →L[ℝ] ℝ)).continuous₂.comp
        (continuous_id.prodMk continuous_id)
    unfold bpzMomField2
    exact ((tendsto_const_nhds.mul (hI.rpow_const (Or.inl hpos.ne'))).smul
      ((hc.tendsto _).comp hD)).add
      ((tendsto_const_nhds.mul (hI.rpow_const (Or.inl hpos.ne'))).smul hD2)

end DOZZ.Proofs
