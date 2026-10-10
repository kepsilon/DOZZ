/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.LocalScale
public import Mathlib.Data.Finset.Max

/-!
# Fixed-shape covers for GMC annuli

An outer annulus of scale epsilon can be covered by finitely many balls of that same
scale. A fixed cover is chosen once on the radius-two reference disk. Moving the centers
through a compact set and a bounded radius interval preserves compactness. Positive
moments use a finite-sum estimate, without independence of the covered masses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- One finite family of unit balls covers the radius-two reference disk. -/
theorem gmc_reference_disk_unit_cover :
    ∃ S : Finset ℂ, S.Nonempty ∧ Metric.closedBall (0 : ℂ) 2 ⊆
      ⋃ v ∈ S, Metric.ball v 1 := by
  classical
  obtain ⟨S, hS⟩ := (isCompact_closedBall (0 : ℂ) (2 : ℝ)).elim_finite_subcover
    (fun v : ℂ => Metric.ball v 1) (fun _ => Metric.isOpen_ball)
    (fun x _ => mem_iUnion.mpr ⟨x, by simp⟩)
  have h0 := hS (show (0 : ℂ) ∈ Metric.closedBall 0 2 by simp)
  simp only [mem_iUnion] at h0
  obtain ⟨v, hv, _⟩ := h0
  exact ⟨S, ⟨v, hv⟩, hS⟩

/-- Centers in a fixed reference cover move affinely with the annulus. -/
def gmcScaledCoverCenter (z v : ℂ) (ε : ℝ) : ℂ := z + (ε : ℂ) * v

/-- Scaling a fixed reference cover gives an outer-ball cover at every positive radius. -/
theorem gmc_scaled_disk_cover (S : Finset ℂ)
    (hS : Metric.closedBall (0 : ℂ) 2 ⊆ ⋃ v ∈ S, Metric.ball v 1)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Metric.ball z (2 * ε) ⊆ ⋃ v ∈ S, Metric.ball (gmcScaledCoverCenter z v ε) ε := by
  intro x hx
  let y : ℂ := (ε : ℂ)⁻¹ * (x - z)
  have hnormε : ‖(ε : ℂ)‖ = ε := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  have hy : y ∈ Metric.closedBall (0 : ℂ) 2 := by
    have hx' : ‖x - z‖ < 2 * ε := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn : ‖y‖ = ‖x - z‖ / ε := by
      dsimp [y]
      rw [norm_mul, norm_inv, hnormε]
      simp only [div_eq_mul_inv, mul_comm]
    rw [Metric.mem_closedBall, dist_zero_right, hn]
    exact ((div_lt_iff₀ hε).mpr hx').le
  have hc := hS hy
  simp only [mem_iUnion] at hc ⊢
  obtain ⟨v, hv, hyv⟩ := hc
  refine ⟨v, hv, ?_⟩
  have hd : x - gmcScaledCoverCenter z v ε = (ε : ℂ) * (y - v) := by
    dsimp [gmcScaledCoverCenter, y]
    field_simp [Complex.ofReal_ne_zero.mpr hε.ne']
    ring
  have hv' : ‖y - v‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hyv
  rw [Metric.mem_ball, dist_eq_norm, hd, norm_mul, hnormε]
  exact (mul_lt_mul_of_pos_left hv' hε).trans_eq (mul_one _)

/-- Measure subadditivity uses the fixed finite cover, even when its balls overlap. -/
theorem gmc_outer_ball_mass_le_cover_sum (μ : Measure ℂ) (S : Finset ℂ)
    (hS : Metric.closedBall (0 : ℂ) 2 ⊆ ⋃ v ∈ S, Metric.ball v 1)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    μ (Metric.ball z (2 * ε)) ≤
      ∑ v ∈ S, μ (Metric.ball (gmcScaledCoverCenter z v ε) ε) :=
  (measure_mono (gmc_scaled_disk_cover S hS z hε)).trans (measure_biUnion_finset_le _ _)

/-- Every nonnegative power of a finite sum is bounded by the sum of the corresponding
powers times a finite cardinality factor. No probabilistic independence enters this estimate. -/
theorem ennreal_finset_sum_rpow_le_card_rpow_sum
    {ι : Type*} (S : Finset ι) (hne : S.Nonempty) (f : ι → ℝ≥0∞)
    (p : ℝ) (hp : 0 ≤ p) :
    (∑ i ∈ S, f i) ^ p ≤ (S.card : ℝ≥0∞) ^ p * ∑ i ∈ S, (f i) ^ p := by
  classical
  obtain ⟨i₀, hi₀, hmax⟩ := S.exists_max_image f hne
  have hsum : (∑ i ∈ S, f i) ≤ (S.card : ℝ≥0∞) * f i₀ := by
    calc
      _ ≤ ∑ _i ∈ S, f i₀ := Finset.sum_le_sum (fun i hi => hmax i hi)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have h := ENNReal.rpow_le_rpow hsum hp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp] at h
  exact h.trans (mul_le_mul' le_rfl (Finset.single_le_sum (f := fun i => (f i) ^ p) (fun _ _ => zero_le) hi₀))

/-- The same cover bounds every nonnegative power of the actual outer-ball mass. -/
theorem gmc_outer_ball_rpow_le_cover_sum (μ : Measure ℂ) (S : Finset ℂ) (hne : S.Nonempty)
    (hS : Metric.closedBall (0 : ℂ) 2 ⊆ ⋃ v ∈ S, Metric.ball v 1)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p) :
    (μ (Metric.ball z (2 * ε))) ^ p ≤
      (S.card : ℝ≥0∞) ^ p *
        ∑ v ∈ S, (μ (Metric.ball (gmcScaledCoverCenter z v ε) ε)) ^ p :=
  (ENNReal.rpow_le_rpow (gmc_outer_ball_mass_le_cover_sum μ S hS z hε) hp).trans
    (ennreal_finset_sum_rpow_le_card_rpow_sum S hne _ p hp)

/-- The random full measure supplied by any `DOZZ.IsGMCOf` version is AE measurable. -/
theorem gmc_measure_aemeasurable_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    AEMeasurable M P := by
  obtain ⟨N, hN, _, he⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  exact hN.aemeasurable.congr (he.mono (fun _ h => h.symm))

/-- Integrating the finite-sum estimate controls outer-ball moments by the moments at the
moving cover centers. This is valid at orders both below and above one. -/
theorem gmc_outer_ball_moment_le_cover_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (hM : AEMeasurable M P) (S : Finset ℂ) (hne : S.Nonempty)
    (hS : Metric.closedBall (0 : ℂ) 2 ⊆ ⋃ v ∈ S, Metric.ball v 1)
    (z : ℂ) {ε : ℝ} (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p) :
    gmcMassMoment P M (Metric.ball z (2 * ε)) p ≤
      (S.card : ℝ≥0∞) ^ p *
        ∑ v ∈ S, gmcMassMoment P M (Metric.ball (gmcScaledCoverCenter z v ε) ε) p := by
  have hf (v : ℂ) : AEMeasurable
      (fun ω => (M ω (Metric.ball (gmcScaledCoverCenter z v ε) ε)) ^ p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((Measure.measurable_coe Metric.isOpen_ball.measurableSet).comp_aemeasurable hM)
  change (∫⁻ ω, (M ω (Metric.ball z (2 * ε))) ^ p ∂P) ≤ _
  calc
    _ ≤ ∫⁻ ω, (S.card : ℝ≥0∞) ^ p *
        ∑ v ∈ S, (M ω (Metric.ball (gmcScaledCoverCenter z v ε) ε)) ^ p ∂P := by
      apply lintegral_mono
      intro ω
      exact gmc_outer_ball_rpow_le_cover_sum (M ω) S hne hS z hε p hp
    _ = _ := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero
        (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne)) (by simp)),
        lintegral_finsetSum' S (fun v _ => hf v)]
      rfl

/-- All moving centers in one finite cover, over the full radius range. -/
def gmcCoverCenterSet (K : Set ℂ) (S : Finset ℂ) : Set ℂ :=
  ⋃ v ∈ S, (fun q : ℂ × ℝ => gmcScaledCoverCenter q.1 v q.2) '' (K ×ˢ Icc 0 1)

/-- Moving a finite reference cover over compact centers produces a compact center set. -/
theorem isCompact_gmcCoverCenterSet (K : Set ℂ) (hK : IsCompact K) (S : Finset ℂ) :
    IsCompact (gmcCoverCenterSet K S) := by
  apply S.isCompact_biUnion
  intro v hv
  exact (hK.prod isCompact_Icc).image (by
    dsimp [gmcScaledCoverCenter]
    fun_prop)

/-- Each radius-dependent cover center belongs to this one compact set. -/
theorem gmcScaledCoverCenter_mem_centerSet (K : Set ℂ) (S : Finset ℂ)
    {z v : ℂ} (hz : z ∈ K) (hv : v ∈ S) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    gmcScaledCoverCenter z v ε ∈ gmcCoverCenterSet K S := by
  exact mem_iUnion.mpr ⟨v, mem_iUnion.mpr ⟨hv, ⟨(z, ε), ⟨hz, hε, hε1⟩, rfl⟩⟩⟩

/-- The inner ball used for inverse moments also has centers in a fixed compact image. -/
def gmcInnerAnnulusCenterSet (K : Set ℂ) : Set ℂ :=
  (fun q : ℂ × ℝ => q.1 + ((3 * q.2 / 2 : ℝ) : ℂ)) '' (K ×ˢ Icc 0 1)

theorem isCompact_gmcInnerAnnulusCenterSet (K : Set ℂ) (hK : IsCompact K) :
    IsCompact (gmcInnerAnnulusCenterSet K) :=
  (hK.prod isCompact_Icc).image (by fun_prop)

theorem gmc_inner_annulus_center_mem (K : Set ℂ) {z : ℂ} (hz : z ∈ K)
    {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    z + ((3 * ε / 2 : ℝ) : ℂ) ∈ gmcInnerAnnulusCenterSet K :=
  ⟨(z, ε), ⟨hz, hε, hε1⟩, rfl⟩

/-- A finite cover transfers any supplied uniform ball upper estimate to the outer ball at
radius twice epsilon. This keeps every covering ball within the original radius range. -/
theorem gmc_outer_ball_uniform_upper_from_cover
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (hM : AEMeasurable M P) (K : Set ℂ) (S : Finset ℂ) (hne : S.Nonempty)
    (hS : Metric.closedBall (0 : ℂ) 2 ⊆ ⋃ v ∈ S, Metric.ball v 1)
    (p ξ C : ℝ) (hp : 0 ≤ p)
    (hBall : ∀ z ∈ gmcCoverCenterSet K S, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      gmcMassMoment P M (Metric.ball z ε) p ≤ ENNReal.ofReal (C * ε ^ ξ)) :
    ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      gmcMassMoment P M (Metric.ball z (2 * ε)) p ≤
        ENNReal.ofReal (((S.card : ℝ) ^ p * S.card * C) * ε ^ ξ) := by
  intro z hz ε hε hε1
  have hb := gmc_outer_ball_moment_le_cover_sum P M hM S hne hS z hε p hp
  have hs : (∑ v ∈ S, gmcMassMoment P M (Metric.ball (gmcScaledCoverCenter z v ε) ε) p) ≤
      (S.card : ℝ≥0∞) * ENNReal.ofReal (C * ε ^ ξ) := by
    calc
      _ ≤ ∑ _v ∈ S, ENNReal.ofReal (C * ε ^ ξ) :=
        Finset.sum_le_sum (fun v hv => hBall _
          (gmcScaledCoverCenter_mem_centerSet K S hz hv hε.le hε1) ε hε hε1)
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have h := hb.trans (mul_le_mul' le_rfl hs)
  have hn : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
  have he : (S.card : ℝ≥0∞) ^ p * ((S.card : ℝ≥0∞) * ENNReal.ofReal (C * ε ^ ξ)) =
      ENNReal.ofReal (((S.card : ℝ) ^ p * S.card * C) * ε ^ ξ) := by
    rw [← ENNReal.ofReal_natCast S.card, ENNReal.ofReal_rpow_of_pos hn,
      ← ENNReal.ofReal_mul hn.le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hn.le p)]
    congr 1
    ring
  exact h.trans_eq he

/-- Complete weighted-annulus assembly from the separate unweighted ball upper estimate. The input
is written in full as the upstream ball theorem, and is not added as a hypothesis of
`DOZZ.equatorGFF_GMC_annulus_moment_bound`. This lemma supplies its finite-cover and inverse-power
proof steps. -/
theorem gmc_weighted_annulus_upper_of_ball_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (hM : ∀ ω, IsFiniteMeasure (M ω))
    (hMm : AEMeasurable M P) (β p ξ : ℝ)
    (hBall : ∀ L : Set ℂ, IsCompact L →
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        gmcMassMoment P M (Metric.ball z ε) p ≤ ENNReal.ofReal (C * ε ^ ξ))
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ ω, (gmcWeightedAnnulusMass (M ω) z ε β) ^ p ∂P) ≤
        ENNReal.ofReal (C * ε ^ (ξ + β * p)) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨S, hne, hS⟩ := gmc_reference_disk_unit_cover
    obtain ⟨C, hC, hCBall⟩ := hBall (gmcCoverCenterSet K S) (isCompact_gmcCoverCenterSet K hK S)
    let N : ℝ := (S.card : ℝ) ^ p * S.card * C
    let D : ℝ := (2 : ℝ) ^ (|β| * |p|) * N
    have hn : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hne)
    have hN : 0 < N := mul_pos (mul_pos (Real.rpow_pos_of_pos hn _) hn) hC
    have hD : 0 < D := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hN
    refine ⟨D, hD, ?_⟩
    intro z hz ε hε hε1
    have hb := gmc_outer_ball_uniform_upper_from_cover P M hMm K S hne hS p ξ C hp
      hCBall z hz ε hε hε1
    have h := (gmcWeightedAnnulusMoment_le_outer_ball P M hM z hε β p hp).trans
      (mul_le_mul' le_rfl hb)
    rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hε _)).le] at h
    have he : ((2 : ℝ) ^ (|β| * |p|) * ε ^ (β * p)) * (N * ε ^ ξ) = D * ε ^ (ξ + β * p) := by
      rw [Real.rpow_add hε]
      dsimp [D]
      ring
    exact h.trans_eq (congrArg ENNReal.ofReal he)
  · have hp' : p ≤ 0 := le_of_not_ge hp
    obtain ⟨C, hC, hCBall⟩ := hBall (gmcInnerAnnulusCenterSet K)
      (isCompact_gmcInnerAnnulusCenterSet K hK)
    let D : ℝ := (2 : ℝ) ^ (|β| * |p|) * C * (1 / 4 : ℝ) ^ ξ
    have hD : 0 < D := mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hC)
      (Real.rpow_pos_of_pos (by norm_num) _)
    refine ⟨D, hD, ?_⟩
    intro z hz ε hε hε1
    have hb := hCBall _ (gmc_inner_annulus_center_mem K hz hε.le hε1)
      (ε / 4) (by positivity) (by linarith)
    have h := (gmcWeightedAnnulusMoment_le_inner_ball P M hM z hε β p hp').trans
      (mul_le_mul' le_rfl hb)
    rw [← ENNReal.ofReal_mul (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos hε _)).le] at h
    have he : ((2 : ℝ) ^ (|β| * |p|) * ε ^ (β * p)) * (C * (ε / 4) ^ ξ) = D * ε ^ (ξ + β * p) := by
      rw [div_eq_mul_inv, Real.mul_rpow hε.le (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹),
        Real.rpow_add hε]
      dsimp [D]
      simp only [one_div]
      ring
    exact h.trans_eq (congrArg ENNReal.ofReal he)

/-- A common geometric shape factor controls the positive-cover and inverse-inner-ball
branches simultaneously. Its arguments are the weight, moment, and scaling exponents. -/
noncomputable def gmcAnnulusCoverFactor (N : ℕ) (β p ξ : ℝ) : ℝ :=
  (2 : ℝ) ^ (|β| * |p|) * ((N : ℝ) ^ p * N + (1 / 4 : ℝ) ^ ξ)

/-- For a nonempty reference cover, the shape factor is continuous in all three exponents. -/
theorem continuous_gmcAnnulusCoverFactor {N : ℕ} (hN : 0 < N) :
    Continuous (fun t : ℝ × ℝ × ℝ => gmcAnnulusCoverFactor N t.1 t.2.1 t.2.2) := by
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hn0 : (N : ℝ) ≠ 0 := hn.ne'
  have h20 : (2 : ℝ) ≠ 0 := by norm_num
  have h40 : (1 / 4 : ℝ) ≠ 0 := by norm_num
  unfold gmcAnnulusCoverFactor
  fun_prop

/-- Compact parameter sets have a common strictly positive geometric factor. This is only
compactness of the explicit finite-cover coefficients, not uniformity of reference moments. -/
theorem gmcAnnulusCoverFactor_uniform {N : ℕ} (hN : 0 < N)
    (T : Set (ℝ × ℝ × ℝ)) (hT : IsCompact T) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ T, gmcAnnulusCoverFactor N t.1 t.2.1 t.2.2 ≤ B := by
  obtain ⟨b, hb⟩ := hT.bddAbove_image (continuous_gmcAnnulusCoverFactor hN).continuousOn
  refine ⟨max 1 b, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro t ht
  exact (hb (mem_image_of_mem _ ht)).trans (le_max_right _ _)

/-- The common shape factor dominates the positive-cover coefficient. -/
theorem gmcAnnulusCoverFactor_ge_positive (N : ℕ) (β p ξ : ℝ) :
    (2 : ℝ) ^ (|β| * |p|) * ((N : ℝ) ^ p * N) ≤ gmcAnnulusCoverFactor N β p ξ := by
  unfold gmcAnnulusCoverFactor
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  exact le_add_of_nonneg_right (Real.rpow_nonneg (by norm_num) _)

/-- It also dominates the shifted-inner-ball coefficient for inverse orders. -/
theorem gmcAnnulusCoverFactor_ge_inverse (N : ℕ) (β p ξ : ℝ) :
    (2 : ℝ) ^ (|β| * |p|) * (1 / 4 : ℝ) ^ ξ ≤ gmcAnnulusCoverFactor N β p ξ := by
  unfold gmcAnnulusCoverFactor
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num) _)
  exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _))


/-- Application of the geometric annulus assembly to a GMC version, with the literal weighted
exponent of `DOZZ.equatorGFF_GMC_annulus_moment_bound`. The separate ball estimate is an explicit
hypothesis here. -/
theorem gmc_source_annulus_upper_of_sharp_ball_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α p : ℝ)
    (hBall : ∀ L : Set ℂ, IsCompact L →
      ∃ C : ℝ, 0 < C ∧ ∀ z ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        gmcMassMoment P M (Metric.ball z ε) p ≤
          ENNReal.ofReal (C * ε ^ (γ * Q γ * p - γ ^ 2 * p ^ 2 / 2)))
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ ω, (∫⁻ x in {x : ℂ | ε < ‖x - z‖ ∧ ‖x - z‖ < 2 * ε},
        ENNReal.ofReal (‖x - z‖ ^ (-γ * α)) ∂M ω) ^ p ∂P) ≤
          ENNReal.ofReal (C * ε ^ (γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2)) := by
  have hm := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
  obtain ⟨C, hC, hbound⟩ := gmc_weighted_annulus_upper_of_ball_upper P M hM.1 hm
    (-γ * α) p (gmcScaleExponent γ p) hBall K hK
  refine ⟨C, hC, ?_⟩
  intro z hz ε hε hε1
  have h := hbound z hz ε hε hε1
  rw [weightedAnnulus_exponent_eq γ α p] at h
  exact h


end DOZZ.Proofs
