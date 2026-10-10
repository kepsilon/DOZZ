/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseGamma
public import DOZZ.GMC.SharpMoments.CriticalEndpoint
public import DOZZ.GMC.Annulus.HigherScales

/-! # Moments of small disks at arbitrary centers

At every center the location transfer compares cutoff moments of a small disk with those of the
same disk at the origin, where the cutoff-uniform positive moments (below `4/γ²`) and the
inverse moments are known. Fatou passes these bounds to every `IsGMCOf` limit. In particular every
disk has almost surely positive mass, which discharges the positivity hypothesis of the critical
endpoint on the logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Cutoff-uniform moments of every order below `4/γ²` of a small disk at an arbitrary center. -/
theorem regularizedGMC_ball_moment_uniform_any_center
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (p : ℝ) (hp : p < 4 / γ ^ 2) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball z ρ) p ≤ K := by
  -- the reference bound at the origin
  obtain ⟨K₀, hK₀, hK₀bound⟩ : ∃ K₀ : ℝ≥0∞, K₀ < ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 ρ) p ≤ K₀ := by
    rcases le_or_gt 0 p with hp0 | hp0
    · exact regularizedGMC_reference_moment_uniform_nonnegative P X hX Xc hXc γ p hγ hp0 hp hρ
        hρ8
    · have hΓ : IsCompact ({γ} : Set ℝ) := isCompact_singleton
      have hΓ2 : ({γ} : Set ℝ) ⊆ Set.Ioo 0 2 := by
        rw [Set.singleton_subset_iff]
        exact ⟨hγ, hγ2⟩
      obtain ⟨K, hK⟩ := regularizedGMC_ball_inverse_moment_uniform_gamma P X hX Xc hXc {γ} hΓ hΓ2
        (-p) (by linarith) ρ hρ hρ8
      refine ⟨ENNReal.ofReal K, ENNReal.ofReal_lt_top, fun r hr => ?_⟩
      have := hK γ (Set.mem_singleton γ) r hr
      rwa [neg_neg] at this
  set R : ℝ := ‖z‖ + ρ with hRdef
  have hR : 0 ≤ R := by positivity
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) /
      2 * |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| with hT
  have hTtop : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top)
  refine ⟨T * K₀, ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hTtop) hK₀, fun r hr => ?_⟩
  have htr := cutoff_translate_moment_le P X hX Xc hXc γ r hr z 0 ρ R hR le_rfl (by simp [hRdef])
    (fun _ => 1) measurable_const 1 (fun _ => le_rfl) p
  have hone : ∀ (c : ℂ) (ω : Ω), (∫⁻ x in Metric.ball c ρ, ((fun _ : ℂ => (1 : ℝ≥0)) (x - c) :
      ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) = regularizedGMC P Xc γ r ω (Metric.ball c ρ) := by
    intro c ω
    simp
  simp only [hone] at htr
  calc gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball z ρ) p
      ≤ T * gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 ρ) p := htr
    _ ≤ T * K₀ := by gcongr; exact hK₀bound r hr

/-- Every `IsGMCOf` limit has finite moments of every order below `4/γ²` on small disks at
arbitrary centers. -/
theorem gmc_ball_moment_lt_top_any_center
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (p : ℝ) (hp : p < 4 / γ ^ 2) :
    gmcMassMoment P M (Metric.ball z ρ) p < ⊤ := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  obtain ⟨K, hK, hKbound⟩ := regularizedGMC_ball_moment_uniform_any_center P X hX Xc hXc γ hγ hγ2
    z ρ hρ hρ8 p hp
  have hsub : Metric.ball z ρ ⊆ Metric.closedBall 0 (‖z‖ + ρ) := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + ρ := by linarith
  exact (gmcMassMoment_le_of_cutoff_uniform P X hX γ hγ hγ2 M hM Xc hXc (Metric.ball z ρ)
    Metric.isOpen_ball.measurableSet (‖z‖ + ρ) hsub p K hKbound).trans_lt hK

/-- Every disk has almost surely positive mass. -/
theorem gmc_ball_mass_pos_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, 0 < M ω (Metric.ball z ρ) := by
  set ρ' : ℝ := min ρ (1 / 8) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (by norm_num)
  have hfin := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM z ρ' hρ'pos
    (min_le_right _ _) (-1) (by
      have : 0 < 4 / γ ^ 2 := by positivity
      linarith)
  have hmeas : AEMeasurable (fun ω => M ω (Metric.ball z ρ') ^ (-1 : ℝ)) P :=
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet).pow_const _
  have hae := ae_lt_top' hmeas hfin.ne
  filter_upwards [hae] with ω hω
  have hpos : 0 < M ω (Metric.ball z ρ') := by
    by_contra h0
    push Not at h0
    have hz : M ω (Metric.ball z ρ') = 0 := le_antisymm h0 zero_le
    rw [hz, ENNReal.zero_rpow_of_neg (by norm_num)] at hω
    exact lt_irrefl _ hω
  exact lt_of_lt_of_le hpos (measure_mono (Metric.ball_subset_ball (min_le_left _ _)))

/-- The critical moment of a small open square in the logarithmic chart is infinite. -/
theorem gmc_openSquare_critical_moment_eq_top_of_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : ℝ) (hs : 0 < s) (hs2 : s < 1 / 4) :
    gmcMassMoment P M (gmcOpenSquare s) (4 / γ ^ 2) = ⊤ := by
  have hball : ∀ σ₁ σ₂ : ℝ, Metric.ball (⟨σ₁ * s / 2, σ₂ * s / 2⟩ : ℂ) (s / 2) ⊆
      gmcSubSquare s σ₁ σ₂ := by
    intro σ₁ σ₂ x hx
    rw [mem_gmcSubSquare_iff]
    rw [Metric.mem_ball, dist_eq_norm] at hx
    constructor
    · have := Complex.abs_re_le_norm (x - ⟨σ₁ * s / 2, σ₂ * s / 2⟩)
      simp only [Complex.sub_re] at this
      linarith
    · have := Complex.abs_im_le_norm (x - ⟨σ₁ * s / 2, σ₂ * s / 2⟩)
      simp only [Complex.sub_im] at this
      linarith
  have hpos : ∀ σ₁ σ₂ : ℝ, ∀ᵐ ω ∂P, 0 < M ω (gmcSubSquare s σ₁ σ₂) := by
    intro σ₁ σ₂
    filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM _ (s / 2) (by positivity)]
      with ω hω
    exact lt_of_lt_of_le hω (measure_mono (hball σ₁ σ₂))
  apply gmc_openSquare_critical_moment_eq_top P X hX γ hγ hγ2 M hM s hs hs2
  filter_upwards [hpos 1 1, hpos (-1) 1, hpos (-1) (-1), hpos 1 (-1)] with ω h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- Every bounded set has finite moments of every nonnegative order below `4/γ²`. -/
theorem gmc_bounded_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (O : Set ℂ) (hO : Bornology.IsBounded O) (p : ℝ) (hp0 : 0 ≤ p) (hp : p < 4 / γ ^ 2) :
    gmcMassMoment P M O p < ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  rcases le_or_gt p 1 with hp1 | hp1
  · have h := gmc_mass_subunit_moment_bound P X hX γ M hM O hp0 hp1
    have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
    exact h.trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, measure_lt_top _ _⟩)
  -- cover the closure by finitely many small disks
  have hK : IsCompact (closure O) := hO.isCompact_closure
  obtain ⟨t, -, htfin, hcover⟩ := finite_cover_balls_of_compact hK (by norm_num : (0 : ℝ) < 1 / 16)
  set S : Finset ℂ := htfin.toFinset with hS
  have hOS : O ⊆ ⋃ c ∈ S, Metric.ball c (1 / 16) := by
    intro x hx
    have := hcover (subset_closure hx)
    simpa [hS] using this
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · have hOe : O = ∅ := by
      rw [hSe] at hOS
      simpa using hOS
    subst hOe
    unfold gmcMassMoment
    simp [ENNReal.zero_rpow_of_pos (by linarith : (0 : ℝ) < p)]
  have hpoint : ∀ ω, M ω O ^ p ≤ (S.card : ℝ≥0∞) ^ p *
      ∑ c ∈ S, M ω (Metric.ball c (1 / 16)) ^ p := by
    intro ω
    calc M ω O ^ p ≤ (∑ c ∈ S, M ω (Metric.ball c (1 / 16))) ^ p := by
          apply ENNReal.rpow_le_rpow _ hp0
          exact (measure_mono hOS).trans (measure_biUnion_finset_le _ _)
      _ ≤ _ := ennreal_finset_sum_rpow_le_card_rpow_sum S hSne _ p hp0
  have hball : ∀ c ∈ S, gmcMassMoment P M (Metric.ball c (1 / 16)) p < ⊤ := fun c _ =>
    gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM c (1 / 16) (by norm_num) (by norm_num) p
      hp
  have hmeas : ∀ c ∈ S, AEMeasurable (fun ω => M ω (Metric.ball c (1 / 16)) ^ p) P :=
    fun c _ => (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet).pow_const _
  calc gmcMassMoment P M O p = ∫⁻ ω, M ω O ^ p ∂P := rfl
    _ ≤ ∫⁻ ω, (S.card : ℝ≥0∞) ^ p * ∑ c ∈ S, M ω (Metric.ball c (1 / 16)) ^ p ∂P :=
        lintegral_mono hpoint
    _ = (S.card : ℝ≥0∞) ^ p * ∑ c ∈ S, gmcMassMoment P M (Metric.ball c (1 / 16)) p := by
        rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum S hmeas),
          lintegral_finsetSum' S hmeas]
        rfl
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hp0 (ENNReal.natCast_ne_top _))
        (ENNReal.sum_lt_top.mpr hball)

end DOZZ.Proofs
