/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.BallAnnulus.RadiusExtension

/-! The two-sided ball estimate `DOZZ.equatorGFF_GMC_ball_moment_bound`, including every negative
moment order. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- A finite random measure has strictly positive nonpositive moments, even if some masses
vanish (at negative orders their extended powers are infinite). -/
theorem gmc_finite_measure_nonpositive_moment_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → Measure ℂ) (hfin : ∀ ω, IsFiniteMeasure (M ω))
    (A : Set ℂ) (hmeas : AEMeasurable (fun ω => M ω A) P) (p : ℝ) (hp : p ≤ 0) :
    0 < gmcMassMoment P M A p := by
  apply pos_iff_ne_zero.mpr
  intro hz
  have he := (lintegral_eq_zero_iff' (hmeas.pow_const p)).mp hz
  have hfalse : ∀ᵐ ω ∂P, False := by
    filter_upwards [he] with ω hω
    let _ := hfin ω
    exact gmc_finite_mass_nonpositive_power_ne_zero (M ω) A hp hω
  obtain ⟨ω, hω⟩ := hfalse.exists
  exact hω

/-- Two-sided ball-mass scaling with one constant uniform on compact center sets. See
[KRV, (momentscaling)]. -/
theorem equatorGFF_GMC_ball_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (p : ℝ) (hp : p < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ENNReal.ofReal (C⁻¹ * Real.rpow ε (γ * Q γ * p - γ ^ 2 * p ^ 2 / 2)) ≤
          gmcMassMoment P M (Metric.ball z ε) p ∧
        gmcMassMoment P M (Metric.ball z ε) p ≤
          ENNReal.ofReal (C * Real.rpow ε (γ * Q γ * p - γ ^ 2 * p ^ 2 / 2)) := by
  let _ := hX.1
  obtain ⟨C₀, hC₀, hsmall⟩ := gmc_compact_small_ball_twoSided_bound
    P X hX γ hγ hγ2 M hM p hp K hK
  obtain ⟨B, hB, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  let O := Metric.closedBall (0 : ℂ) (B+1)
  have hO : MeasurableSet O := Metric.isClosed_closedBall.measurableSet
  have hsubset (z : K) (r : ℝ) (hr1 : r ≤ 1) : Metric.ball z.val r ⊆ O := by
    exact (ball_subset_closedBall_norm_add z.val r).trans
      (Metric.closedBall_subset_closedBall (by linarith [hnorm z.val z.property]))
  have hinner : Metric.ball (0 : ℂ) (1/8) ⊆ O := by
    exact (Metric.ball_subset_closedBall).trans
      (Metric.closedBall_subset_closedBall (by linarith))
  have hmono {A D : Set ℂ} (hAD : A ⊆ D) (hp0 : 0 ≤ p) :
      gmcMassMoment P M A p ≤ gmcMassMoment P M D p :=
    lintegral_mono (fun ω => ENNReal.rpow_le_rpow (measure_mono hAD) hp0)
  have hanti {A D : Set ℂ} (hAD : A ⊆ D) (hp0 : p ≤ 0) :
      gmcMassMoment P M D p ≤ gmcMassMoment P M A p :=
    by
    apply lintegral_mono
    intro ω
    change (M ω D) ^ p ≤ (M ω A) ^ p
    have hh := ENNReal.inv_le_inv.mpr
      (ENNReal.rpow_le_rpow (show M ω A ≤ M ω D from measure_mono hAD) (neg_nonneg.mpr hp0))
    simpa only [← ENNReal.rpow_neg, neg_neg] using hh
  have hcoarse : ∃ l u : ℝ, 0 < l ∧ 0 ≤ u ∧ ∀ z : K, ∀ r : ℝ,
      1/8 ≤ r → r ≤ 1 → ENNReal.ofReal l ≤ gmcMassMoment P M (Metric.ball z.val r) p ∧
        gmcMassMoment P M (Metric.ball z.val r) p ≤ ENNReal.ofReal u := by
    by_cases hp0 : 0 ≤ p
    · have hOt := gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM O
        Metric.isBounded_closedBall p hp0 hp
      refine ⟨C₀⁻¹ * (1/8 : ℝ) ^ gmcScaleExponent γ p,
        (gmcMassMoment P M O p).toReal, mul_pos (inv_pos.mpr hC₀)
          (Real.rpow_pos_of_pos (by norm_num) _), ENNReal.toReal_nonneg, ?_⟩
      intro z r hr hr1
      exact ⟨(hsmall z.val z.property (1/8) (by norm_num) le_rfl).1.trans
        (hmono (Metric.ball_subset_ball hr) hp0),
        (hmono (hsubset z r hr1) hp0).trans_eq (ENNReal.ofReal_toReal hOt.ne).symm⟩
    · have hp0' : p ≤ 0 := (lt_of_not_ge hp0).le
      have hOt : gmcMassMoment P M O p < ⊤ :=
        (hanti hinner hp0').trans_lt (gmc_ball_moment_lt_top_any_center
          P X hX γ hγ hγ2 M hM 0 (1/8) (by norm_num) le_rfl p hp)
      have hOp := gmc_finite_measure_nonpositive_moment_pos P M hM.1 O
        (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM O hO) p hp0'
      refine ⟨(gmcMassMoment P M O p).toReal,
        C₀ * (1/8 : ℝ) ^ gmcScaleExponent γ p,
        ENNReal.toReal_pos hOp.ne' hOt.ne, (by positivity), ?_⟩
      intro z r hr hr1
      exact ⟨(ENNReal.ofReal_toReal hOt.ne).le.trans (hanti (hsubset z r hr1) hp0'),
        (hanti (Metric.ball_subset_ball hr) hp0').trans
          (hsmall z.val z.property (1/8) (by norm_num) le_rfl).2⟩
  obtain ⟨l, u, hl, hu, hcoarse⟩ := hcoarse
  obtain ⟨C, hC, hbound⟩ := gmc_twoSided_radius_extend
    (fun z : K => fun r => gmcMassMoment P M (Metric.ball z.val r) p)
    (gmcScaleExponent γ p) (1/8) (by norm_num) C₀ hC₀
    (fun z r hr hr8 => hsmall z.val z.property r hr hr8) l u hl hu hcoarse
  exact ⟨C, hC, fun z hz r hr hr1 => hbound ⟨z, hz⟩ r hr hr1⟩

end DOZZ.Proofs
end
