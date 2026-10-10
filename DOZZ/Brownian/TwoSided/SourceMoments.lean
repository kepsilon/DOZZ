/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseGamma
public import DOZZ.GMC.SharpMoments.BallScaling
public import DOZZ.Brownian.Lateral.SharpPositive
public import DOZZ.Brownian.LateralUnitBlock.LateralInverse

/-! Charge-uniform reference moments, independent of the chosen source witnesses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- On the reference chart, convex moments increase with the charge even when the two
circle-average fields are different versions of the equator field. -/
theorem twosided_reference_cutoff_convex_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : Ω → Distr) (hX : IsEquatorGFF P X) (hY : IsEquatorGFF P Y)
    (Xc Yc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hYc : IsCircleAverage P Y Yc) (γ g r p : ℝ)
    (hγ : 0 < γ) (hγg : γ ≤ g) (hr : 1 ≤ r) (hp : p ≤ 0 ∨ 1 ≤ p) :
    gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 (1 / 8)) p ≤
      gmcMassMoment P (regularizedGMC P Yc g r) (Metric.ball 0 (1 / 8)) p := by
  have hg : 0 < g := lt_of_lt_of_le hγ hγg
  let c : ℝ := γ / g
  have hc0 : 0 ≤ c := div_nonneg hγ.le hg.le
  have hc1 : c ≤ 1 := (div_le_one hg).mpr hγg
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  let A : Set ℂ := Metric.ball 0 (1 / 8)
  let ν : Measure ℂ := gmcReferenceMeasure.restrict A
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet
  have hνfin : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (subset_univ A)))
  have hΦ := circleAverage_smul_isCenteredGaussianField P X hX Xc hXc r c
  have hΨ := circleAverage_isCenteredGaussianField P Y hY Yc hYc r
  have hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, c * Xc ω xy.1 r * (c * Xc ω xy.2 r) ∂P ≤
        ∫ ω, Yc ω xy.1 r * Yc ω xy.2 r ∂P := by
    have hprod : ν.prod ν = (gmcReferenceMeasure.prod gmcReferenceMeasure).restrict (A ×ˢ A) := by
      have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
      dsimp only [ν]
      rw [Measure.prod_restrict]
    rw [hprod]
    filter_upwards [ae_restrict_mem (hA.prod hA)] with xy hxy
    have he : (fun ω => c * Xc ω xy.1 r * (c * Xc ω xy.2 r)) =
        fun ω => c ^ 2 * (Xc ω xy.1 r * Xc ω xy.2 r) := by funext ω; ring
    rw [he, integral_const_mul]
    have h0 := circleField_covariance_nonneg_reference P X hX Xc hXc r hr
      xy.1 hxy.1 xy.2 hxy.2
    have heq : (∫ ω, Yc ω xy.1 r * Yc ω xy.2 r ∂P) =
        ∫ ω, Xc ω xy.1 r * Xc ω xy.2 r ∂P := by
      rw [circleField_covariance_eq P Y hY Yc hYc,
        circleField_covariance_eq P X hX Xc hXc]
    rw [heq]
    nlinarith
  have hdiag : ∀ᵐ x ∂ν, ∫ ω, (c * Xc ω x r) ^ 2 ∂P ≤ ∫ ω, Yc ω x r ^ 2 ∂P := by
    filter_upwards [] with x
    have he : (fun ω => (c * Xc ω x r) ^ 2) = fun ω => c ^ 2 * Xc ω x r ^ 2 := by
      funext ω; ring
    rw [he, integral_const_mul]
    have heq : (∫ ω, Yc ω x r ^ 2 ∂P) = ∫ ω, Xc ω x r ^ 2 ∂P := by
      simp only [pow_two]
      rw [circleField_covariance_eq P Y hY Yc hYc,
        circleField_covariance_eq P X hX Xc hXc]
    rw [heq]
    have h0 : 0 ≤ ∫ ω, Xc ω x r ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    nlinarith
  have hk := kahane_field_power_convex P P (fun ω x => c * Xc ω x r)
    (fun ω x => Yc ω x r) hΦ hΨ ν (fun _ => 1) measurable_const
    ⟨1, fun _ => le_rfl⟩ g p hp hcov hdiag
  change (∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ p ∂P) ≤
    ∫⁻ ω, (regularizedGMC P Yc g r ω A) ^ p ∂P
  simp only [regularizedGMC_apply_eq_fieldChaosMass_scaled P X hX Xc hXc γ g r hg.ne' A hA,
    regularizedGMC_apply_eq_fieldChaosMass P Y hY Yc hYc g r A hA]
  exact hk

/-- Fatou only needs the cutoff estimate after time one; no coarse-cutoff premise is added. -/
theorem twosided_reference_moment_le_of_fine_cutoffs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (p : ℝ) (C : ℝ≥0∞)
    (hbound : ∀ r : ℝ, 1 ≤ r →
      gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball 0 (1 / 8)) p ≤ C) :
    gmcMassMoment P M (Metric.ball 0 (1 / 8)) p ≤ C := by
  let A : Set ℂ := Metric.ball 0 (1 / 8)
  let f : ℕ → Ω → ℝ := fun n ω => (regularizedGMC P Xc γ (n + 1 : ℕ) ω A).toReal
  let g : Ω → ℝ := fun ω => (M ω A).toReal
  have hseq : Tendsto (fun n : ℕ => n + 1) atTop atTop := tendsto_add_atTop_nat 1
  have hconv : TendstoInMeasure P f atTop g :=
    (regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc A
      Metric.isOpen_ball.measurableSet (1 / 8) Metric.ball_subset_closedBall).comp hseq
  have hfmeas (n : ℕ) : Measurable (f n) :=
    measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ _ A Metric.isOpen_ball.measurableSet
  have hpow (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p) P :=
    (ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp ((hfmeas n).max measurable_const))).aemeasurable
  have hfbound (n : ℕ) : (∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (max (f n ω) 0)) p ∂P) ≤ C := by
    refine le_trans (le_of_eq ?_) (hbound (n + 1 : ℕ) (by exact_mod_cast Nat.le_add_left 1 n))
    unfold gmcMassMoment
    apply lintegral_congr_ae
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ (n + 1 : ℕ)] with ω hω
    let _ := hω
    dsimp only [f]
    rw [max_eq_left ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hfatou := lintegral_ennreal_rpow_le_of_tendstoInMeasure P f g p C hconv hpow
    (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) hfbound
  refine le_trans (le_of_eq ?_) hfatou
  unfold gmcMassMoment
  apply lintegral_congr
  intro ω
  let _ := hM.1 ω
  exact congrArg (fun x : ℝ≥0∞ => x ^ p) (ENNReal.ofReal_toReal (measure_ne_top (M ω) A)).symm

/-- One fixed equator witness at the maximal charge bounds every source witness and every
smaller charge, at any single convex subcritical order. -/
theorem twosided_reference_convex_moments_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : Ω → Distr) (hY : IsEquatorGFF P Y)
    (Yc : Ω → ℂ → ℝ → ℝ) (hYc : IsCircleAverage P Y Yc)
    (g : ℝ) (hg : 0 < g) (hg2 : g < 2) (p : ℝ)
    (hp : p < 0 ∨ 1 ≤ p) (hcrit : p < 4 / g ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ g →
      ∀ X : Ω → Distr, ∀ M : Ω → Measure ℂ,
        IsEquatorGFF P X → IsGMCOf P X γ M →
          gmcMassMoment P M (Metric.ball 0 (1 / 8)) p ≤ C := by
  have hfixed : ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
      gmcMassMoment P (regularizedGMC P Yc g r) (Metric.ball 0 (1 / 8)) p ≤ C := by
    rcases hp with hp | hp
    · obtain ⟨K, hK⟩ := regularizedGMC_reference_inverse_moment_uniform P Y hY Yc hYc
        g hg hg2 (-p) (neg_pos.mpr hp)
      refine ⟨ENNReal.ofReal K, ENNReal.ofReal_lt_top, ?_⟩
      intro r hr
      change (∫⁻ ω, (regularizedGMC P Yc g r ω (Metric.ball 0 (1 / 8))) ^ p ∂P) ≤ _
      simpa only [neg_neg] using hK r hr
    · exact regularizedGMC_reference_moment_uniform_nonnegative P Y hY Yc hYc g p hg
        (le_trans zero_le_one hp) hcrit (by norm_num) le_rfl
  obtain ⟨C, hC, hbound⟩ := hfixed
  refine ⟨C, hC, ?_⟩
  intro γ hγ hγg X M hX hM
  obtain ⟨Xc, hXc, -⟩ := hM.2
  apply twosided_reference_moment_le_of_fine_cutoffs P X hX γ hγ (lt_of_le_of_lt hγg hg2)
    M hM Xc hXc p C
  intro r hr
  exact (twosided_reference_cutoff_convex_comparison P X Y hX hY Xc Yc hXc hYc γ g r p
    hγ hγg hr (hp.imp le_of_lt id)).trans (hbound r (le_trans zero_le_one hr))

end DOZZ.Proofs
