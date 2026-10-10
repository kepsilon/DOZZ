/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliComparison
public import DOZZ.GMC.SharpMoments.LocationTransfer

/-! Simultaneous bounded-chart translation for retained cutoff masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Exponents add on a positive finite extended base. -/
theorem rpow_sum {κ : Type*} (A : ℝ≥0∞) (hA : A ≠ 0) (hAt : A ≠ ⊤)
    (q : κ → ℝ) (s : Finset κ) : A ^ (∑ k ∈ s, q k) = ∏ k ∈ s, A ^ q k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk, Finset.prod_insert hk]
    rw [ENNReal.rpow_add _ _ hA hAt, ih]

/-- Translation of a family of negative cutoff moments with one common covariance factor.
The density factor depends on the sum of the orders. Neither mass independence nor separate
Gaussian comparisons are presumed. -/
theorem cutoff_translate_multi_inverse
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (hr : 0 ≤ r)
    (z z₀ : ℂ) (ρ L : ℝ) (hL : 0 ≤ L) (hzL : ‖z‖ + ρ ≤ L) (hz₀L : ‖z₀‖ + ρ ≤ L)
    (w : κ → ℂ → ℝ≥0) (hw : ∀ k, Measurable (w k))
    (hwc : ∀ k, ∃ c : ℝ≥0, ∀ y, w k y ≤ c) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k) :
    (∫⁻ ω, ∏ k, (∫⁻ x in Metric.ball z ρ, (w k (x - z) : ℝ≥0∞)
      ∂regularizedGMC P Xc γ r ω) ^ (-q k) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * gmcCircleChartRemainder L) / 2 *
        ((∑ k, q k) ^ 2 + ∑ k, q k))) *
        ENNReal.ofReal ((1 + L) ^ 4) ^ (∑ k, q k) *
          ∫⁻ ω, ∏ k, (∫⁻ x in Metric.ball z₀ ρ, (w k (x - z₀) : ℝ≥0∞)
            ∂regularizedGMC P Xc γ r ω) ^ (-q k) ∂P := by
  classical
  let C : ℝ := 2 * gmcCircleChartRemainder L
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (gmcCircleChartRemainder_nonneg hL)
  let ν : Measure ℂ := volume.restrict (Metric.ball 0 ρ)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let Φ : Ω → ℂ → ℝ := fun ω y => Xc ω (y + z) r
  let Ψ : Ω → ℂ → ℝ := fun ω y => Xc ω (y + z₀) r
  have hΦ := circleAverage_translate_isCenteredGaussianField P X hX Xc hXc r z
  have hΨ := circleAverage_translate_isCenteredGaussianField P X hX Xc hXc r z₀
  have hball : ∀ᵐ y ∂ν, ‖y‖ < ρ := by
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with y hy
    simpa only [Metric.mem_ball, dist_zero_right] using hy
  have hin (y : ℂ) (hy : ‖y‖ < ρ) : ‖y + z‖ ≤ L ∧ ‖y + z₀‖ ≤ L :=
    ⟨(norm_add_le _ _).trans (by linarith only [hy, hzL]),
      (norm_add_le _ _).trans (by linarith only [hy, hz₀L])⟩
  have hcov : ∀ᵐ xy ∂ν.prod ν,
      (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤ (∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂P) + C := by
    have hprod : ν.prod ν = (volume.prod volume).restrict
        (Metric.ball (0 : ℂ) ρ ×ˢ Metric.ball (0 : ℂ) ρ) := by
      dsimp only [ν]
      rw [Measure.prod_restrict]
    rw [hprod]
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.prod
      Metric.isOpen_ball.measurableSet)] with xy hxy
    have hx : ‖xy.1‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hxy.1
    have hy : ‖xy.2‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hxy.2
    have hh := translated_covariance_abs_sub_le P X hX Xc hXc L r hL hr z z₀ xy.1 xy.2
      (hin xy.1 hx).1 (hin xy.2 hy).1 (hin xy.1 hx).2 (hin xy.2 hy).2
    have hu := (abs_le.mp hh).2
    dsimp only [Φ, Ψ, C, gmcCircleChartRemainder]
    linarith only [hu]
  have hdiag : ∀ᵐ y ∂ν,
      (∫ ω, Φ ω y ^ 2 ∂P) ≤ (∫ ω, Ψ ω y ^ 2 ∂P) + C := by
    filter_upwards [hball] with y hy
    have hh := translated_covariance_abs_sub_le P X hX Xc hXc L r hL hr z z₀ y y
      (hin y hy).1 (hin y hy).1 (hin y hy).2 (hin y hy).2
    have hu := sub_le_iff_le_add.mp (abs_le.mp hh).2
    dsimp only [Φ, Ψ, C, gmcCircleChartRemainder]
    simp only [pow_two]
    linarith only [hu]
  have hweights (k : κ) : ∃ c : ℝ≥0, ∀ y, translatedWeight (w k) z y ≤ c := by
    obtain ⟨c, hc⟩ := hwc k
    exact ⟨c, translatedWeight_le (w k) c hc z⟩
  have hk := retained_fields_multi_negative_compare P P Φ Ψ hΦ hΨ ν
    (fun k => translatedWeight (w k) z) (fun k => measurable_translatedWeight (w k) (hw k) z)
    hweights γ C hC q hq hcov hdiag
  let A : ℝ≥0∞ := ENNReal.ofReal ((1 + L) ^ 4)
  have hA : 1 ≤ A := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith only [hL]))
  have hA0 : A ≠ 0 := (zero_lt_one.trans_le hA).ne'
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmass (k : κ) (ω : Ω) :
      fieldChaosMass P Ψ ν (translatedWeight (w k) z) γ ω ^ (-q k) ≤
        A ^ q k * fieldChaosMass P Ψ ν (translatedWeight (w k) z₀) γ ω ^ (-q k) := by
    have h₁ := fieldChaosMass_le_const_mul_of_weight P Ψ ν
      (translatedWeight (w k) z) (translatedWeight (w k) z₀) γ A hAt
      (hball.mono fun y hy => translatedWeight_le_mul (w k) z z₀ y hL (hin y hy).2) ω
    have h₂ := fieldChaosMass_le_const_mul_of_weight P Ψ ν
      (translatedWeight (w k) z₀) (translatedWeight (w k) z) γ A hAt
      (hball.mono fun y hy => translatedWeight_le_mul (w k) z₀ z y hL (hin y hy).1) ω
    simpa only [abs_neg, abs_of_nonneg (hq k)] using
      ennreal_rpow_le_of_two_sided A _ _ hA hAt h₁ h₂ (-q k)
  have hpoint (ω : Ω) :
      (∏ k, fieldChaosMass P Ψ ν (translatedWeight (w k) z) γ ω ^ (-q k)) ≤
        A ^ (∑ k, q k) * ∏ k, fieldChaosMass P Ψ ν (translatedWeight (w k) z₀) γ ω ^ (-q k) := by
    rw [rpow_sum A hA0 hAt, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun k _ => hmass k ω)
  have hsum : 0 ≤ ∑ k, q k := Finset.sum_nonneg (fun k _ => hq k)
  have hstep := (lintegral_mono (μ := P) hpoint).trans_eq
    (lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hsum hAt))
  have htotal := hk.trans (mul_le_mul' le_rfl hstep)
  have hm (s : ℂ) (k : κ) (ω : Ω) :=
    translated_cutoff_mass_eq_fieldChaosMass P X hX Xc hXc γ r s ρ (w k) (hw k) ω
  dsimp only [Φ, Ψ, ν] at htotal
  simp_rw [← hm z, ← hm z₀] at htotal
  simpa only [mul_assoc] using htotal

/-- A translated indicator in a common containing ball recovers the retained disk mass. -/
theorem retained_ball_indicator_mass (μ : Measure ℂ) (z u : ℂ) (ρ τ : ℝ)
    (hsub : Metric.ball u ρ ⊆ Metric.ball 0 τ) :
    let w : ℂ → ℝ≥0 := (Metric.ball u ρ).indicator (fun _ => 1)
    (∫⁻ x in Metric.ball z τ, (w (x - z) : ℝ≥0∞) ∂μ) = μ (Metric.ball (u + z) ρ) := by
  dsimp only
  have hmem (x : ℂ) : x - z ∈ Metric.ball u ρ ↔ x ∈ Metric.ball (u + z) ρ := by
    simp only [Metric.mem_ball, dist_eq_norm]
    have he : x - z - u = x - (u + z) := by abel
    rw [he]
  let w : ℂ → ℝ≥0 := (Metric.ball u ρ).indicator (fun _ => 1)
  have hfun : (fun x : ℂ => (w (x - z) : ℝ≥0∞)) =
        (Metric.ball (u + z) ρ).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    dsimp only [w]
    by_cases hx : x - z ∈ Metric.ball u ρ
    · simp only [Set.indicator_of_mem hx, Set.indicator_of_mem ((hmem x).mp hx),
        ENNReal.coe_one]
    · simp only [Set.indicator_of_notMem hx, Set.indicator_of_notMem
        (fun h => hx ((hmem x).mpr h)), ENNReal.coe_zero]
  have htarget : Metric.ball (u + z) ρ ⊆ Metric.ball z τ := by
    intro x hx
    have hh := hsub ((hmem x).mpr hx)
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hh
  change (∫⁻ x in Metric.ball z τ, (w (x - z) : ℝ≥0∞) ∂μ) = _
  rw [hfun, lintegral_indicator Metric.isOpen_ball.measurableSet]
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
  rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet, inter_eq_left.mpr htarget]

/-- A simultaneous translation bound for the two cutoff retained disks. -/
theorem cutoff_joint_ball_inverse_translate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) (hr : 0 ≤ r)
    (z z₀ u v : ℂ) (ρ σ τ L a b : ℝ) (hL : 0 ≤ L)
    (hzL : ‖z‖ + τ ≤ L) (hz₀L : ‖z₀‖ + τ ≤ L)
    (hu : Metric.ball u ρ ⊆ Metric.ball 0 τ) (hv : Metric.ball v σ ⊆ Metric.ball 0 τ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball (u + z) ρ)) ^ (-a) *
      (regularizedGMC P Xc γ r ω (Metric.ball (v + z) σ)) ^ (-b) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * gmcCircleChartRemainder L) / 2 *
        ((a + b) ^ 2 + a + b))) * ENNReal.ofReal ((1 + L) ^ 4) ^ (a + b) *
          ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball (u + z₀) ρ)) ^ (-a) *
            (regularizedGMC P Xc γ r ω (Metric.ball (v + z₀) σ)) ^ (-b) ∂P := by
  let w : Fin 2 → ℂ → ℝ≥0 := ![(Metric.ball u ρ).indicator (fun _ => 1),
    (Metric.ball v σ).indicator (fun _ => 1)]
  have hm : ∀ k, Measurable (w k) := by
    intro k
    fin_cases k <;> exact measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hw : ∀ k, ∃ c : ℝ≥0, ∀ x, w k x ≤ c := by
    intro k
    refine ⟨1, ?_⟩
    intro x
    fin_cases k
    · change (Metric.ball u ρ).indicator (fun _ => (1 : ℝ≥0)) x ≤ 1
      by_cases hx : x ∈ Metric.ball u ρ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
    · change (Metric.ball v σ).indicator (fun _ => (1 : ℝ≥0)) x ≤ 1
      by_cases hx : x ∈ Metric.ball v σ
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact zero_le
  have hq : ∀ k : Fin 2, 0 ≤ (![a, b] : Fin 2 → ℝ) k := by
    intro k
    fin_cases k
    · exact ha
    · exact hb
  have hh := cutoff_translate_multi_inverse P X hX Xc hXc γ r hr z z₀ τ L
    hL hzL hz₀L w hm hw ![a, b] hq
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, w, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hh
  have hmu (s : ℂ) (ω : Ω) :=
    retained_ball_indicator_mass (regularizedGMC P Xc γ r ω) s u ρ τ hu
  have hmv (s : ℂ) (ω : Ω) :=
    retained_ball_indicator_mass (regularizedGMC P Xc γ r ω) s v σ τ hv
  simp_rw [hmu z, hmv z, hmu z₀, hmv z₀] at hh
  simpa only [add_assoc] using hh

end DOZZ.Proofs
