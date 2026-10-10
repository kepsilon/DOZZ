/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliFatou
public import DOZZ.GMC.SharpMoments.ArbitraryCenter

/-! Covariance and inverse-product bounds for two geometrically separated retained disks. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The separation margin of the centers survives throughout the two open disks. -/
theorem retained_disk_separation (u v x y : ℂ) (ρ σ d : ℝ)
    (hsep : ρ + σ + d ≤ ‖u - v‖)
    (hx : x ∈ Metric.ball u ρ) (hy : y ∈ Metric.ball v σ) : d ≤ ‖x - y‖ := by
  have hx' : ‖x - u‖ < ρ := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hy' : ‖y - v‖ < σ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have he : u - v = (u - x) + (x - y) + (y - v) := by abel
  have hn := (norm_add_le (u - x + (x - y)) (y - v)).trans
    (add_le_add (norm_add_le (u - x) (x - y)) le_rfl)
  rw [← he, norm_sub_rev u x] at hn
  linarith only [hx', hy', hsep, hn]

/-- Bounded charts and a positive spatial gap give one covariance constant for every cutoff. -/
theorem circle_cross_covariance_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L d r : ℝ) (hL : 0 ≤ L) (hd : 0 < d) (hr : 0 ≤ r)
    (x y : ℂ) (hx : ‖x‖ ≤ L) (hy : ‖y‖ ≤ L) (hxy : d ≤ ‖x - y‖) :
    (∫ ω, Xc ω x r * Xc ω y r ∂P) ≤
      max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) := by
  have hb := circleField_covariance_le_log P X hX Xc hXc L r hL hr x y hx hy
  have hmax : d ≤ max ‖x - y‖ (Real.exp (-r)) := hxy.trans (le_max_left _ _)
  have hp : 0 < max ‖x - y‖ (Real.exp (-r)) := lt_of_lt_of_le hd hmax
  have hl : Real.log (1 / max ‖x - y‖ (Real.exp (-r))) ≤ Real.log (1 / d) :=
    Real.log_le_log (one_div_pos.mpr hp) (one_div_le_one_div_of_le hd hmax)
  have hsum := add_le_add hl (le_refl (Real.log 3 + 2 * Real.log (1 + L)))
  exact (hb.trans (by simpa only [gmcCircleChartRemainder] using hsum)).trans
    (le_max_right _ _)

/-- Cutoff joint inverse moments decouple at a cost independent of either retained radius. -/
theorem joint_retained_disks_cutoff_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (hr : 0 ≤ r) (u v : ℂ) (ρ σ L d a b : ℝ)
    (hL : 0 ≤ L) (hd : 0 < d)
    (hu : ‖u‖ + ρ ≤ L) (hv : ‖v‖ + σ ≤ L)
    (hsep : ρ + σ + d ≤ ‖u - v‖) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball u ρ)) ^ (-a) *
      (regularizedGMC P Xc γ r ω (Metric.ball v σ)) ^ (-b) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 *
        max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 *
          ((a + b) ^ 2 + a + b))) *
        gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball u ρ) (-a) *
          gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball v σ) (-b) := by
  classical
  let A := Metric.ball u ρ
  let B := Metric.ball v σ
  let U := A ∪ B
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hU : MeasurableSet U := hA.union hB
  let ν := gmcReferenceMeasure.restrict U
  have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have : IsFiniteMeasure ν := inferInstance
  let h₀ : ℂ → ℝ≥0 := A.indicator (fun _ => 1)
  let h₁ : ℂ → ℝ≥0 := B.indicator (fun _ => 1)
  have hm₀ : Measurable h₀ := measurable_const.indicator hA
  have hm₁ : Measurable h₁ := measurable_const.indicator hB
  have hbound (D : Set ℂ) : ∃ c : ℝ≥0, ∀ x, D.indicator (fun _ => (1 : ℝ≥0)) x ≤ c := by
    refine ⟨1, ?_⟩
    intro x
    by_cases hx : x ∈ D
    · simp only [Set.indicator_of_mem hx, le_refl]
    · simp only [Set.indicator_of_notMem hx, zero_le]
  have hs₀ : ∀ x, x ∉ A → h₀ x = 0 := fun x hx => Set.indicator_of_notMem hx _
  have hs₁ : ∀ x, x ∈ A → h₁ x = 0 := by
    intro x hx
    apply Set.indicator_of_notMem
    intro hxB
    have h := retained_disk_separation u v x x ρ σ d hsep hx hxB
    rw [sub_self, norm_zero] at h
    exact not_le_of_gt hd h
  let Φ : Ω → ℂ → ℝ := fun ω x => Xc ω x r
  have hΦ := circleAverage_isCenteredGaussianField P X hX Xc hXc r
  have hprod : ν.prod ν = (gmcReferenceMeasure.prod gmcReferenceMeasure).restrict (U ×ˢ U) := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
  have hcross : ∀ᵐ xy ∂ν.prod ν, (xy.1 ∈ A ↔ xy.2 ∉ A) →
      (∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂P) ≤
        max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) := by
    rw [hprod]
    filter_upwards [ae_restrict_mem (hU.prod hU)] with xy hxy
    intro hdifferent
    have hn (x : ℂ) (hx : x ∈ U) : ‖x‖ ≤ L := by
      rcases hx with hx | hx
      · have hxr : ‖x - u‖ < ρ := by simpa only [A, Metric.mem_ball, dist_eq_norm] using hx
        have hnorm := norm_add_le (x - u) u
        rw [sub_add_cancel] at hnorm
        linarith only [hxr, hnorm, hu]
      · have hxr : ‖x - v‖ < σ := by simpa only [B, Metric.mem_ball, dist_eq_norm] using hx
        have hnorm := norm_add_le (x - v) v
        rw [sub_add_cancel] at hnorm
        linarith only [hxr, hnorm, hv]
    apply circle_cross_covariance_bound P X hX Xc hXc L d r hL hd hr
      xy.1 xy.2 (hn xy.1 hxy.1) (hn xy.2 hxy.2)
    by_cases hx : xy.1 ∈ A
    · have hy : xy.2 ∈ B := hxy.2.resolve_left (hdifferent.mp hx)
      exact retained_disk_separation u v xy.1 xy.2 ρ σ d hsep hx hy
    · have hxB : xy.1 ∈ B := hxy.1.resolve_left hx
      have hy : xy.2 ∈ A := by_contra fun h => hx (hdifferent.mpr h)
      rw [norm_sub_rev]
      exact retained_disk_separation u v xy.2 xy.1 ρ σ d hsep hy hxB
  have hk := two_retained_blocks_inverse_compare P Φ hΦ A hA ν h₀ h₁ hm₀ hm₁
    (hbound A) (hbound B) hs₀ hs₁ γ _ a b (le_max_left _ _) ha hb hcross
  have hm0 (ω : Ω) : fieldChaosMass P Φ ν h₀ γ ω =
      regularizedGMC P Xc γ r ω A := by
    rw [fieldChaosMass_indicator P Φ gmcReferenceMeasure A U hA subset_union_left,
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r A hA ω]
  have hm1 (ω : Ω) : fieldChaosMass P Φ ν h₁ γ ω =
      regularizedGMC P Xc γ r ω B := by
    rw [fieldChaosMass_indicator P Φ gmcReferenceMeasure B U hB subset_union_right,
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r B hB ω]
  simp_rw [hm0, hm1] at hk
  exact hk

/-- The retained-annulus comparison on the supplied chaos: two separated retained disks
have joint inverse moments bounded by their marginal moments and one geometric Gaussian factor.
The radii may shrink; the separation and chart constants precede them. -/
theorem joint_retained_annuli_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (u v : ℂ) (ρ σ L d a b : ℝ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hρ8 : ρ ≤ 1 / 8) (hσ8 : σ ≤ 1 / 8)
    (hL : 0 ≤ L) (hd : 0 < d) (hu : ‖u‖ + ρ ≤ L) (hv : ‖v‖ + σ ≤ L)
    (hsep : ρ + σ + d ≤ ‖u - v‖) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫⁻ ω, (M ω (Metric.ball u ρ)) ^ (-a) * (M ω (Metric.ball v σ)) ^ (-b) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 *
        max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 *
          ((a + b) ^ 2 + a + b))) *
        gmcMassMoment P M (Metric.ball u ρ) (-a) *
          gmcMassMoment P M (Metric.ball v σ) (-b) := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  let A := Metric.ball u ρ
  let B := Metric.ball v σ
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 *
    max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 * ((a + b) ^ 2 + a + b)))
  let f₀ : ℕ → Ω → ℝ := fun n ω => (regularizedGMC P Xc γ n ω A).toReal
  let f₁ : ℕ → Ω → ℝ := fun n ω => (regularizedGMC P Xc γ n ω B).toReal
  let g₀ : Ω → ℝ := fun ω => (M ω A).toReal
  let g₁ : Ω → ℝ := fun ω => (M ω B).toReal
  have hcrit : 0 < 4 / γ ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hγ)
  have hp₀ : -a < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr ha) hcrit
  have hp₁ : -b < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr hb) hcrit
  have hma := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM u ρ hρ hρ8 (-a) hp₀
  have hmb := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM v σ hσ hσ8 (-b) hp₁
  have hta := gmc_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc u ρ hρ hρ8 (-a) hp₀
  have htb := gmc_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc v σ hσ hσ8 (-b) hp₁
  let R : ℕ → ℝ≥0∞ := fun n =>
    K * gmcMassMoment P (regularizedGMC P Xc γ n) A (-a) *
      gmcMassMoment P (regularizedGMC P Xc γ n) B (-b)
  have hR : Tendsto R atTop (nhds (K * gmcMassMoment P M A (-a) * gmcMassMoment P M B (-b))) :=
    ENNReal.Tendsto.mul
      (ENNReal.Tendsto.mul tendsto_const_nhds (Or.inr hma.ne) hta (Or.inr ENNReal.ofReal_ne_top))
      (Or.inr hmb.ne) htb (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hma.ne))
  have hf₀ := regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc A
    Metric.isOpen_ball.measurableSet _ (ball_subset_closedBall_norm_add u ρ)
  have hf₁ := regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc B
    Metric.isOpen_ball.measurableSet _ (ball_subset_closedBall_norm_add v σ)
  have hmeas (n : ℕ) : AEMeasurable
      (fun ω => (ENNReal.ofReal (f₀ n ω)) ^ (-a) * (ENNReal.ofReal (f₁ n ω)) ^ (-b)) P := by
    have hm₀ := measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ n A
      Metric.isOpen_ball.measurableSet
    have hm₁ := measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ n B
      Metric.isOpen_ball.measurableSet
    exact ((ENNReal.measurable_ofReal.comp hm₀).pow_const _).aemeasurable.mul
      ((ENNReal.measurable_ofReal.comp hm₁).pow_const _).aemeasurable
  have hg₀ : ∀ᵐ ω ∂P, 0 < g₀ ω := by
    filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM u ρ hρ] with ω hω
    let _ := hM.1 ω
    exact ENNReal.toReal_pos hω.ne' (measure_ne_top _ _)
  have hg₁ : ∀ᵐ ω ∂P, 0 < g₁ ω := by
    filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM v σ hσ] with ω hω
    let _ := hM.1 ω
    exact ENNReal.toReal_pos hω.ne' (measure_ne_top _ _)
  have hbound (n : ℕ) :
      (∫⁻ ω, (ENNReal.ofReal (f₀ n ω)) ^ (-a) * (ENNReal.ofReal (f₁ n ω)) ^ (-b) ∂P) ≤ R n := by
    have he : (fun ω => (ENNReal.ofReal (f₀ n ω)) ^ (-a) * (ENNReal.ofReal (f₁ n ω)) ^ (-b)) =ᵐ[P]
        fun ω => (regularizedGMC P Xc γ n ω A) ^ (-a) * (regularizedGMC P Xc γ n ω B) ^ (-b) := by
      filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hω
      let _ := hω
      dsimp only [f₀, f₁]
      rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [lintegral_congr_ae he]
    exact joint_retained_disks_cutoff_inverse_bound P X hX Xc hXc γ n (Nat.cast_nonneg n)
      u v ρ σ L d a b hL hd hu hv hsep ha hb
  have hfatou := two_mass_fatou P f₀ f₁ g₀ g₁ (-a) (-b) hf₀ hf₁ hmeas hg₀ hg₁
    R _ hR hbound
  have he : (fun ω => (ENNReal.ofReal (g₀ ω)) ^ (-a) * (ENNReal.ofReal (g₁ ω)) ^ (-b)) =
      fun ω => (M ω A) ^ (-a) * (M ω B) ^ (-b) := by
    funext ω
    let _ := hM.1 ω
    dsimp only [g₀, g₁]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [he] at hfatou
  exact hfatou

end DOZZ.Proofs
