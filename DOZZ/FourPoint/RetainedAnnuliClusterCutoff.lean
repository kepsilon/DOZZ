/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliJoint
public import DOZZ.FourPoint.RetainedAnnuliClusterComparison

/-! Two retained cluster disks and one separated fixed disk at the cutoff level. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Decouple the fixed disk, keeping the joint cutoff law of the two cluster disks. -/
theorem retained_cluster_disk_cutoff_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (hr : 0 ≤ r) (z w u v : ℂ) (τ δ ρ σ L d a b s : ℝ)
    (hL : 0 ≤ L) (hd : 0 < d) (hz : ‖z‖ + τ ≤ L) (hw : ‖w‖ + δ ≤ L)
    (hsep : τ + δ + d ≤ ‖z - w‖)
    (hu : Metric.ball u ρ ⊆ Metric.ball z τ) (hv : Metric.ball v σ ⊆ Metric.ball z τ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball u ρ)) ^ (-a) *
      (regularizedGMC P Xc γ r ω (Metric.ball v σ)) ^ (-b) *
      (regularizedGMC P Xc γ r ω (Metric.ball w δ)) ^ (-s) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 *
        max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 *
          ((a + b + s) ^ 2 + a + b + s))) *
        (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball u ρ)) ^ (-a) *
          (regularizedGMC P Xc γ r ω (Metric.ball v σ)) ^ (-b) ∂P) *
            gmcMassMoment P (regularizedGMC P Xc γ r) (Metric.ball w δ) (-s) := by
  classical
  let A := Metric.ball z τ
  let B := Metric.ball w δ
  let U := A ∪ B
  have hA : MeasurableSet A := Metric.isOpen_ball.measurableSet
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hU : MeasurableSet U := hA.union hB
  let ν := gmcReferenceMeasure.restrict U
  have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have : IsFiniteMeasure ν := inferInstance
  let h₀ : ℂ → ℝ≥0 := (Metric.ball u ρ).indicator (fun _ => 1)
  let h₁ : ℂ → ℝ≥0 := (Metric.ball v σ).indicator (fun _ => 1)
  let h₂ : ℂ → ℝ≥0 := B.indicator (fun _ => 1)
  have hm₀ : Measurable h₀ := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hm₁ : Measurable h₁ := measurable_const.indicator Metric.isOpen_ball.measurableSet
  have hm₂ : Measurable h₂ := measurable_const.indicator hB
  have hbound (D : Set ℂ) : ∃ c : ℝ≥0, ∀ x, D.indicator (fun _ => (1 : ℝ≥0)) x ≤ c := by
    refine ⟨1, ?_⟩
    intro x
    by_cases hx : x ∈ D
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  have hs₀ : ∀ x, x ∉ A → h₀ x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun h => hx (hu h)) _
  have hs₁ : ∀ x, x ∉ A → h₁ x = 0 := by
    intro x hx
    exact Set.indicator_of_notMem (fun h => hx (hv h)) _
  have hs₂ : ∀ x, x ∈ A → h₂ x = 0 := by
    intro x hx
    apply Set.indicator_of_notMem
    intro hxB
    have h := retained_disk_separation z w x x τ δ d hsep hx hxB
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
      · have hxr : ‖x - z‖ < τ := by simpa only [A, Metric.mem_ball, dist_eq_norm] using hx
        have hnorm := norm_add_le (x - z) z
        rw [sub_add_cancel] at hnorm
        linarith only [hxr, hnorm, hz]
      · have hxr : ‖x - w‖ < δ := by simpa only [B, Metric.mem_ball, dist_eq_norm] using hx
        have hnorm := norm_add_le (x - w) w
        rw [sub_add_cancel] at hnorm
        linarith only [hxr, hnorm, hw]
    apply circle_cross_covariance_bound P X hX Xc hXc L d r hL hd hr
      xy.1 xy.2 (hn xy.1 hxy.1) (hn xy.2 hxy.2)
    by_cases hx : xy.1 ∈ A
    · have hy : xy.2 ∈ B := hxy.2.resolve_left (hdifferent.mp hx)
      exact retained_disk_separation z w xy.1 xy.2 τ δ d hsep hx hy
    · have hxB : xy.1 ∈ B := hxy.1.resolve_left hx
      have hy : xy.2 ∈ A := by_contra fun h => hx (hdifferent.mpr h)
      rw [norm_sub_rev]
      exact retained_disk_separation z w xy.2 xy.1 τ δ d hsep hy hxB
  have hk := retained_cluster_disk_inverse_compare P Φ hΦ A hA ν h₀ h₁ h₂
    hm₀ hm₁ hm₂ (hbound _) (hbound _) (hbound _) hs₀ hs₁ hs₂ γ _ a b s
    (le_max_left _ _) ha hb hs hcross
  have hm0 (ω : Ω) : fieldChaosMass P Φ ν h₀ γ ω =
      regularizedGMC P Xc γ r ω (Metric.ball u ρ) := by
    rw [fieldChaosMass_indicator P Φ gmcReferenceMeasure (Metric.ball u ρ) U
      Metric.isOpen_ball.measurableSet (hu.trans subset_union_left),
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r _
        Metric.isOpen_ball.measurableSet ω]
  have hm1 (ω : Ω) : fieldChaosMass P Φ ν h₁ γ ω =
      regularizedGMC P Xc γ r ω (Metric.ball v σ) := by
    rw [fieldChaosMass_indicator P Φ gmcReferenceMeasure (Metric.ball v σ) U
      Metric.isOpen_ball.measurableSet (hv.trans subset_union_left),
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r _
        Metric.isOpen_ball.measurableSet ω]
  have hm2 (ω : Ω) : fieldChaosMass P Φ ν h₂ γ ω = regularizedGMC P Xc γ r ω B := by
    rw [fieldChaosMass_indicator P Φ gmcReferenceMeasure B U hB subset_union_right,
      ← regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r B hB ω]
  simp_rw [hm0, hm1, hm2] at hk
  exact hk

end DOZZ.Proofs
