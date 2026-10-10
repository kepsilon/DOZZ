/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.Statements.GMC.WeightedGmcBallMass

/-! # Decomposition of the Coulomb mass

For a measure without atoms at the finite roots, the Coulomb mass is bounded by constant
multiples of the weighted local masses at the roots, of the mass of a bounded disk, and of the
power weight at infinity integrated over the exterior of a large disk. A fixed exterior disk gives
a lower bound by a positive multiple of its mass. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Distinct roots are uniformly separated: some radius `δ ∈ (0, 1/8]` has `2δ` below every
distance between distinct roots. -/
theorem exists_root_separation {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖ := by
  have h : ∀ j k : Fin N, ∀ᶠ δ in 𝓝[>] (0 : ℝ), j ≠ k → 2 * δ ≤ ‖z j - z k‖ := by
    intro j k
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ h => absurd hjk h
    · have hpos : 0 < ‖z j - z k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hz.ne hjk))
      filter_upwards [Ioo_mem_nhdsGT (half_pos hpos)] with δ hδ _
      linarith [hδ.2]
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖ := by
    rw [eventually_all]
    intro j
    rw [eventually_all]
    exact h j
  obtain ⟨δ, hδ1, hδ2⟩ := (hall.and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num))).exists
  exact ⟨δ, hδ2.1, hδ2.2.le, hδ1⟩

/-- With no atom at the root, the Coulomb mass of a small root disk is at most a constant times
the weighted local mass at the root. -/
theorem coulomb_root_piece_le {N : ℕ} (μ : Measure ℂ) (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf : ℝ) (k : Fin N) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ j, j ≠ k → 2 * δ ≤ ‖z j - z k‖) (hatom : μ {z k} = 0) :
    ∫⁻ x in Metric.ball (z k) δ, coulombWeight γ α z αinf x ∂μ ≤
      ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) *
        weightedGmcBallMass γ μ (α k) (z k) δ := by
  have hB : MeasurableSet (Metric.ball (z k) δ) := Metric.isOpen_ball.measurableSet
  have hw : Measurable fun x : ℂ => ENNReal.rpow (ENNReal.ofReal ‖x - z k‖) (-γ * α k) :=
    (ENNReal.continuous_rpow_const (y := -γ * α k)).measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.sub_const _).norm)
  have hne : ∀ᵐ x ∂μ.restrict (Metric.ball (z k) δ), x ≠ z k :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp hatom)
  unfold weightedGmcBallMass
  rw [← lintegral_const_mul _ hw]
  apply lintegral_mono_ae
  filter_upwards [hne, ae_restrict_mem hB] with x hxk hx
  exact coulombWeight_le_root γ α z αinf k hδ hδ1 hsep hx hxk

theorem measurableSet_coulombBulk {N : ℕ} (z : Fin N → ℂ) (δ Rr : ℝ) :
    MeasurableSet {y : ℂ | ‖y‖ ≤ Rr ∧ ∀ k, δ ≤ ‖y - z k‖} := by
  have h : {y : ℂ | ‖y‖ ≤ Rr ∧ ∀ k, δ ≤ ‖y - z k‖} =
      {y : ℂ | ‖y‖ ≤ Rr} ∩ ⋂ k, {y : ℂ | δ ≤ ‖y - z k‖} := by
    ext y
    simp
  rw [h]
  exact (measurableSet_le measurable_norm measurable_const).inter
    (MeasurableSet.iInter fun k => measurableSet_le measurable_const
      (measurable_id.sub_const _).norm)

/-- The exterior radius used in the decomposition. -/
theorem coulomb_exterior_radius_bounds {N : ℕ} (z : Fin N → ℂ) :
    1 ≤ 1 + 2 * ∑ j, ‖z j‖ ∧ ∀ j, 2 * ‖z j‖ ≤ 1 + 2 * ∑ j, ‖z j‖ := by
  have hsum : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  refine ⟨by linarith, fun j => ?_⟩
  have := Finset.single_le_sum (f := fun j => ‖z j‖) (fun j _ => norm_nonneg _)
    (Finset.mem_univ j)
  linarith

/-- For a measure without atoms at the roots, the Coulomb mass is bounded by its root, bulk and
exterior pieces. -/
theorem coulombMass_le_pieces {N : ℕ} (μ : Measure ℂ) (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖) (hatom : ∀ k, μ {z k} = 0)
    {Rr : ℝ} (hRr1 : 1 ≤ Rr) (hzRr : ∀ j, 2 * ‖z j‖ ≤ Rr) :
    coulombMass γ μ α z αinf ≤
      ∑ k, ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) *
          weightedGmcBallMass γ μ (α k) (z k) δ +
        ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) *
          μ (Metric.closedBall 0 Rr) +
        ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) *
          ∫⁻ x in {x : ℂ | Rr < ‖x‖}, ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂μ := by
  set F : ℂ → ℝ≥0∞ := coulombWeight γ α z αinf with hF
  have hFm : Measurable F := measurable_coulombWeight γ α z αinf
  set K : Set ℂ := {y : ℂ | ‖y‖ ≤ Rr ∧ ∀ k, δ ≤ ‖y - z k‖} with hK
  set E : Set ℂ := {y : ℂ | Rr < ‖y‖} with hE
  have hKm : MeasurableSet K := measurableSet_coulombBulk z δ Rr
  have hEm : MeasurableSet E := measurableSet_lt measurable_const measurable_norm
  have hBm : ∀ k, MeasurableSet (Metric.ball (z k) δ) := fun k =>
    Metric.isOpen_ball.measurableSet
  have hg : Measurable fun x : ℂ => ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) :=
    (ENNReal.continuous_rpow_const (y := γ * αinf)).measurable.comp
      (ENNReal.measurable_ofReal.comp measurable_norm)
  rw [coulombMass_eq_lintegral_coulombWeight]
  calc ∫⁻ x, F x ∂μ
      ≤ ∫⁻ x, ((∑ k, (Metric.ball (z k) δ).indicator F x + K.indicator F x) +
          E.indicator F x) ∂μ := lintegral_mono fun x => coulombWeight_le_pieces γ α z αinf δ Rr x
    _ = ∑ k, ∫⁻ x in Metric.ball (z k) δ, F x ∂μ + ∫⁻ x, K.indicator F x ∂μ +
          ∫⁻ x, E.indicator F x ∂μ := by
        have hS : Measurable fun x => ∑ k, (Metric.ball (z k) δ).indicator F x :=
          Finset.measurable_fun_sum _ fun k _ => hFm.indicator (hBm k)
        have hSK : Measurable fun x => ∑ k, (Metric.ball (z k) δ).indicator F x +
            K.indicator F x := hS.add (hFm.indicator hKm)
        rw [lintegral_add_left hSK, lintegral_add_left hS,
          lintegral_finsetSum _ fun k _ => hFm.indicator (hBm k)]
        simp only [lintegral_indicator (hBm _)]
    _ ≤ _ := by
        gcongr with k hk
        · exact coulomb_root_piece_le μ γ α z αinf k hδ hδ1 (fun j hj => hsep j k hj) (hatom k)
        · rw [← lintegral_indicator_const Metric.isClosed_closedBall.measurableSet]
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ K
          · have hxb : x ∈ Metric.closedBall (0 : ℂ) Rr := by
              rw [Metric.mem_closedBall, dist_zero_right]
              exact hx.1
            rw [Set.indicator_of_mem hx, Set.indicator_of_mem hxb]
            exact coulombWeight_le_bulk γ α z αinf hδ hδ1 (by linarith) hx.1 hx.2
          · rw [Set.indicator_of_notMem hx]
            exact zero_le
        · rw [← lintegral_const_mul _ hg, ← lintegral_indicator hEm]
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ E
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
            exact coulombWeight_le_exterior γ α z αinf hRr1 hzRr hx
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-- A fixed exterior disk bounds the Coulomb mass from below by a positive multiple of its
mass. -/
theorem coulombMass_ge_exterior_ball {N : ℕ} (μ : Measure ℂ) (γ : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (αinf : ℝ) {Rr : ℝ} (hRr1 : 1 ≤ Rr) (hzRr : ∀ j, 2 * ‖z j‖ ≤ Rr) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) * ENNReal.ofReal ((Rr + 2) ^ (-|γ * αinf|)) *
        μ (Metric.ball (((Rr + 1 : ℝ)) : ℂ) (1 / 8)) ≤
      coulombMass γ μ α z αinf := by
  set B : Set ℂ := Metric.ball (((Rr + 1 : ℝ)) : ℂ) (1 / 8) with hB
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hnorm : ∀ x ∈ B, Rr + 7 / 8 < ‖x‖ ∧ ‖x‖ < Rr + 9 / 8 := by
    intro x hx
    rw [hB, Metric.mem_ball, dist_eq_norm] at hx
    have hc : ‖(((Rr + 1 : ℝ)) : ℂ)‖ = Rr + 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h1 := norm_sub_norm_le x (((Rr + 1 : ℝ)) : ℂ)
    have h2 := norm_sub_norm_le (((Rr + 1 : ℝ)) : ℂ) x
    rw [norm_sub_rev] at h2
    rw [hc] at h1 h2
    constructor <;> linarith
  rw [coulombMass_eq_lintegral_coulombWeight]
  calc ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((Rr + 2) ^ (-|γ * αinf|)) * μ B
      = ∫⁻ _x in B, ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
          ENNReal.ofReal ((Rr + 2) ^ (-|γ * αinf|)) ∂μ := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ x in B, coulombWeight γ α z αinf x ∂μ := by
        apply setLIntegral_mono' hBm
        intro x hx
        obtain ⟨h1, h2⟩ := hnorm x hx
        refine le_trans ?_ (coulombWeight_ge_exterior γ α z αinf hRr1 hzRr
          (show Rr < ‖x‖ by linarith))
        gcongr
        refine ennreal_ofReal_le_rpow_ofReal_of_mem_Icc (by linarith) ?_ (by linarith) _
        calc (Rr + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
          _ ≤ ‖x‖ := by linarith
    _ ≤ ∫⁻ x, coulombWeight γ α z αinf x ∂μ := setLIntegral_le_lintegral _ _

end DOZZ.Proofs
