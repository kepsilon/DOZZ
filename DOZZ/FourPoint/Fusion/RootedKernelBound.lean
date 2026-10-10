/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MixedKernelBound
public import DOZZ.FourPoint.Fusion.Kernel
import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.Statements.GMC.WeightedGmcBallMass

/-! # Fused-charge domination of the local rooted kernel -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- On the half-unit disk the remaining insertion at one contributes a bounded factor. -/
theorem fusion_oneRoot_factor_bound (x : ℂ) (hx : ‖x‖ ≤ 1 / 2) (e : ℝ) :
    (‖x - 1‖ ^ e)⁻¹ ≤ (2 : ℝ) ^ |e| := by
  have hd : (1 / 2 : ℝ) ≤ ‖x - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) x
    rw [norm_sub_rev] at h
    norm_num at h
    linarith
  have hu : ‖x - 1‖ ≤ 2 := by
    have h := norm_sub_le x (1 : ℂ)
    norm_num at h
    linarith
  rw [← Real.rpow_neg (by linarith : 0 ≤ ‖x - 1‖)]
  have h := coulombWeight_rpow_le (L := 2) (by norm_num)
    (y := ‖x - 1‖) (by norm_num; exact hd) hu (-e)
  simpa only [abs_neg] using h

/-- The local rooted kernel is bounded by the sum of the two fused-charge weights. -/
theorem fusion_rootedKernel_local_bound (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hα : γ / 2 ≤ α₁) (y z x : ℂ) (hy : y ≠ 0)
    (hx : x ≠ 0) (hxu : x ≠ y * z) (hsmall : ‖x‖ ≤ 1 / 2)
    (hu : ‖y * z‖ ≤ 1) :
    gammaHalfKernel γ α₁ α₂ α₃ z x * Real.exp (γ ^ 2 * gffKernel (y * z) x) ≤
      ((2 : ℝ) ^ |γ * α₂| * (1 + 2 / ‖y‖) ^ (γ ^ 2 / 2)) *
        (‖x‖ ^ (-γ * (α₁ + γ / 2)) + ‖x - y * z‖ ^ (-γ * (α₁ + γ / 2))) := by
  have hpx : normPlus x = 1 := max_eq_left (by linarith)
  have hpu : normPlus (y * z) = 1 := max_eq_left hu
  have hd : 0 < ‖x - y * z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu)
  have he : Real.exp (γ ^ 2 * gffKernel (y * z) x) = ‖x - y * z‖ ^ (-γ ^ 2) := by
    rw [gffKernel, hpx, hpu, Real.log_one, add_zero, add_zero,
      norm_sub_rev, Real.rpow_def_of_pos hd]
    congr 1
    ring
  rw [he]
  unfold gammaHalfKernel
  rw [hpx, Real.one_rpow, mul_one, Real.rpow_neg hd.le]
  have hfactor := fusion_oneRoot_factor_bound x hsmall (γ * α₂)
  have hmix := fusion_movingRoot_power_bound γ α₁ hγ hα y z x hy hx hxu
  have hnonneg : 0 ≤ ‖x - z‖ ^ (γ ^ 2 / 2) /
      (‖x‖ ^ (γ * α₁) * ‖x - y * z‖ ^ (γ ^ 2)) := by positivity
  calc
    _ = (‖x - z‖ ^ (γ ^ 2 / 2) /
        (‖x‖ ^ (γ * α₁) * ‖x - y * z‖ ^ (γ ^ 2))) * (‖x - 1‖ ^ (γ * α₂))⁻¹ := by ring
    _ ≤ (‖x - z‖ ^ (γ ^ 2 / 2) /
        (‖x‖ ^ (γ * α₁) * ‖x - y * z‖ ^ (γ ^ 2))) * (2 : ℝ) ^ |γ * α₂| :=
      mul_le_mul_of_nonneg_left hfactor hnonneg
    _ ≤ ((1 + 2 / ‖y‖) ^ (γ ^ 2 / 2) *
        (‖x‖ ^ (-γ * (α₁ + γ / 2)) + ‖x - y * z‖ ^ (-γ * (α₁ + γ / 2)))) *
          (2 : ℝ) ^ |γ * α₂| := mul_le_mul_of_nonneg_right hmix (by positivity)
    _ = _ := by ring

/-- The small-disk contribution is bounded by local masses with the fused charge. -/
theorem fusion_rootedKernel_smallBall_le (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hα : γ / 2 ≤ α₁) (y z : ℂ) (hy : y ≠ 0) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (hu0 : μ {y * z} = 0)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (huδ : ‖y * z‖ ≤ δ) :
    (∫⁻ x in Metric.ball (0 : ℂ) δ,
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂| * (1 + 2 / ‖y‖) ^ (γ ^ 2 / 2)) *
        (weightedGmcBallMass γ μ (α₁ + γ / 2) 0 δ +
          weightedGmcBallMass γ μ (α₁ + γ / 2) (y * z) (2 * δ)) := by
  let C : ℝ := (2 : ℝ) ^ |γ * α₂| * (1 + 2 / ‖y‖) ^ (γ ^ 2 / 2)
  let w : ℂ → ℝ≥0∞ := fun x => ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * (α₁ + γ / 2))
  let v : ℂ → ℝ≥0∞ := fun x => ENNReal.rpow (ENNReal.ofReal ‖x - y * z‖) (-γ * (α₁ + γ / 2))
  have hw : Measurable w := by
    exact (ENNReal.continuous_rpow_const (y := -γ * (α₁ + γ / 2))).measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_norm : Measurable (fun x : ℂ => ‖x‖)))
  have hv : Measurable v := by
    exact (ENNReal.continuous_rpow_const (y := -γ * (α₁ + γ / 2))).measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_id.sub_const (y * z)).norm)
  have ha0 : ∀ᵐ x ∂μ.restrict (Metric.ball (0 : ℂ) δ), x ≠ 0 := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simpa using h0
  have hau : ∀ᵐ x ∂μ.restrict (Metric.ball (0 : ℂ) δ), x ≠ y * z := by
    apply ae_restrict_of_ae
    rw [ae_iff]
    simpa using hu0
  have hbound : (∫⁻ x in Metric.ball (0 : ℂ) δ,
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂μ) ≤
      ∫⁻ x in Metric.ball (0 : ℂ) δ, ENNReal.ofReal C * (w x + v x) ∂μ := by
    apply lintegral_mono_ae
    filter_upwards [ha0, hau, ae_restrict_mem Metric.isOpen_ball.measurableSet] with x hx0 hxu hx
    have hxδ : ‖x‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have h := ENNReal.ofReal_le_ofReal
      (fusion_rootedKernel_local_bound γ α₁ α₂ α₃ hγ hα y z x hy hx0 hxu
        (by linarith) (by linarith))
    have he : ENNReal.ofReal (C * (‖x‖ ^ (-γ * (α₁ + γ / 2)) +
        ‖x - y * z‖ ^ (-γ * (α₁ + γ / 2)))) = ENNReal.ofReal C * (w x + v x) := by
      rw [ENNReal.ofReal_mul (by dsimp [C]; positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      dsimp [w, v]
      rw [ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr hx0),
        ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxu))]
    exact h.trans_eq he
  have hsub : Metric.ball (0 : ℂ) δ ⊆ Metric.ball (y * z) (2 * δ) := by
    intro x hx
    have hxδ : ‖x‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hx
    have h := norm_sub_le x (y * z)
    rw [Metric.mem_ball, dist_eq_norm]
    linarith
  calc
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) δ, ENNReal.ofReal C * (w x + v x) ∂μ := hbound
    _ = ENNReal.ofReal C * ((∫⁻ x in Metric.ball (0 : ℂ) δ, w x ∂μ) +
        ∫⁻ x in Metric.ball (0 : ℂ) δ, v x ∂μ) := by
      have hsum : Measurable (fun x => w x + v x) := hw.add hv
      rw [lintegral_const_mul _ hsum, lintegral_add_left hw]
    _ ≤ _ := by
      apply mul_le_mul' le_rfl
      simp only [weightedGmcBallMass, sub_zero]
      change (∫⁻ x in Metric.ball (0 : ℂ) δ, w x ∂μ) +
          (∫⁻ x in Metric.ball (0 : ℂ) δ, v x ∂μ) ≤
        (∫⁻ x in Metric.ball (0 : ℂ) δ, w x ∂μ) +
          (∫⁻ x in Metric.ball (y * z) (2 * δ), v x ∂μ)
      apply add_le_add le_rfl
      exact lintegral_mono' (Measure.restrict_mono hsub le_rfl) le_rfl

end DOZZ.Proofs
