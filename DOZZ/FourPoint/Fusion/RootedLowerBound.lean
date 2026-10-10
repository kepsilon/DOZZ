/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootedMass
import DOZZ.GMC.Construction.RootedMeasureKernel
import DOZZ.GMC.SharpMoments.SeibergDecomp
public import DOZZ.GMC.SharpMoments.LocationTransfer
import DOZZ.GMC.SharpMoments.ArbitraryCenter
import DOZZ.GMC.SharpMoments.SeibergMoment

/-! # A uniform lower bound for the rooted density

The covariance kernel is bounded below globally. Thus rooting preserves every fixed-disk
lower bound for the mass, uniformly in the location of the root.
-/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The equator covariance is bounded below even with the totalized diagonal value. -/
theorem fusion_gffKernel_lower (u x : ℂ) : -Real.log 2 ≤ gffKernel u x := by
  have hu : 1 ≤ normPlus u := le_max_left _ _
  have hx : 1 ≤ normPlus x := le_max_left _ _
  have hu0 : 0 < normPlus u := lt_of_lt_of_le zero_lt_one hu
  have hx0 : 0 < normPlus x := lt_of_lt_of_le zero_lt_one hx
  have hud : ‖u‖ ≤ normPlus u := le_max_right _ _
  have hxd : ‖x‖ ≤ normPlus x := le_max_right _ _
  have hb : ‖u - x‖ ≤ 2 * (normPlus u * normPlus x) := by
    have h1 : normPlus u ≤ normPlus u * normPlus x := le_mul_of_one_le_right hu0.le hx
    have h2 : normPlus x ≤ normPlus u * normPlus x := le_mul_of_one_le_left hx0.le hu
    have hn := norm_sub_le u x
    linarith
  by_cases hdiag : u = x
  · subst x
    simp only [gffKernel, sub_self, norm_zero, Real.log_zero, neg_zero, zero_add]
    have hlog := Real.log_nonneg hu
    have htwo : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have hd : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdiag)
    have hlog := Real.log_le_log hd hb
    rw [Real.log_mul (by norm_num) (mul_pos hu0 hx0).ne',
      Real.log_mul hu0.ne' hx0.ne'] at hlog
    unfold gffKernel
    linarith

/-- A positive constant bounds every rooted density from below. -/
theorem fusion_rootDensity_lower (γ : ℝ) (u x : ℂ) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (fusion_gffKernel_lower u x) (sq_nonneg γ)
  nlinarith only [h]

/-- Rooting uniformly preserves a lower bound for any Coulomb mass. -/
theorem fusion_rootedCoulombMass_lower {N : ℕ} (γ : ℝ) (u : ℂ) (μ : Measure ℂ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) * coulombMass γ μ α z αinf ≤
      coulombMass γ (gmcRootedMeasure γ u μ) α z αinf := by
  have hd : Measurable (fun x : ℂ =>
      ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x))) := by
    exact ENNReal.measurable_ofReal.comp
      ((measurable_const.mul (measurable_pointRootPotential.comp
        (measurable_const.prodMk measurable_id))).exp)
  rw [coulombMass_eq_lintegral_coulombWeight, coulombMass_eq_lintegral_coulombWeight,
    gmcRootedMeasure, lintegral_withDensity_eq_lintegral_mul μ hd
      (measurable_coulombWeight _ _ _ _),
    ← lintegral_const_mul _ (measurable_coulombWeight _ _ _ _)]
  exact lintegral_mono fun x => mul_le_mul' (fusion_rootDensity_lower γ u x) le_rfl

/-- A fixed disk lower bound is uniform in all roots in the unit disk and in the rooting point. -/
theorem fusion_rootedMass_disk_lower {N : ℕ} (γ : ℝ) (u : ℂ) (μ : Measure ℂ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    (ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
      (ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((4 : ℝ) ^ (-|γ * αinf|)))) *
      μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      coulombMass γ (gmcRootedMeasure γ u μ) α z αinf := by
  have hmass := coulombMass_ge_exterior_ball μ γ α z αinf
    (Rr := 2) (by norm_num) (fun j => by linarith [hz j])
  have hroot := fusion_rootedCoulombMass_lower γ u μ α z αinf
  apply le_trans ?_ hroot
  simpa only [show (2 : ℝ) + 2 = 4 by norm_num,
    show (((2 : ℝ) + 1 : ℝ) : ℂ) = 3 by norm_num, mul_assoc] using
    mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)))) hmass

/-- Every nonpositive power of the rooted mass is dominated by a fixed-disk inverse power. -/
theorem fusion_rootedMass_inverse_domination {N : ℕ} (γ : ℝ) (u : ℂ) (μ : Measure ℂ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (s : ℝ) (hs : s ≤ 0) :
    ENNReal.rpow (coulombMass γ (gmcRootedMeasure γ u μ) α z αinf) s ≤
      ENNReal.rpow
        (ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
          (ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
            ENNReal.ofReal ((4 : ℝ) ^ (-|γ * αinf|)))) s *
        ENNReal.rpow (μ (Metric.ball (3 : ℂ) (1 / 8))) s := by
  have hc0 : (ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
      (ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((4 : ℝ) ^ (-|γ * αinf|)))) ≠ 0 := by
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    · apply mul_ne_zero <;> exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hct : (ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
      (ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((4 : ℝ) ^ (-|γ * αinf|)))) ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have h := ennreal_rpow_antitone_of_nonpos
    (fusion_rootedMass_disk_lower γ u μ α z αinf hz) hs
  rwa [ennreal_mul_rpow_of_ne_zero_ne_top _ _ hc0 hct] at h

/-- The fixed-disk domination gives a uniform finite inverse moment for all rooting points. -/
theorem fusion_rootedMass_inverse_moment_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ} (α : Fin N → ℝ) (αinf s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (u : ℂ) (z : Fin N → ℂ), (∀ j, ‖z j‖ ≤ 1) →
      (∫⁻ ω, ENNReal.rpow (coulombMass γ (gmcRootedMeasure γ u (M ω)) α z αinf) s ∂P) ≤ C := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-γ ^ 2 * Real.log 2)) *
    (ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
      ENNReal.ofReal ((4 : ℝ) ^ (-|γ * αinf|)))
  have hc0 : c ≠ 0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    · apply mul_ne_zero <;> exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hBm : AEMeasurable (fun ω => M ω (Metric.ball (3 : ℂ) (1 / 8))) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet
  have hfin := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM
    3 (1 / 8) (by norm_num) le_rfl s (lt_of_le_of_lt hs (by positivity))
  refine ⟨ENNReal.rpow c s * gmcMassMoment P M (Metric.ball (3 : ℂ) (1 / 8)) s,
    ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc0 hct).lt_top hfin, ?_⟩
  intro u z hz
  calc
    _ ≤ ∫⁻ ω, ENNReal.rpow c s * ENNReal.rpow (M ω (Metric.ball (3 : ℂ) (1 / 8))) s ∂P :=
      lintegral_mono fun ω => fusion_rootedMass_inverse_domination γ u (M ω) α z αinf hz s hs
    _ = _ := by
      simp only [ENNReal.rpow_eq_pow]
      rw [lintegral_const_mul'' _ (hBm.pow_const s)]
      rfl

end DOZZ.Proofs
