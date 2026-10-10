/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.RootOnlyMass
public import DOZZ.FourPoint.Fusion.RootOnlyExterior
public import DOZZ.FourPoint.Fusion.RootOnlySmallBall
import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # Measurability and finiteness of the moving-mass pieces -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem fusionRootOnlyBadMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) :
    AEMeasurable (fun ω => fusionRootOnlyBadMass γ α₁ α₂ α₃ y z δ (M ω)) P :=
  gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
    (fusionRootOnlyKernel_measurable _ _ _ _ _ _) _ Metric.isOpen_ball.measurableSet

theorem fusionRootOnlyGoodMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) :
    AEMeasurable (fun ω => fusionRootOnlyGoodMass γ α₁ α₂ α₃ y z δ (M ω)) P :=
  gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
    (fusionRootOnlyKernel_measurable _ _ _ _ _ _) _
    (measurableSet_le measurable_const measurable_norm)

/-- Exterior domination holds before taking expectations. -/
theorem fusionRootOnlyGoodMass_le (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (_hz : ‖z‖ ≤ δ) (hu : ‖y * z‖ ≤ δ / 2) (hu1 : ‖y * z‖ ≤ 1) (μ : Measure ℂ) :
    fusionRootOnlyGoodMass γ α₁ α₂ α₃ y z δ μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2))) *
        fusionRootOnlyGoodMass γ α₁ α₂ α₃ y 0 δ μ := by
  unfold fusionRootOnlyGoodMass
  rw [← lintegral_const_mul _ (fusionRootOnlyKernel_measurable γ α₁ α₂ α₃ y 0)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hδ hx))
  have h := ENNReal.ofReal_le_ofReal
    (fusion_rootedKernel_exterior_bound γ α₁ α₂ α₃ 0 (y * z) x hx0 (by simp)
      (by linarith) hu1)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at h
  simpa only [fusionRootOnlyKernel, mul_zero] using h

end DOZZ.Proofs
