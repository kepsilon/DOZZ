/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingMass
public import DOZZ.FourPoint.Fusion.MovingRootExterior
public import DOZZ.FourPoint.Fusion.MovingRootSmallBall
import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # Measurability and finiteness of the moving-mass pieces -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem fusionMovingBadMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) :
    AEMeasurable (fun ω => fusionMovingBadMass γ α₁ α₂ α₃ y z δ (M ω)) P :=
  gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
    (fusionMovingKernel_measurable _ _ _ _ _ _) _ Metric.isOpen_ball.measurableSet

theorem fusionMovingGoodMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) :
    AEMeasurable (fun ω => fusionMovingGoodMass γ α₁ α₂ α₃ y z δ (M ω)) P :=
  gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
    (fusionMovingKernel_measurable _ _ _ _ _ _) _
    (measurableSet_le measurable_const measurable_norm)

/-- Exterior domination holds before taking expectations. -/
theorem fusionMovingGoodMass_le (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hz : ‖z‖ ≤ δ) (hu : ‖y * z‖ ≤ δ / 2) (hu1 : ‖y * z‖ ≤ 1) (μ : Measure ℂ) :
    fusionMovingGoodMass γ α₁ α₂ α₃ y z δ μ ≤
      ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2))) *
        fusionMovingGoodMass γ α₁ α₂ α₃ y 0 δ μ := by
  unfold fusionMovingGoodMass
  rw [← lintegral_const_mul _ (fusionMovingKernel_measurable γ α₁ α₂ α₃ y 0)]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hδ hx))
  have h := ENNReal.ofReal_le_ofReal
    (fusion_rootedKernel_exterior_bound γ α₁ α₂ α₃ z (y * z) x hx0 (hz.trans hx)
      (by linarith) hu1)
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at h
  simpa only [fusionMovingKernel, mul_zero] using h

/-- A finite positive moment implies almost-sure finiteness of an extended mass. -/
theorem fusion_mass_finite_of_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {p : ℝ} (hp : 0 < p)
    (hfin : (∫⁻ ω, f ω ^ p ∂P) < ⊤) : ∀ᵐ ω ∂P, f ω ≠ ⊤ := by
  filter_upwards [ae_lt_top' (hf.pow_const p) hfin.ne] with ω hω
  intro he
  rw [he, ENNReal.top_rpow_of_pos hp] at hω
  exact lt_irrefl _ hω

end DOZZ.Proofs
