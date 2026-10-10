/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.Kernel
public import DOZZ.FourPoint.Fusion.RootedMass
import DOZZ.GMC.Construction.RootedMeasureKernel
import DOZZ.GMC.SharpMoments.SeibergMoment

/-! # The moving mass after rooting at `y*z` -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The real density in the scaled one-rooted fusion integrals. -/
noncomputable def fusionMovingKernel (γ α₁ α₂ α₃ : ℝ) (y z x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x * Real.exp (γ ^ 2 * gffKernel (y * z) x))

/-- The moving rooted mass, including both colliding insertion points. -/
noncomputable def fusionMovingMass (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x, fusionMovingKernel γ α₁ α₂ α₃ y z x ∂μ

/-- The part of the moving mass in the disk about zero. -/
noncomputable def fusionMovingBadMass (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ)
    (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball (0 : ℂ) δ, fusionMovingKernel γ α₁ α₂ α₃ y z x ∂μ

/-- The part of the moving mass outside the disk about zero. -/
noncomputable def fusionMovingGoodMass (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ)
    (μ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ x in {x : ℂ | δ ≤ ‖x‖}, fusionMovingKernel γ α₁ α₂ α₃ y z x ∂μ

theorem fusionMovingKernel_measurable (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) :
    Measurable (fusionMovingKernel γ α₁ α₂ α₃ y z) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.mul
  · exact (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp (f := fun x : ℂ => (z, x))
      (measurable_const.prodMk measurable_id)
  · exact (measurable_const.mul (measurable_pointRootPotential.comp
      (measurable_const.prodMk measurable_id))).exp

theorem fusionMovingMass_split (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (δ : ℝ) (μ : Measure ℂ) :
    fusionMovingMass γ α₁ α₂ α₃ y z μ =
      fusionMovingBadMass γ α₁ α₂ α₃ y z δ μ + fusionMovingGoodMass γ α₁ α₂ α₃ y z δ μ := by
  have hc : (Metric.ball (0 : ℂ) δ)ᶜ = {x : ℂ | δ ≤ ‖x‖} := by
    ext x
    simp only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq, not_lt]
  exact (lintegral_add_compl _ Metric.isOpen_ball.measurableSet).symm.trans
    (by rw [hc]; rfl)

/-- The real kernel mass is the Coulomb mass under the rooted measure. -/
theorem fusionMovingMass_eq_rooted (γ α₁ α₂ α₃ : ℝ) (y z : ℂ) (μ : Measure ℂ)
    (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    fusionMovingMass γ α₁ α₂ α₃ y z μ =
      coulombMass γ (gmcRootedMeasure γ (y * z) μ) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
  have hrz : gmcRootedMeasure γ (y * z) μ {z} = 0 := withDensity_absolutelyContinuous _ _ hz
  have hr0 : gmcRootedMeasure γ (y * z) μ {0} = 0 := withDensity_absolutelyContinuous _ _ h0
  have hr1 : gmcRootedMeasure γ (y * z) μ {1} = 0 := withDensity_absolutelyContinuous _ _ h1
  rw [fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z _ hrz hr0 hr1, gmcRootedMeasure]
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel (y * z) x))) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.mul (measurable_pointRootPotential.comp
      (measurable_const.prodMk measurable_id))).exp)
  have hk : Measurable (fun x : ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)) :=
    ENNReal.measurable_ofReal.comp ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (f := fun x : ℂ => (z, x)) (measurable_const.prodMk measurable_id))
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hk]
  apply lintegral_congr
  intro x
  dsimp [fusionMovingKernel]
  rw [mul_comm, ENNReal.ofReal_mul (Real.exp_nonneg _)]

theorem fusionMovingMass_eq_rooted_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) :
    ∀ᵐ ω ∂P, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) =
      coulombMass γ (gmcRootedMeasure γ (y * z) (M ω)) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
  filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hz h0 h1
  exact fusionMovingMass_eq_rooted γ α₁ α₂ α₃ y z (M ω) hz h0 h1

theorem fusionMovingMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (y z : ℂ) :
    AEMeasurable (fun ω => fusionMovingMass γ α₁ α₂ α₃ y z (M ω)) P :=
  gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _ (fusionMovingKernel_measurable _ _ _ _ _ _)

end DOZZ.Proofs
