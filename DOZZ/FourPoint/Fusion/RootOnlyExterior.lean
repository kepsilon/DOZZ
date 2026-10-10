/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingRootExterior
public import DOZZ.FourPoint.Fusion.RootedMass
public import DOZZ.FourPoint.Fusion.MovingRootFiniteness
import DOZZ.GMC.Construction.RootedMeasureKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Domination away from the colliding roots -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Outside a fixed disk, the moving rooted mass converges for every measure whose limiting
rooted kernel is integrable. -/
theorem fusion_rootOnlyKernel_exterior_tendsto (γ α₁ α₂ α₃ : ℝ) (y : ℂ) (μ : Measure ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hfin : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
      Real.exp (γ ^ 2 * gffKernel 0 x)) ∂μ) < ⊤) :
    Tendsto (fun z : ℂ => ∫⁻ x in {x : ℂ | δ ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
          Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂μ) (nhds 0)
      (nhds (∫⁻ x in {x : ℂ | δ ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
          Real.exp (γ ^ 2 * gffKernel 0 x)) ∂μ)) := by
  let F : ℂ → ℂ → ℝ≥0∞ := fun z x => ENNReal.ofReal
    (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel (y * z) x))
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2)))
  have hm : ∀ z, Measurable (F z) := by
    intro z
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
        (f := fun x : ℂ => ((0 : ℂ), x)) (measurable_const.prodMk measurable_id)
    · exact (measurable_const.mul (measurable_pointRootPotential.comp
        (measurable_const.prodMk measurable_id))).exp
  have hzlim : Tendsto (fun z : ℂ => ‖z‖) (nhds 0) (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.continuousAt (x := (0 : ℂ))).tendsto
  have hulim : Tendsto (fun z : ℂ => ‖y * z‖) (nhds 0) (nhds 0) := by
    have hc : Continuous (fun z : ℂ => ‖y * z‖) := by fun_prop
    simpa only [mul_zero, norm_zero] using (hc.continuousAt (x := (0 : ℂ))).tendsto
  have hev : ∀ᶠ z : ℂ in nhds 0, ‖z‖ < δ ∧ ‖y * z‖ < δ / 2 ∧ ‖y * z‖ < 1 :=
    (hzlim.eventually_lt_const hδ).and
      ((hulim.eventually_lt_const (half_pos hδ)).and (hulim.eventually_lt_const zero_lt_one))
  apply tendsto_lintegral_filter_of_dominated_convergence (fun x => C * F 0 x)
  · exact Eventually.of_forall hm
  · filter_upwards [hev] with z hz
    filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hδ hx))
    have h := ENNReal.ofReal_le_ofReal (fusion_rootedKernel_exterior_bound γ α₁ α₂ α₃ 0 (y * z) x
      hx0 (by simp) (by linarith [hz.2.1]) hz.2.2.le)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at h
    simpa only [C, F, mul_zero] using h
  · rw [lintegral_const_mul _ (hm 0)]
    dsimp only [C, F]
    simp only [mul_zero]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hfin)).ne
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hδ hx))
    have hg : ContinuousAt (fun z : ℂ => gffKernel (y * z) x) 0 := by
      unfold gffKernel normPlus
      apply ContinuousAt.add
      · apply ContinuousAt.add
        · apply ContinuousAt.neg
          apply ContinuousAt.log
          · fun_prop
          · simpa only [mul_zero, zero_sub, norm_neg] using norm_ne_zero_iff.mpr hx0
        · apply ContinuousAt.log
          · fun_prop
          · simp
      · exact continuousAt_const
    have hc : Tendsto (fun z : ℂ => gammaHalfKernel γ α₁ α₂ α₃ 0 x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) (nhds 0)
        (nhds (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel (y * 0) x))) :=
      tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
        (by simpa only [Pi.mul_apply] using
          (show ContinuousAt (fun z : ℂ => γ ^ 2 * gffKernel (y * z) x) 0 from
            continuousAt_const.mul hg).tendsto))
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (by simpa only [mul_zero] using hc)

/-- The exterior part of the moving rooted GMC mass converges almost surely. -/
theorem fusion_rootOnly_exterior_real_tendsto_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (y : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, Tendsto (fun z : ℂ =>
      (∫⁻ x in {x : ℂ | δ ≤ ‖x‖}, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂M ω).toReal) (nhds 0)
      (nhds (∫⁻ x in {x : ℂ | δ ≤ ‖x‖}, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
        Real.exp (γ ^ 2 * gffKernel 0 x)) ∂M ω).toReal) := by
  filter_upwards [fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃] with ω hω
  have hfin := lt_of_le_of_lt (setLIntegral_le_lintegral {x : ℂ | δ ≤ ‖x‖} _) hω
  exact (ENNReal.tendsto_toReal hfin.ne).comp
    (fusion_rootOnlyKernel_exterior_tendsto γ α₁ α₂ α₃ y (M ω) δ hδ hω)

end DOZZ.Proofs
