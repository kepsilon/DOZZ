/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.Kernel
public import DOZZ.FourPoint.Fusion.RootedMass
public import DOZZ.FourPoint.Fusion.MovingRootFiniteness
import DOZZ.GMC.Construction.RootedMeasureKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Domination away from the colliding roots -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The rooting density as a product of distance powers away from the diagonal. -/
theorem fusion_rootDensity_formula (γ : ℝ) (u x : ℂ) (hxu : x ≠ u) :
    Real.exp (γ ^ 2 * gffKernel u x) =
      normPlus u ^ (γ ^ 2) * normPlus x ^ (γ ^ 2) * ‖x - u‖ ^ (-γ ^ 2) := by
  have hu : 0 < normPlus u := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hx : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < ‖x - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu)
  rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hd,
    ← Real.exp_add, ← Real.exp_add, gffKernel, norm_sub_rev]
  congr 1
  ring

/-- The distance powers are bounded by the fused zero-root power away from a collision. -/
theorem fusion_exterior_power_bound (a b c k : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hk : 0 ≤ k) (hca : c ≤ 2 * a) (hab : a / 2 ≤ b) :
    c ^ k * b ^ (-(2 * k)) ≤ (2 : ℝ) ^ (3 * k) * a ^ (-k) := by
  have hc' : c ^ k ≤ (2 * a) ^ k := Real.rpow_le_rpow hc hca hk
  have hb' : b ^ (-(2 * k)) ≤ (a / 2) ^ (-(2 * k)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hab (by linarith)
  calc
    _ ≤ (2 * a) ^ k * (a / 2) ^ (-(2 * k)) :=
      mul_le_mul hc' hb' (Real.rpow_nonneg hb.le _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha.le,
        Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 2),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul]
      calc
        _ = ((2 : ℝ) ^ k * (2 : ℝ) ^ (2 * k)) * (a ^ k * a ^ (-(2 * k))) := by ring
        _ = (2 : ℝ) ^ (k + 2 * k) * a ^ (k + -(2 * k)) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2), ← Real.rpow_add ha]
        _ = _ := by congr 2 <;> ring

/-- Moving rooted kernels are dominated by the limiting kernel outside a fixed disk. -/
theorem fusion_rootedKernel_exterior_bound (γ α₁ α₂ α₃ : ℝ) (z u x : ℂ)
    (hx : x ≠ 0) (hz : ‖z‖ ≤ ‖x‖) (hu : ‖u‖ ≤ ‖x‖ / 2) (hu1 : ‖u‖ ≤ 1) :
    gammaHalfKernel γ α₁ α₂ α₃ z x * Real.exp (γ ^ 2 * gffKernel u x) ≤
      (2 : ℝ) ^ (3 * (γ ^ 2 / 2)) *
        (gammaHalfKernel γ α₁ α₂ α₃ 0 x * Real.exp (γ ^ 2 * gffKernel 0 x)) := by
  have ha : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hb : ‖x‖ / 2 ≤ ‖x - u‖ := by
    have h := norm_sub_norm_le x u
    linarith
  have hxu : x ≠ u := by
    intro he
    rw [he] at hu
    have hu0 : 0 < ‖u‖ := by simpa [he] using ha
    linarith
  have hc : ‖x - z‖ ≤ 2 * ‖x‖ := by
    have h := norm_sub_le x z
    linarith
  have hm := fusion_exterior_power_bound ‖x‖ ‖x - u‖ ‖x - z‖ (γ ^ 2 / 2)
    ha (norm_pos_iff.mpr (sub_ne_zero.mpr hxu)) (norm_nonneg _) (by positivity) hc hb
  have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpx : normPlus u = 1 := max_eq_left hu1
  rw [fusion_rootDensity_formula γ u x hxu, hpx, Real.one_rpow, one_mul,
    fusion_rootDensity_formula γ 0 x hx]
  simp only [normPlus, norm_zero, max_eq_left zero_le_one, Real.one_rpow, one_mul,
    gammaHalfKernel, sub_zero]
  have hpow : ‖x‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ ^ 2) = ‖x‖ ^ (-(γ ^ 2 / 2)) := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  have he : -(2 * (γ ^ 2 / 2)) = -γ ^ 2 := by ring
  rw [he] at hm
  have hf : 0 ≤ normPlus x ^ (γ * (α₁ + α₂ + α₃ - γ / 2)) * normPlus x ^ (γ ^ 2) /
      (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂)) := by positivity
  have h := mul_le_mul_of_nonneg_right hm hf
  have heq : ‖x‖ ^ (-(γ ^ 2 / 2)) = ‖x‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ ^ 2) := hpow.symm
  rw [heq] at h
  unfold normPlus at h
  convert h using 1 <;> ring

/-- Outside a fixed disk, the moving rooted mass converges for every measure whose limiting
rooted kernel is integrable. -/
theorem fusion_rootedKernel_exterior_tendsto (γ α₁ α₂ α₃ : ℝ) (y : ℂ) (μ : Measure ℂ)
    (δ : ℝ) (hδ : 0 < δ)
    (hfin : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
      Real.exp (γ ^ 2 * gffKernel 0 x)) ∂μ) < ⊤) :
    Tendsto (fun z : ℂ => ∫⁻ x in {x : ℂ | δ ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x *
          Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂μ) (nhds 0)
      (nhds (∫⁻ x in {x : ℂ | δ ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
          Real.exp (γ ^ 2 * gffKernel 0 x)) ∂μ)) := by
  let F : ℂ → ℂ → ℝ≥0∞ := fun z x => ENNReal.ofReal
    (gammaHalfKernel γ α₁ α₂ α₃ z x * Real.exp (γ ^ 2 * gffKernel (y * z) x))
  let C : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (3 * (γ ^ 2 / 2)))
  have hm : ∀ z, Measurable (F z) := by
    intro z
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.mul
    · exact (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp (f := fun x : ℂ => (z, x))
        (measurable_const.prodMk measurable_id)
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
    have h := ENNReal.ofReal_le_ofReal (fusion_rootedKernel_exterior_bound γ α₁ α₂ α₃ z (y * z) x
      hx0 (hz.1.le.trans hx) (by linarith [hz.2.1]) hz.2.2.le)
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)] at h
    simpa only [C, F, mul_zero] using h
  · rw [lintegral_const_mul _ (hm 0)]
    dsimp only [C, F]
    simp only [mul_zero]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hfin)).ne
  · filter_upwards [ae_restrict_mem (measurableSet_le measurable_const measurable_norm)] with x hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hδ hx))
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (fusion_rootedKernel_tendsto γ α₁ α₂ α₃ y x hx0)

/-- The exterior part of the moving rooted GMC mass converges almost surely. -/
theorem fusion_movingRoot_exterior_real_tendsto_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (y : ℂ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, Tendsto (fun z : ℂ =>
      (∫⁻ x in {x : ℂ | δ ≤ ‖x‖}, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x *
        Real.exp (γ ^ 2 * gffKernel (y * z) x)) ∂M ω).toReal) (nhds 0)
      (nhds (∫⁻ x in {x : ℂ | δ ≤ ‖x‖}, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x *
        Real.exp (γ ^ 2 * gffKernel 0 x)) ∂M ω).toReal) := by
  filter_upwards [fusion_limitingRootedKernel_finite_ae P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ hα₁ hα₂ hα₃] with ω hω
  have hfin := lt_of_le_of_lt (setLIntegral_le_lintegral {x : ℂ | δ ≤ ‖x‖} _) hω
  exact (ENNReal.tendsto_toReal hfin.ne).comp
    (fusion_rootedKernel_exterior_tendsto γ α₁ α₂ α₃ y (M ω) δ hδ hω)

end DOZZ.Proofs
