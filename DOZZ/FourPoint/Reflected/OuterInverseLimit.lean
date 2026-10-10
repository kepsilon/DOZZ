/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.OuterInverseGuard
import Mathlib.Tactic

/-! # Dominated convergence of the actual reflected outer inverse moments -/
public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Every inverse order converges, with a fixed exterior disk providing an integrable majorant. -/
theorem reflected_outerMass_inverse_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ q : ℝ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁ - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ => ∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (∫⁻ ω, rho γ (M ω) (α₁ - γ / 2) α₂ α₃ ^ (-q) ∂P)) := by
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  let w : ℝ := (2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-γ / 2, α₁, α₂] : Fin 3 → ℝ) i|) *
    (4 : ℝ) ^ (-|γ * α₃|)
  let G : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (w ^ (-q)) *
    M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q)
  have hw : 0 < w := by dsimp only [w]; positivity
  have hn : Tendsto (fun z : ℂ => ‖z‖) l (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ z in l, ‖z‖ < 1 := hn.eventually (gt_mem_nhds zero_lt_one)
  have hgeom : ∀ᶠ z in l, ‖z‖ ≤ 1 ∧ ‖z‖ ^ (1 - ξ) ≤ 1 ∧ ‖z‖ < ‖z‖ ^ (1 - ξ) := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with z hz hz0
    have hr := Real.rpow_le_rpow (norm_nonneg z) hz.le (sub_nonneg.mpr hξ₁.le)
    have hs := Real.rpow_lt_rpow_of_exponent_gt (norm_pos_iff.mpr hz0) hz
      (by linarith only [hξ] : 1 - ξ < 1)
    exact ⟨hz.le, by simpa only [Real.one_rpow] using hr,
      by simpa only [Real.rpow_one] using hs⟩
  have hbound : ∀ᶠ z in l, ∀ᵐ ω ∂P,
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ≤ G ω := by
    filter_upwards [hgeom] with z hz
    apply Eventually.of_forall
    intro ω
    have hlow := reflected_outerMass_fixed_disk_lower γ α₁ α₂ α₃ ξ (M ω) z hz.1 hz.2.1
    have hh : gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ≤
        (ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1 / 8))) ^ (-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hlow hq)
    have hf : M ω (Metric.ball (3 : ℂ) (1 / 8)) ≠ ⊤ := by
      let _ := hM.1 ω
      exact measure_ne_top _ _
    rwa [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hf,
      ENNReal.ofReal_rpow_of_pos hw] at hh
  have hfinite : (∫⁻ ω, G ω ∂P) ≠ ⊤ := by
    obtain ⟨C, _, hb⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hM
      (-q) (lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)) {(3 : ℂ)} isCompact_singleton
    have hb' := (hb 3 (Set.mem_singleton _) (1 / 8) (by norm_num) (by norm_num)).2
    dsimp only [G]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb')
  have hmeas : ∀ᶠ z in l, AEMeasurable
      (fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q)) P := by
    obtain ⟨M', hM', _, heq⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ₂ M hM
    filter_upwards [hgeom] with z hz
    let f : ℂ → ℝ≥0∞ := {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}.indicator
      (fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x))
    have hf : Measurable f := (ENNReal.measurable_ofReal.comp
      (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z)).indicator
      (isClosed_le continuous_const continuous_norm).measurableSet
    apply (((Measure.measurable_lintegral hf).comp hM').pow_const (-q)).aemeasurable.congr
    filter_upwards [heq,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1] with ω he h0 h1
    dsimp only [Function.comp_def]
    rw [← he, reflected_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ z (M ω) h0 h1 hz.2.2]
    rw [lintegral_indicator (isClosed_le continuous_const continuous_norm).measurableSet]
  have hlimit : ∀ᵐ ω ∂P, Tendsto
      (fun z : ℂ => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q)) l
      (nhds (rho γ (M ω) (α₁ - γ / 2) α₂ α₃ ^ (-q))) := by
    filter_upwards [reflected_outerMass_ae_tendsto P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hξ hξ₁ hα₁ hα₂ hα₃] with ω ht
    exact ENNReal.continuous_rpow_const.tendsto _ |>.comp ht
  exact tendsto_lintegral_filter_of_dominated_convergence' G hmeas hbound hfinite hlimit

end DOZZ.Proofs
