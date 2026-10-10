/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.DiscardedAnnulus
public import DOZZ.FourPoint.Dual.SourceFullMoments
public import DOZZ.FourPoint.Dual.SeparatedSplit
public import DOZZ.FourPoint.Dual.SourceDecouplingLimit
public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
import Mathlib.Tactic
/-! Removing the actual intermediate annulus from the full inverse expectation. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The supplied full dual inverse expectation and the actual separated observable differ by
little-o at the fusion scale. Every positivity, finiteness and annular moment input is proved. -/
theorem dual_full_separated_inverse_littleO
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p ξ κ h : ℝ) (hp : 0 < p)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ*α₁ < 4) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hslack : κ < (1-ξ)*(4-γ*α₁)) :
    Tendsto (fun z : ℂ =>
      ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-p) ∂P).toReal-
        (dualSeparatedInverseMoment P M γ α₁ α₂ α₃ p z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal)/‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  let s := fun z : ℂ => Real.exp (-h)*‖z‖
  let r := fun z : ℂ => ‖z‖^(1-ξ)
  let I := fun z ω => ∫⁻ x in {x : ℂ | s z ≤ ‖x‖ ∧ ‖x‖ < r z},
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω
  let B := fun z ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let F := fun z ω => ∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω
  let S := fun z ω => (∫⁻ x in reflected_innerRegion (s z),
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)+
    (∫⁻ x in reflected_outerRegion (r z), ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)
  let R := fun z ω => ENNReal.ofReal p*(I z ω*B z ω^(-(p+1)))
  have ht := (dual_discarded_annulus_rooted_littleO P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ (p+1) ξ κ h (by linarith only [hp]) hβ hξ1 hslack).const_mul p
  simp only [mul_zero] at ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_ ht
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hpow (v : ℝ) (hv : 0 < v) : Tendsto (fun z : ℂ => ‖z‖^v) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hv.ne'] using
      ((Real.continuous_rpow_const hv.le).tendsto (0 : ℝ)).comp hn
  have hratio := (hpow ξ hξ).const_mul (Real.exp (-h))
  simp only [mul_zero] at hratio
  obtain ⟨Cb, _, hbi⟩ := dual_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ p hp.le
  obtain ⟨Cd, _, hdb⟩ := dual_deleted_disk_rooted_bound P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ (p+1) (by linarith only [hp]) hβ
  filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds zero_lt_one),
    (hpow (1-ξ) (sub_pos.mpr hξ1)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2)),
    (hpow ξ hξ).eventually (gt_mem_nhds zero_lt_one),
    hratio.eventually (gt_mem_nhds zero_lt_one)] with z hz0 hz hcut hsmall hsr
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hr : 0 < r z := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _
  have hs : 0 < s z := mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hz0)
  have hsr' : s z ≤ r z := by
    have hh : s z/r z < 1 := by simpa only [s,r,dual_restart_radius_ratio z hz0 h ξ] using hsr
    exact ((div_lt_one hr).mp hh).le
  have hzsep : ‖z‖ < r z := by
    have he : ‖z‖ = r z*‖z‖^ξ := by
      dsimp only [r]; rw [← Real.rpow_add (norm_pos_iff.mpr hz0), sub_add_cancel, Real.rpow_one]
    calc
      _ = _ := he
      _ < r z*1 := mul_lt_mul_of_pos_left hsmall hr
      _ = _ := mul_one _
  have hsource : ∀ᵐ ω ∂P, 0 < B z ω ∧ F z ω < ⊤ ∧ F z ω = S z ω+I z ω ∧ B z ω ≤ S z ω := by
    filter_upwards [dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hz.le (by linarith only [hcut]),
      dual_full_kernel_finite_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz0 hz1,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1,
      reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 0 (r z)] with ω hb hf h0 h1 hc
    have he := dual_kernel_separated_split γ α₁ α₂ α₃ (s z) (r z) hs hsr' z (M ω) h0 h1 hc
    have hB := dual_outerMass_eq_comparison_region γ α₁ α₂ α₃ ξ hγ.ne' z (M ω) h0 h1 hzsep hc
    refine ⟨hb.1,hf,he,?_⟩
    dsimp only [B,S]
    rw [hB]
    exact le_add_left le_rfl
  have hmM := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ₂ M hM
  have hk := (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hFm : AEMeasurable (F z) P := (Measure.measurable_lintegral hk).comp_aemeasurable hmM
  have hSm : AEMeasurable (S z) P := by
    have hi : MeasurableSet (reflected_innerRegion (s z)) :=
      (isOpen_lt continuous_const continuous_norm).measurableSet.inter
        (isOpen_lt continuous_norm continuous_const).measurableSet
    have ho : MeasurableSet (reflected_outerRegion (r z)) :=
      (isOpen_lt continuous_const continuous_norm).measurableSet.inter
        (isClosed_singleton.union isClosed_singleton).measurableSet.compl
    have hmi := (Measure.measurable_lintegral (hk.indicator hi)).comp_aemeasurable hmM
    have hmo := (Measure.measurable_lintegral (hk.indicator ho)).comp_aemeasurable hmM
    convert hmi.add hmo using 1
    funext ω
    simp only [S, Pi.add_apply, Function.comp_apply, lintegral_indicator hi, lintegral_indicator ho]
  have hSt : (∫⁻ ω, S z ω^(-p) ∂P) ≠ ⊤ := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply le_trans (lintegral_mono_ae (hsource.mono fun ω hh =>
      ennreal_rpow_antitone_of_nonpos hh.2.2.2 (neg_nonpos.mpr hp.le)))
    exact hbi z ξ hz.le (by linarith only [hcut])
  have hFt : (∫⁻ ω, F z ω^(-p) ∂P) ≠ ⊤ := ne_top_of_le_ne_top hSt
    (lintegral_mono_ae (hsource.mono fun ω hh => ennreal_rpow_antitone_of_nonpos
      (le_self_add.trans_eq hh.2.2.1.symm) (neg_nonpos.mpr hp.le)))
  have hIB : (∫⁻ ω, I z ω*B z ω^(-(p+1)) ∂P) ≠ ⊤ := by
    have hb := hdb z ξ (r z) hz.le (by linarith only [hcut]) hr hcut.le
    have hd : (∫⁻ ω, I z ω*B z ω^(-(p+1)) ∂P) ≤
        ENNReal.ofReal ((1+Real.exp h)^2)*
          (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) (r z),
            ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω)*
              B z ω^(-(p+1)) ∂P) := by
      calc
        _ ≤ ∫⁻ ω, (ENNReal.ofReal ((1+Real.exp h)^2)*
          (∫⁻ x in Metric.ball (0 : ℂ) (r z),
            ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω))*B z ω^(-(p+1)) ∂P :=
          lintegral_mono fun ω => mul_le_mul'
            (dual_discarded_annulus_mass_bound γ α₁ α₂ α₃ h (r z) z (M ω)) le_rfl
        _ = _ := by simp_rw [mul_assoc]; exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb)) hd
  have hRt : (∫⁻ ω, R z ω ∂P) ≠ ⊤ := by
    dsimp only [R]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIB
  have hSF : ∀ᵐ ω ∂P, S z ω^(-p) ≤ F z ω^(-p)+R z ω := by
    filter_upwards [hsource] with ω hh
    have hS0 : S z ω ≠ 0 := (hh.1.trans_le hh.2.2.2).ne'
    have hSt0 : S z ω ≠ ⊤ := ne_top_of_le_ne_top hh.2.1.ne
      (le_self_add.trans_eq hh.2.2.1.symm)
    have hIt : I z ω ≠ ⊤ := ne_top_of_le_ne_top hh.2.1.ne
      (le_add_self.trans_eq hh.2.2.1.symm)
    have hb := reflected_ennreal_inverse_add_bound p hp (S z ω) (I z ω) hS0 hSt0 hIt
    rw [← hh.2.2.1] at hb
    exact hb.trans (add_le_add le_rfl (by
      dsimp only [R]
      rw [mul_assoc]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
        (ennreal_rpow_antitone_of_nonpos hh.2.2.2 (by linarith only [hp] : -(p+1) ≤ 0)))))
  have hFS : ∀ᵐ ω ∂P, F z ω^(-p) ≤ S z ω^(-p)+R z ω :=
    hsource.mono fun ω hh => (ennreal_rpow_antitone_of_nonpos
      (le_self_add.trans_eq hh.2.2.1.symm) (neg_nonpos.mpr hp.le)).trans le_self_add
  have hb := reflected_lintegral_toReal_difference_bound P (fun ω => F z ω^(-p))
    (fun ω => S z ω^(-p)) (R z) (hFm.pow_const _) (hSm.pow_const _) hFt hSt hRt hFS hSF
  dsimp only [R] at hb
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hp.le] at hb
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) κ)]
  have hdiv := div_le_div_of_nonneg_right hb (Real.rpow_nonneg (norm_nonneg z) κ)
  simpa only [dualSeparatedInverseMoment, F, S, I, B, s, r, mul_div_assoc] using hdiv

end DOZZ.Proofs
