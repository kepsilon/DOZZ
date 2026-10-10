/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.DecorrelationError
public import DOZZ.FourPoint.TaylorKernelMass
/-! The literal full mass splits into inner, intermediate annulus and exterior masses. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_three_region_kernel_partition (μ : Measure ℂ) (s r : ℝ)
    (_hs : 0 < s) (hsr : s ≤ r) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hr : μ (Metric.sphere (0 : ℂ) r) = 0) (K : ℂ → ℝ≥0∞) (hK : Measurable K) :
    (∫⁻ x, K x ∂μ) = (∫⁻ x in reflected_innerRegion s, K x ∂μ)+
      (∫⁻ x in {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < r}, K x ∂μ)+
      ∫⁻ x in reflected_outerRegion r, K x ∂μ := by
  let U := reflected_innerRegion s
  let V := {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < r}
  let W := reflected_outerRegion r
  have hU : MeasurableSet U := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hV : MeasurableSet V := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hW : MeasurableSet W := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_insert.mpr (measurableSet_singleton (1 : ℂ)) : MeasurableSet ({0,1} : Set ℂ)).compl
  have he : K =ᵐ[μ] (fun x => U.indicator K x+V.indicator K x+W.indicator K x) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0,measure_eq_zero_iff_ae_notMem.mp h1,
      measure_eq_zero_iff_ae_notMem.mp hr] with x hx0 hx1 hxr
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr (by simpa only [mem_singleton_iff] using hx0)
    have hxne : ‖x‖ ≠ r := by simpa only [Metric.mem_sphere,dist_zero_right] using hxr
    have hx1' : x ≠ 1 := by simpa only [mem_singleton_iff] using hx1
    have hx0' : x ≠ 0 := norm_pos_iff.mp hn
    by_cases hxs : ‖x‖ < s
    · have hUx : x ∈ U := ⟨hn,hxs⟩
      have hVx : x ∉ V := fun hx => (not_le.mpr hxs) hx.1
      have hWx : x ∉ W := fun hx => (not_lt.mpr (hxs.le.trans hsr)) hx.1
      simp only [indicator_of_mem hUx,indicator_of_notMem hVx,indicator_of_notMem hWx,add_zero]
    · have hUx : x ∉ U := fun hx => hxs hx.2
      by_cases hxr' : ‖x‖ < r
      · have hVx : x ∈ V := ⟨le_of_not_gt hxs,hxr'⟩
        have hWx : x ∉ W := fun hx => (not_lt.mpr hxr'.le) hx.1
        simp only [indicator_of_notMem hUx,indicator_of_mem hVx,indicator_of_notMem hWx,zero_add,add_zero]
      · have hrx : r < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hxr') hxne.symm
        have hVx : x ∉ V := fun hx => hxr' hx.2
        have hWx : x ∈ W := ⟨hrx,by simp [hx0',hx1']⟩
        simp only [indicator_of_notMem hUx,indicator_of_notMem hVx,indicator_of_mem hWx,zero_add]
  have hab : Measurable (fun x => U.indicator K x+V.indicator K x) :=
    (hK.indicator hU).add (hK.indicator hV)
  rw [lintegral_congr_ae he,lintegral_add_left hab,
    lintegral_add_left (hK.indicator hU),lintegral_indicator hU,lintegral_indicator hV,
    lintegral_indicator hW]

theorem reflected_source_three_region_partition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ ξ s : ℝ)
    (z : ℂ) (hs : 0 < s) (hsr : s ≤ ‖z‖^(1-ξ)) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) ![-γ/2,α₁,α₂] ![z,0,1] α₃ =
      (∫⁻ x in reflected_innerRegion s, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)+
      (∫⁻ x in {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)+
      ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω := by
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1,
    reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 0 (‖z‖^(1-ξ)),
    gammaHalfMass_eq_coulombMass_ae P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ z] with ω h0 h1 hr he
  rw [← he]
  exact reflected_three_region_kernel_partition (M ω) s (‖z‖^(1-ξ)) hs hsr h0 h1 hr _
    (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal

end DOZZ.Proofs
