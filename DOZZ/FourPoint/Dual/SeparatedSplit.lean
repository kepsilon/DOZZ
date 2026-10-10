/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SpatialBoundary
public import DOZZ.FourPoint.Reflected.SeparatedRegions
import Mathlib.Tactic
/-! The exact actual mass decomposition into inner, intermediate and exterior regions. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual full kernel mass splits into the two separated comparison masses plus the
literal intervening annulus. Only the null outer circle and null insertion roots are removed. -/
theorem dual_kernel_separated_split (γ α₁ α₂ α₃ s r : ℝ) (_hs : 0 < s) (hsr : s ≤ r)
    (z : ℂ) (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hc : μ (Metric.sphere (0 : ℂ) r) = 0) :
    (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ) =
      ((∫⁻ x in reflected_innerRegion s, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ)+
       (∫⁻ x in reflected_outerRegion r, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ))+
       ∫⁻ x in {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < r},
         ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  let k := fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)
  let D := {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < r}
  have hI : MeasurableSet (reflected_innerRegion s) :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have hO : MeasurableSet (reflected_outerRegion r) :=
    (isOpen_lt continuous_const continuous_norm).measurableSet.inter
      (isClosed_singleton.union isClosed_singleton).measurableSet.compl
  have hD : MeasurableSet D :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isOpen_lt continuous_norm continuous_const).measurableSet
  have he : k =ᵐ[μ] fun x =>
      ((reflected_innerRegion s).indicator k x+(reflected_outerRegion r).indicator k x)+D.indicator k x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0,
      measure_eq_zero_iff_ae_notMem.mp h1, measure_eq_zero_iff_ae_notMem.mp hc] with x hx0 hx1 hxc
    have hx0' : x ≠ 0 := by simpa only [mem_singleton_iff] using hx0
    have hx1' : x ≠ 1 := by simpa only [mem_singleton_iff] using hx1
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx0'
    have hxr : ‖x‖ ≠ r := by simpa only [Metric.mem_sphere, dist_zero_right] using hxc
    by_cases hxs : ‖x‖ < s
    · have hxxr : ‖x‖ < r := hxs.trans_le hsr
      have hix : x ∈ reflected_innerRegion s := ⟨hxp,hxs⟩
      have hox : x ∉ reflected_outerRegion r := fun hh => (not_lt_of_ge hxxr.le) hh.1
      have hdx : x ∉ D := fun hh => (not_le_of_gt hxs) hh.1
      simp only [indicator_of_mem hix, indicator_of_notMem hox, indicator_of_notMem hdx, add_zero]
    · have hsx : s ≤ ‖x‖ := le_of_not_gt hxs
      have hix : x ∉ reflected_innerRegion s := fun hh => hxs hh.2
      by_cases hxxr : ‖x‖ < r
      · have hdx : x ∈ D := ⟨hsx,hxxr⟩
        have hox : x ∉ reflected_outerRegion r := fun hh => (not_lt_of_ge hxxr.le) hh.1
        simp only [indicator_of_notMem hix, indicator_of_notMem hox, indicator_of_mem hdx,
          zero_add, add_zero]
      · have hrx : r < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hxxr) hxr.symm
        have hox : x ∈ reflected_outerRegion r := ⟨hrx, by simp [hx0',hx1']⟩
        have hdx : x ∉ D := fun hh => hxxr hh.2
        simp only [indicator_of_notMem hix, indicator_of_mem hox, indicator_of_notMem hdx,
          zero_add, add_zero]
  rw [lintegral_congr_ae he, lintegral_add_left]
  · rw [lintegral_add_left, lintegral_indicator hI, lintegral_indicator hO, lintegral_indicator hD]
    exact ((dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal.indicator hI)
  · exact ((dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal.indicator hI).add
      ((dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal.indicator hO)

end DOZZ.Proofs
