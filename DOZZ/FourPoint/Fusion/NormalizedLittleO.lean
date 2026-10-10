/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import Mathlib.Analysis.Complex.Basic

/-! # Passing from a normalized complex limit to the little-o convention `IsComplexLittleOAtZero` -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- A normalized complex limit gives the literal norm little-o remainder. -/
theorem fusion_littleO_of_normalized_tendsto (κ : ℝ) (F : ℂ → ℂ) (C : ℂ)
    (h : Tendsto (fun z => F z / (‖z‖ ^ κ : ℝ)) (nhdsWithin 0 {0}ᶜ) (nhds C)) :
    IsComplexLittleOAtZero κ (fun z => F z - C * (‖z‖ ^ κ : ℝ)) := by
  have hd := h.sub (tendsto_const_nhds (x := C))
  have hn := continuous_norm.continuousAt.tendsto.comp hd
  simp only [sub_self, norm_zero, Function.comp_def] at hn
  have heq : (fun z : ℂ => ‖F z / (‖z‖ ^ κ : ℝ) - C‖) =ᶠ[nhdsWithin 0 {0}ᶜ]
      (fun z => ‖F z - C * (‖z‖ ^ κ : ℝ)‖ / ‖z‖ ^ κ) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
    have hr : 0 < ‖z‖ ^ κ := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) κ
    have hrC : ((‖z‖ ^ κ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    have halg (a b c : ℂ) (hb : b ≠ 0) : a / b - c = (a - c * b) / b := by
      rw [sub_div, mul_div_cancel_right₀ _ hb]
    rw [halg _ _ _ hrC, norm_div, Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hs : ({z : ℂ | z ≠ 0}) = {0}ᶜ := by ext z; simp
  unfold IsComplexLittleOAtZero
  rw [hs]
  exact hn.congr' heq

/-- The norm little-o convention also gives convergence of the signed complex quotient. -/
theorem fusion_normalized_tendsto_of_littleO (κ : ℝ) (F : ℂ → ℂ)
    (h : IsComplexLittleOAtZero κ F) :
    Tendsto (fun z => F z / (‖z‖ ^ κ : ℝ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hs : ({z : ℂ | z ≠ 0}) = {0}ᶜ := by ext z; simp
  unfold IsComplexLittleOAtZero at h
  rw [hs] at h
  simpa only [norm_div, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using h

end DOZZ.Proofs
