/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.CutSqueezeLimit
import Mathlib.Tactic
/-! Remove the radial buffer after taking each fixed-buffer spatial limit. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

/-- Fixed-buffer polar limits, vanishing copied-model errors and the literal relative
kernel errors imply the original fusion limit in the spatial-then-buffer order. -/
theorem dual_buffer_relative_squeeze_tendsto {A : Type*} (l : Filter A)
    (f : A → ℝ) (g d e : ℝ → A → ℝ) (C : ℝ → ℝ) (L : ℝ)
    (hg : ∀ h, 0 < h → Tendsto (g h) l (𝓝 L))
    (hd : ∀ h, 0 < h → Tendsto (d h) l (𝓝 0))
    (he : ∀ h, 0 < h → Tendsto (e h) l (𝓝 (C h)))
    (hC : Tendsto C atTop (𝓝 0))
    (hb : ∀ h, 0 < h → ∀ᶠ x in l, |f x-g h x| ≤ d h x+e h x*(-g h x)) :
    Tendsto f l (𝓝 L) := by
  have hLower : Tendsto (fun h => L-(0+C h*(-L))) atTop (𝓝 L) := by
    simpa only [zero_mul, add_zero, sub_zero] using
      (tendsto_const_nhds (x := L)).sub ((tendsto_const_nhds (x := (0 : ℝ))).add
        (hC.mul (tendsto_const_nhds (x := -L))))
  have hUpper : Tendsto (fun h => L+(0+C h*(-L))) atTop (𝓝 L) := by
    simpa only [zero_mul, add_zero] using
      (tendsto_const_nhds (x := L)).add ((tendsto_const_nhds (x := (0 : ℝ))).add
        (hC.mul (tendsto_const_nhds (x := -L))))
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨h, hh, hc⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (hLower.eventually (lt_mem_nhds ha))).exists
    have ht := (hg h hh).sub ((hd h hh).add ((he h hh).mul (hg h hh).neg))
    filter_upwards [ht.eventually (lt_mem_nhds hc), hb h hh] with x hx hbound
    have hlow := (abs_le.mp hbound).1
    have hf : g h x-(d h x+e h x*(-g h x)) ≤ f x := by linarith only [hlow]
    exact hx.trans_le hf
  · intro b hb'
    obtain ⟨h, hh, hc⟩ := ((eventually_gt_atTop (0 : ℝ)).and
      (hUpper.eventually (gt_mem_nhds hb'))).exists
    have ht := (hg h hh).add ((hd h hh).add ((he h hh).mul (hg h hh).neg))
    filter_upwards [ht.eventually (gt_mem_nhds hc), hb h hh] with x hx hbound
    have hhigh := (abs_le.mp hbound).2
    have hf : f x ≤ g h x+(d h x+e h x*(-g h x)) := by linarith only [hhigh]
    exact hf.trans_lt hx

end DOZZ.Proofs
