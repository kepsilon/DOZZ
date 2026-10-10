/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
/-! Two-stage signed squeezing for the Williams last-cut limit. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

/-- First take the spatial limit at each fixed cut, then send the cut level to infinity.
The proof retains the one-sided signed bounds rather than taking absolute values early. -/
theorem dual_cut_squeeze_tendsto {A : Type*} (l : Filter A)
    (f lower : A → ℝ) (upper error : ℝ → A → ℝ) (C : ℝ → ℝ) (L : ℝ)
    (hLower : Tendsto lower l (𝓝 L))
    (hUpper : ∀ c, Tendsto (fun x => upper c x + error c x) l (𝓝 (C c)))
    (hC : Tendsto C atTop (𝓝 L))
    (hBound : ∀ c, ∀ᶠ x in l, lower x ≤ f x ∧ f x ≤ upper c x + error c x) :
    Tendsto f l (𝓝 L) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [hLower.eventually (lt_mem_nhds ha), hBound 0] with x hx hb
    exact hx.trans_le hb.1
  · intro b hb
    obtain ⟨c, hc⟩ := (hC.eventually (gt_mem_nhds hb)).exists
    filter_upwards [(hUpper c).eventually (gt_mem_nhds hc), hBound c] with x hx hb
    exact hb.2.trans_lt hx

end DOZZ.Proofs
