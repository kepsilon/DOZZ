/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.OrderedCutSqueeze
/-! Both kernel coefficient bounds are removed after the spatial limit. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

theorem reflected_ordered_two_sided_squeeze {ι : Type*} (l : Filter ι)
    (f : ι → ℝ) (g k : ℝ → ι → ℝ) (L : ℝ) (Llo Lhi : ℝ → ℝ)
    (hg : ∀ H, 0 < H → Tendsto (g H) l (𝓝 (Llo H)))
    (hk : ∀ H, 0 < H → Tendsto (k H) l (𝓝 (Lhi H)))
    (hLlo : Tendsto Llo atTop (𝓝 L)) (hLhi : Tendsto Lhi atTop (𝓝 L))
    (hbound : ∀ H, 0 < H → ∀ᶠ i in l, g H i ≤ f i ∧ f i ≤ k H i) :
    Tendsto f l (𝓝 L) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨H,hHa,hH⟩ := ((hLlo.eventually (lt_mem_nhds ha)).and
      (eventually_gt_atTop (0 : ℝ))).exists
    filter_upwards [(hg H hH).eventually (lt_mem_nhds hHa),hbound H hH] with i hi hb
    exact hi.trans_le hb.1
  · intro b hb
    obtain ⟨H,hHb,hH⟩ := ((hLhi.eventually (gt_mem_nhds hb)).and
      (eventually_gt_atTop (0 : ℝ))).exists
    filter_upwards [(hk H hH).eventually (gt_mem_nhds hHb),hbound H hH] with i hi hu
    exact hu.2.trans_lt hi

end DOZZ.Proofs
