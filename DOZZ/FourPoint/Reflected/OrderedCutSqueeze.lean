/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
/-! The cutoff is removed only after the spatial limit in the signed Williams squeeze. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

/-- A common lower limit and fixed-cut upper limits tending to it determine the spatial
limit, even when each fixed-cut error has a cutoff-dependent constant. -/
theorem reflected_ordered_cut_squeeze {ι : Type*} (l : Filter ι)
    (f g : ι → ℝ) (k error : ℝ → ι → ℝ) (L : ℝ) (Lcut : ℝ → ℝ)
    (hg : Tendsto g l (𝓝 L)) (hk : ∀ H, 0 < H → Tendsto (k H) l (𝓝 (Lcut H)))
    (he : ∀ H, 0 < H → Tendsto (error H) l (𝓝 0))
    (hL : Tendsto Lcut atTop (𝓝 L))
    (hlow : ∀ᶠ i in l, g i ≤ f i)
    (hupp : ∀ H, 0 < H → ∀ᶠ i in l, f i ≤ k H i+error H i) :
    Tendsto f l (𝓝 L) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hg.eventually (lt_mem_nhds ha),hlow] with i hi hl
    exact hi.trans_le hl
  · intro b hb
    obtain ⟨H,hHb,hH⟩ := ((hL.eventually (gt_mem_nhds hb)).and (eventually_gt_atTop (0 : ℝ))).exists
    have ht : Tendsto (fun i => k H i+error H i) l (𝓝 (Lcut H)) := by
      simpa only [add_zero] using (hk H hH).add (he H hH)
    filter_upwards [ht.eventually (gt_mem_nhds hHb),hupp H hH] with i hi hu
    exact hu.trans_lt hi

end DOZZ.Proofs
