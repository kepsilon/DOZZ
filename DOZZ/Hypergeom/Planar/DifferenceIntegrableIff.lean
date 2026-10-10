/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.DifferenceIntegrable
public import DOZZ.Hypergeom.Planar.DifferenceAsymptotics

/-! Exact absolute-integrability criterion for the planar difference kernel. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

theorem planar_difference_integrable_iff (k β : ℝ) (hk : 0 < k)
    (z : ℂ) (hz : z ≠ 0) :
    Integrable (DOZZ.planarDifferenceKernel k β z) volume ↔
      k + 1 < β ∧ β < 2 := by
  constructor
  · intro hK
    have hβ₂ := planarDifferenceKernel_local_exponent_gt_neg_two k β hk z hz hK
    have htail : k + 1 < β := by
      by_cases hk₂ : k < 2
      · have hexp := planarDifferenceKernel_tail_exponent_lt k β hk hk₂ z hz hK
        linarith
      · have hk₁ : 1 ≤ k := by linarith
        have hexp := planarDifferenceKernel_tail_exponent_lt_of_ge_one k β hk₁ z hz hK
        linarith
    exact ⟨htail, hβ₂⟩
  · rintro ⟨hβtail, hβ₂⟩
    have hkβ : k < β := by linarith
    exact integrable_planarDifferenceKernel k β hk hkβ hβ₂ hβtail z

end DOZZ.Proofs
