/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RealChargeBudget
public import DOZZ.GMC.SharpMoments.SeibergDecomp

/-! Fixed separated insertion geometry for the local analytic construction. -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- Distinct finitely many insertions admit one positive disk separation, bounded by `1/8`. -/
theorem separated_geometry {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 8 ∧ ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖ := by
  have esep : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖ := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    by_cases h : j = k
    · exact Filter.Eventually.of_forall (fun _ hne => (hne h).elim)
    · have hn : 0 < ‖z j - z k‖ := norm_pos_iff.mpr
        (sub_ne_zero.mpr (fun he => h (hz he)))
      filter_upwards [Ioo_mem_nhdsGT (half_pos hn)] with δ hδ
      intro _
      linarith [hδ.2]
  have eδ : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 (1 / 8) :=
    Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨δ, hδ, hs⟩ := (eδ.and esep).exists
  exact ⟨δ, hδ.1, hδ.2.le, hs⟩

end DOZZ.Proofs
