/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterRegression
public import Mathlib.MeasureTheory.Group.Integral

/-! Translation of the lateral test kernel from an insertion disk to the origin. -/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- Translate a compact smooth test from the origin to the insertion disk. -/
noncomputable def translatedTest (z : ℂ) (ψ : TestFn) : TestFn :=
  ⟨fun w => ψ (w - z), ψ.contDiff.comp (contDiff_id.sub contDiff_const),
    ψ.hasCompactSupport.comp_homeomorph (Homeomorph.addRight (-z)), by simp⟩

theorem translatedTest_apply (z : ℂ) (ψ : TestFn) (w : ℂ) :
    translatedTest z ψ w = ψ (w - z) := rfl

/-- Translation carries the punctured unit test disk to the insertion disk. -/
noncomputable def translateDiskTest (z : ℂ) (ψ : offCenterTest 0) :
    offCenterTest z := by
  refine ⟨translatedTest z ψ.val, ?_⟩
  intro w hw
  have hsub : w - z ∈ tsupport (ψ.val : ℂ → ℝ) :=
    tsupport_comp_subset_preimage (ψ.val : ℂ → ℝ)
      (show Continuous (fun w : ℂ => w - z) by fun_prop) hw
  have h := ψ.property hsub
  simpa only [Set.mem_ofPred_eq, sub_zero] using h

/-- Translation leaves the lateral covariance kernel unchanged after moving both tests. -/
theorem translated_lateral_kernel (z : ℂ) (ψ χ : TestFn) :
    (∫ w : ℂ, translatedTest z ψ w * ∫ v : ℂ,
      (-Real.log ‖w - v‖ + Real.log (max ‖w - z‖ ‖v - z‖)) *
        translatedTest z χ v) =
      ∫ w : ℂ, ψ w * ∫ v : ℂ,
        (-Real.log ‖w - v‖ + Real.log (max ‖w‖ ‖v‖)) * χ v := by
  rw [← integral_add_right_eq_self (fun w : ℂ =>
    translatedTest z ψ w * ∫ v : ℂ,
      (-Real.log ‖w - v‖ + Real.log (max ‖w - z‖ ‖v - z‖)) *
        translatedTest z χ v) z]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    simp only [translatedTest_apply, add_sub_cancel_right]
    congr 1
    rw [← integral_add_right_eq_self (fun v : ℂ =>
      (-Real.log ‖w + z - v‖ + Real.log (max ‖w‖ ‖v - z‖)) * χ (v - z)) z]
    apply integral_congr_ae
    exact ae_of_all _ fun v => by simp only [add_sub_cancel_right, add_sub_add_right_eq_sub]

end DOZZ.Proofs
