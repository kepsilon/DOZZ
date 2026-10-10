/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import Mathlib.Tactic

/-! # Remainder calculus at the punctured complex origin -/

public section

open Filter Topology

namespace DOZZ.Proofs

/-- The complex norm convention agrees with a signed real remainder limit. -/
theorem isComplexLittleOAtZero_ofReal_iff (κ : ℝ) (f : ℂ → ℝ) :
    IsComplexLittleOAtZero κ (fun z => (f z : ℂ)) ↔
      Tendsto (fun z => f z / ‖z‖ ^ κ)
        (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  unfold IsComplexLittleOAtZero
  conv_rhs => rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg
    (norm_nonneg _) _)]

/-- Addition preserves the little-o remainder convention. -/
theorem IsComplexLittleOAtZero.add {κ : ℝ} {f g : ℂ → ℂ}
    (hf : DOZZ.IsComplexLittleOAtZero κ f) (hg : DOZZ.IsComplexLittleOAtZero κ g) :
    DOZZ.IsComplexLittleOAtZero κ (fun z => f z + g z) := by
  unfold DOZZ.IsComplexLittleOAtZero at hf hg ⊢
  apply squeeze_zero (fun z => div_nonneg (norm_nonneg _) (Real.rpow_nonneg
    (norm_nonneg _) _))
  · intro z
    calc
      ‖f z + g z‖ / ‖z‖ ^ κ ≤ (‖f z‖ + ‖g z‖) / ‖z‖ ^ κ :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (Real.rpow_nonneg (norm_nonneg _) _)
      _ = ‖f z‖ / ‖z‖ ^ κ + ‖g z‖ / ‖z‖ ^ κ := add_div _ _ _
  · simpa only [add_zero] using hf.add hg

/-- Multiplication by a fixed scalar preserves the little-o convention. -/
theorem IsComplexLittleOAtZero.const_mul {κ : ℝ} {f : ℂ → ℂ}
    (hf : DOZZ.IsComplexLittleOAtZero κ f) (c : ℂ) :
    DOZZ.IsComplexLittleOAtZero κ (fun z => c * f z) := by
  unfold DOZZ.IsComplexLittleOAtZero at hf ⊢
  simpa only [norm_mul, mul_div_assoc, mul_zero] using hf.const_mul ‖c‖

/-- A strictly higher power of the radius is negligible at the reflected scale. -/
theorem reflected_radius_power_ratio_tendsto (κ η : ℝ) (hη : κ < η) :
    Tendsto (fun z : ℂ => ‖z‖ ^ η / ‖z‖ ^ κ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  have he : 0 < η - κ := sub_pos.mpr hη
  have hpow := ((Real.continuous_rpow_const he.le).comp continuous_norm).tendsto
    (0 : ℂ)
  have ht : Tendsto (fun z : ℂ => ‖z‖ ^ (η - κ))
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
    simpa only [Function.comp_def, norm_zero, Real.zero_rpow he.ne'] using hpow.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact Real.rpow_sub (norm_pos_iff.mpr hz) η κ

/-- Uniform power bounds suffice for every decorrelation and buffer remainder. -/
theorem isComplexLittleOAtZero_of_norm_le_power {κ η C : ℝ} {f : ℂ → ℂ}
    (hη : κ < η)
    (hb : ∀ᶠ z in nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}, ‖f z‖ ≤ C * ‖z‖ ^ η) :
    DOZZ.IsComplexLittleOAtZero κ f := by
  unfold DOZZ.IsComplexLittleOAtZero
  have ht := (reflected_radius_power_ratio_tendsto κ η hη).const_mul C
  apply squeeze_zero' (Filter.Eventually.of_forall (fun z =>
    div_nonneg (norm_nonneg (f z)) (Real.rpow_nonneg (norm_nonneg z) κ)))
  · filter_upwards [hb] with z hz
    calc
      ‖f z‖ / ‖z‖ ^ κ ≤ (C * ‖z‖ ^ η) / ‖z‖ ^ κ :=
        div_le_div_of_nonneg_right hz (Real.rpow_nonneg (norm_nonneg z) κ)
      _ = C * (‖z‖ ^ η / ‖z‖ ^ κ) := mul_div_assoc _ _ _
  · simpa only [mul_zero] using ht

end DOZZ.Proofs
