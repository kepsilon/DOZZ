/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.KernelNorms
public import DOZZ.Hypergeom.Planar.TwoPointRpow

/-! Exact integrability tests for the two differentiated planar kernels. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

/-- Replace a singular quotient of two radial powers by a product away from the origin. -/
theorem integrable_two_point_rpow_div_iff (a b : ℝ) (z : ℂ) (hz : z ≠ 0) :
    Integrable (fun u : ℂ => ‖u - z‖ ^ b / ‖u‖ ^ a) volume ↔
      -2 < -a ∧ -2 < b ∧ -a + b < -2 := by
  have heq : (fun u : ℂ => ‖u - z‖ ^ b / ‖u‖ ^ a) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-a) * ‖u - z‖ ^ b) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with u hu
    have hnorm : 0 ≤ ‖u‖ := norm_nonneg u
    calc
      ‖u - z‖ ^ b / ‖u‖ ^ a = ‖u - z‖ ^ b * (‖u‖ ^ a)⁻¹ := by ring
      _ = ‖u‖ ^ (-a) * ‖u - z‖ ^ b := by
        rw [Real.rpow_neg hnorm]
        ring
  rw [integrable_congr heq]
  exact integrableOn_two_point_rpow_iff (-a) b z hz

private theorem measurable_norm_rpow_local (s : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ s) := by
  have hrepr : (fun u : ℂ => ‖u‖ ^ s) =
      fun u => if ‖u‖ = 0 then 0 ^ s else Real.exp (s * Real.log ‖u‖) := by
    funext u
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    · rw [ite_eq_right hu,
        Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) (by fun_prop)
  · exact measurable_const
  · fun_prop

private theorem measurable_rpow_of_nonneg_local {f : ℂ → ℝ} (hf : Measurable f)
    (hfn : ∀ u, 0 ≤ f u) (s : ℝ) : Measurable (fun u => f u ^ s) := by
  have hrepr : (fun u => f u ^ s) =
      fun u => if f u = 0 then 0 ^ s else Real.exp (s * Real.log (f u)) := by
    funext u
    by_cases hu : f u = 0
    · simp [hu]
    · rw [ite_eq_right hu, Real.rpow_def_of_pos (lt_of_le_of_ne (hfn u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) hf
  · exact measurable_const
  · fun_prop

/-- Exact integrability criterion for the mixed derivative kernel. -/
theorem integrable_planarMixedKernel_iff (k β : ℝ) (hk : 0 < k) (z : ℂ) (hz : z ≠ 0) :
    Integrable (DOZZ.planarMixedKernel k β z) volume ↔ k < β ∧ β < 2 := by
  change Integrable (fun u : ℂ => ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β) volume ↔ _
  rw [integrable_two_point_rpow_div_iff β (k - 2) z hz]
  constructor
  · rintro ⟨hβ, hk, hsum⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hkb, hβ⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-- Exact integrability criterion for the Wirtinger derivative kernel. -/
theorem integrable_planarWirtingerKernel_iff (k β : ℝ) (hk : 0 < k) (z : ℂ) (hz : z ≠ 0) :
    Integrable (DOZZ.planarWirtingerKernel k β z) volume ↔ k < β ∧ β < 2 := by
  have hnum : Measurable (fun u : ℂ => ‖u - z‖ ^ k) :=
    measurable_rpow_of_nonneg_local (by fun_prop) (fun u => norm_nonneg (u - z)) k
  have hden : Measurable (fun u : ℂ => ‖u‖ ^ β) :=
    measurable_rpow_of_nonneg_local (by fun_prop) (fun u => norm_nonneg u) β
  have hmeas : Measurable (DOZZ.planarWirtingerKernel k β z) := by
    change Measurable (fun u : ℂ =>
      ((‖u - z‖ ^ k : ℝ) : ℂ) / ((z - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ)))
    fun_prop
  have hstrong : AEStronglyMeasurable (DOZZ.planarWirtingerKernel k β z) volume :=
    hmeas.aestronglyMeasurable
  rw [← integrable_norm_iff hstrong]
  have heq : (fun u : ℂ => ‖DOZZ.planarWirtingerKernel k β z u‖) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume z] with u hu0 huz
    have hnorm := norm_planarWirtingerKernel_eq k β z u hu0 huz
    have hnorm0 : 0 ≤ ‖u‖ := norm_nonneg u
    calc
      ‖DOZZ.planarWirtingerKernel k β z u‖ =
          ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β := hnorm
      _ = ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := by
        rw [div_eq_mul_inv, Real.rpow_neg hnorm0]
        ring
  rw [integrable_congr heq]
  rw [integrableOn_two_point_rpow_iff (-β) (k - 2) z hz]
  constructor
  · rintro ⟨hβ, hk, hsum⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hkb, hβ⟩
    exact ⟨by linarith, by linarith, by linarith⟩

/-- The pair of exact integrability criteria for the two differentiated kernels. -/
theorem planar_derivative_integrable_iff (k β : ℝ) (hk : 0 < k)
    (z : ℂ) (hz : z ≠ 0) :
    (Integrable (DOZZ.planarWirtingerKernel k β z) volume ↔ k < β ∧ β < 2) ∧
      (Integrable (DOZZ.planarMixedKernel k β z) volume ↔ k < β ∧ β < 2) := by
  exact ⟨integrable_planarWirtingerKernel_iff k β hk z hz,
    integrable_planarMixedKernel_iff k β hk z hz⟩

end DOZZ.Proofs
