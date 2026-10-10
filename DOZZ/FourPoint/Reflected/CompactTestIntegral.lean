/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.WickReinsertion
/-! Identifying nonnegative compact real tests with their extended-real masses. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A nonnegative compact test has its ordinary real integral and its extended-real mass
identified under only local finiteness on its support. -/
theorem reflected_compact_test_integral_ofReal
    (μ : Measure ℂ) (K : Set ℂ) (_hK : IsCompact K) (hμ : μ K < ⊤)
    (f : BoundedContinuousFunction ℂ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hfK : tsupport (f : ℂ → ℝ) ⊆ K) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x in K, ENNReal.ofReal (f x) ∂μ := by
  let _ : IsFiniteMeasure (μ.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hμ⟩
  have he : (∫ x, f x ∂μ.restrict K) = ∫ x, f x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hfK h))
  rw [← he]
  exact ofReal_integral_eq_lintegral_ofReal (f.integrable (μ := μ.restrict K)) (ae_of_all _ hf)

end DOZZ.Proofs
