/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-! Signed inverse increments are dominated by the retained inverse moment. -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- A nonnegative added mass has an integrable signed inverse increment whenever the actual
retained inverse moment is integrable; no moment of the added mass is required. -/
theorem reflected_inverse_increment_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (p : ℝ) (hp : 0 < p)
    (A T : Ω → ℝ) (hA : ∀ᵐ ω ∂P, 0 < A ω) (hT : ∀ᵐ ω ∂P, 0 ≤ T ω)
    (hAm : AEMeasurable A P) (hTm : AEMeasurable T P)
    (hInv : Integrable (fun ω => (A ω)^(-p)) P) :
    Integrable (fun ω => (A ω+T ω)^(-p)-(A ω)^(-p)) P := by
  have hpow : Measurable (fun x : ℝ => x^(-p)) := by fun_prop
  have hm := ((hpow.comp_aemeasurable (hAm.add hTm)).sub
    (hpow.comp_aemeasurable hAm)).aestronglyMeasurable
  apply hInv.mono' hm
  filter_upwards [hA,hT] with ω hAω hTω
  have hneg : (A ω+T ω)^(-p)-(A ω)^(-p) ≤ 0 :=
    sub_nonpos.mpr (Real.rpow_le_rpow_of_nonpos hAω
      (le_add_of_nonneg_right hTω) (neg_nonpos.mpr hp.le))
  change ‖(A ω+T ω)^(-p)-(A ω)^(-p)‖ ≤ (A ω)^(-p)
  rw [Real.norm_eq_abs,abs_of_nonpos hneg,neg_sub]
  exact sub_le_self _ (Real.rpow_nonneg (hAω.le.trans (le_add_of_nonneg_right hTω)) _)

end DOZZ.Proofs
