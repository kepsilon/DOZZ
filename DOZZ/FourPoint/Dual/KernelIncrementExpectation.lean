/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RelativeIncrement
import Mathlib.Tactic
/-! Integrated relative kernel errors are controlled by the finite signed polar increment. -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Integrate a kernel squeeze using only the retained inverse moment. The two inner
masses can depend on the entire sample; no independence or inner first moment is needed. -/
theorem dual_negative_increment_kernel_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (p θlo θhi : ℝ) (hp : 0 < p) (hlo : 0 ≤ θlo) (hhi : 0 ≤ θhi)
    (A t u : Ω → ℝ) (hA : ∀ᵐ ω ∂P, 0 < A ω) (ht : ∀ᵐ ω ∂P, 0 ≤ t ω)
    (hsqueeze : ∀ᵐ ω ∂P, θlo*t ω ≤ u ω ∧ u ω ≤ θhi*t ω)
    (hAm : AEMeasurable A P) (htm : AEMeasurable t P) (hum : AEMeasurable u P)
    (hInv : Integrable (fun ω => (A ω)^(-p)) P) :
    |(∫ ω, (A ω+u ω)^(-p)-(A ω)^(-p) ∂P)-
      (∫ ω, (A ω+t ω)^(-p)-(A ω)^(-p) ∂P)| ≤
      max |θlo-1| |θhi-1| * (∫ ω, (A ω)^(-p)-(A ω+t ω)^(-p) ∂P) := by
  have hu : ∀ᵐ ω ∂P, 0 ≤ u ω := by
    filter_upwards [ht, hsqueeze] with ω htω hs
    exact (mul_nonneg hlo htω).trans hs.1
  have hInt (v : Ω → ℝ) (hv : ∀ᵐ ω ∂P, 0 ≤ v ω) (hvm : AEMeasurable v P) :
      Integrable (fun ω => (A ω+v ω)^(-p)-(A ω)^(-p)) P := by
    have hm := ((hAm.add hvm).pow_const (-p)).sub (hAm.pow_const (-p))
    have hm' : AEStronglyMeasurable (fun ω => (A ω+v ω)^(-p)-(A ω)^(-p)) P := by
      convert hm.aestronglyMeasurable using 1
    apply hInv.mono' hm'
    filter_upwards [hA, hv] with ω hAω hvω
    simpa only [Real.norm_eq_abs] using
      dual_negative_increment_abs_le p (A ω) (v ω) hp.le hAω hvω
  have hit := hInt t ht htm
  have hiu := hInt u hu hum
  have hLoss : Integrable (fun ω => (A ω)^(-p)-(A ω+t ω)^(-p)) P := by
    convert hit.neg using 1
    ext ω
    change (A ω)^(-p)-(A ω+t ω)^(-p) = -((A ω+t ω)^(-p)-(A ω)^(-p))
    ring
  rw [← integral_sub hiu hit]
  have hb := norm_integral_le_of_norm_le
    (f := fun ω => ((A ω+u ω)^(-p)-(A ω)^(-p))-((A ω+t ω)^(-p)-(A ω)^(-p)))
    (hLoss.const_mul (max |θlo-1| |θhi-1|)) (by
      filter_upwards [hA, ht, hsqueeze] with ω hAω htω hs
      simpa only [Real.norm_eq_abs] using
        dual_negative_increment_kernel_squeeze p (A ω) (t ω) (u ω) θlo θhi
          hp hAω htω hlo hhi hs.1 hs.2)
  simpa only [Real.norm_eq_abs, integral_const_mul] using hb

end DOZZ.Proofs
