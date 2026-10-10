/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.Distributions.Gaussian.Real

/-! One-dimensional Gaussian integration by parts for the standard normal law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace DOZZ.Proofs

/-- Stein's identity for the standard normal law, with the integrability hypotheses required by
integration by parts against its density. -/
theorem gaussianReal_standard_stein
    (g g' : ℝ → ℝ)
    (hg : ∀ x, HasDerivAt g (g' x) x)
(hgp : Integrable (fun x => g x * (-x * gaussianPDFReal 0 1 x)) volume)
    (hg' : Integrable (fun x => g' x * gaussianPDFReal 0 1 x) volume)
    (hprod : Integrable (fun x => g x * gaussianPDFReal 0 1 x) volume) :
    ∫ x, x * g x ∂gaussianReal 0 1 = ∫ x, g' x ∂gaussianReal 0 1 := by
  have hpdf : ∀ x, HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
    intro x
    have hqbase := (((hasDerivAt_id x).pow 2).const_mul (- (1 / 2 : ℝ)))
    have hq0 : HasDerivAt (fun y : ℝ => (- (1 / 2 : ℝ)) * y ^ 2)
        ((- (1 / 2 : ℝ)) * (2 * x)) x := by
      convert hqbase using 1
      · ext y
        simp only [Pi.pow_apply, id_eq]
      · simp only [id_eq, Nat.reduceSub, pow_one]
        ring
    have hq : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      convert hq0 using 1
      · ext y
        ring
      · ring
    have he := (Real.hasDerivAt_exp (-x ^ 2 / 2)).comp x hq
    rw [gaussianPDFReal_def]
    convert he.const_mul (Real.sqrt (2 * Real.pi * (1 : ℝ≥0)))⁻¹ using 1 <;>
      simp [mul_assoc, mul_left_comm, mul_comm]
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := g) (v := gaussianPDFReal 0 1)
    (u' := g') (v' := fun x => -x * gaussianPDFReal 0 1 x)
    (fun x _ => hg x) (fun x _ => hpdf x) hgp hg' hprod
  have hv : (1 : ℝ≥0) ≠ 0 := by norm_num
  rw [integral_gaussianReal_eq_integral_smul hv, integral_gaussianReal_eq_integral_smul hv]
    at ⊢
  simp only [smul_eq_mul] at ⊢
  have hpdf_id : ∫ x, g x * (-x * gaussianPDFReal 0 1 x) ∂volume =
      - ∫ x, x * g x * gaussianPDFReal 0 1 x ∂volume := by
    rw [show (fun x => g x * (-x * gaussianPDFReal 0 1 x)) =
      fun x => -(x * g x * gaussianPDFReal 0 1 x) by
        funext x
        ring]
    rw [integral_neg]
  have hpdf_id' : ∫ x, x * g x * gaussianPDFReal 0 1 x ∂volume =
      - ∫ x, g x * (-x * gaussianPDFReal 0 1 x) ∂volume := by
    linarith [hpdf_id]
  have hgauss : ∫ x, g' x * gaussianPDFReal 0 1 x ∂volume =
      ∫ x, gaussianPDFReal 0 1 x * g' x ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  calc
    ∫ x, gaussianPDFReal 0 1 x * (x * g x) ∂volume
        = - ∫ x, g x * (-x * gaussianPDFReal 0 1 x) ∂volume := by
            rw [show (fun x => gaussianPDFReal 0 1 x * (x * g x)) =
              fun x => x * g x * gaussianPDFReal 0 1 x by
                funext x
                ring]
            exact hpdf_id'
    _ = - (- ∫ x, g' x * gaussianPDFReal 0 1 x ∂volume) := by rw [hibp]
    _ = ∫ x, g' x * gaussianPDFReal 0 1 x ∂volume := by ring
    _ = ∫ x, gaussianPDFReal 0 1 x * g' x ∂volume := hgauss

end DOZZ.Proofs
