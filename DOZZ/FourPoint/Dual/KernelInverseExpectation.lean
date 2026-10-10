/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.KernelRealSqueeze
public import DOZZ.FourPoint.Dual.KernelIncrementExpectation
import Mathlib.Tactic
/-! Compare the extended-valued copied inverse expectation with the real signed polar loss. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The finite retained inverse expectation controls the actual copied inverse expectation.
Every extended-to-real conversion is justified by finite masses and finite inverse integrals. -/
theorem dual_ennreal_kernel_inverse_expectation_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (O I V : Ω → ℝ≥0∞) (β : Ω → ℝ) (p θlo θhi : ℝ)
    (hp : 0 < p) (hlo : 0 ≤ θlo) (hhi : 0 ≤ θhi)
    (hO : AEMeasurable O P) (hI : AEMeasurable I P) (hV : AEMeasurable V P)
    (hβ : AEMeasurable β P) (hβpos : ∀ᵐ ω ∂P, 0 ≤ β ω)
    (hpos : ∀ᵐ ω ∂P, 0 < (O ω).toReal) (hVfin : ∀ᵐ ω ∂P, V ω ≠ ⊤)
    (hInv : (∫⁻ ω, O ω^(-p) ∂P) ≠ ⊤)
    (hs : ∀ᵐ ω ∂P, ENNReal.ofReal (θlo*β ω)*V ω ≤ I ω ∧
      I ω ≤ ENNReal.ofReal (θhi*β ω)*V ω) :
    |(∫⁻ ω, (O ω+I ω)^(-p) ∂P).toReal-(∫⁻ ω, O ω^(-p) ∂P).toReal-
      (∫ ω, ((O ω).toReal+β ω*(V ω).toReal)^(-p)-(O ω).toReal^(-p) ∂P)| ≤
      max |θlo-1| |θhi-1| *
        (∫ ω, (O ω).toReal^(-p)-((O ω).toReal+β ω*(V ω).toReal)^(-p) ∂P) := by
  have hIfin : ∀ᵐ ω ∂P, I ω ≠ ⊤ := by
    filter_upwards [hpos, hβpos, hVfin, hs] with ω hOω hβω hVω hsω
    exact (dual_ennreal_kernel_increment_error (I ω) (V ω) p (O ω).toReal (β ω)
      θlo θhi hp hOω hβω hlo hhi hVω hsω).1
  have hOfin : ∀ᵐ ω ∂P, O ω ≠ ⊤ := by
    filter_upwards [hpos] with ω hω
    intro he
    simp only [he, ENNReal.toReal_top, lt_self_iff_false] at hω
  have hreal : (fun ω => ((O ω+I ω)^(-p)).toReal) =ᵐ[P]
      (fun ω => ((O ω).toReal+(I ω).toReal)^(-p)) := by
    filter_upwards [hOfin, hIfin] with ω hOω hIω
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_add hOω hIω]
  have hK : (∫⁻ ω, (O ω+I ω)^(-p) ∂P) ≠ ⊤ := by
    apply ne_top_of_le_ne_top hInv
    apply lintegral_mono
    intro ω
    change (O ω+I ω)^(-p) ≤ O ω^(-p)
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow le_self_add hp.le)
  have hmK := (hO.add hI).pow_const (-p)
  have hmO := hO.pow_const (-p)
  have hiK := (integrable_toReal_of_lintegral_ne_top hmK hK).congr hreal
  have hiO : Integrable (fun ω => (O ω).toReal^(-p)) P := by
    simpa only [ENNReal.toReal_rpow] using integrable_toReal_of_lintegral_ne_top hmO hInv
  have heK : (∫ ω, ((O ω).toReal+(I ω).toReal)^(-p) ∂P) =
      (∫⁻ ω, (O ω+I ω)^(-p) ∂P).toReal := by
    rw [← integral_congr_ae hreal]
    exact integral_toReal hmK (ae_lt_top' hmK hK)
  have heO : (∫ ω, (O ω).toReal^(-p) ∂P) = (∫⁻ ω, O ω^(-p) ∂P).toReal := by
    simpa only [ENNReal.toReal_rpow] using integral_toReal hmO (ae_lt_top' hmO hInv)
  have hbounds : ∀ᵐ ω ∂P, θlo*(β ω*(V ω).toReal) ≤ (I ω).toReal ∧
      (I ω).toReal ≤ θhi*(β ω*(V ω).toReal) := by
    filter_upwards [hs, hIfin, hVfin, hβpos] with ω hsω hIω hVω hβω
    constructor
    · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hlo hβω), mul_assoc] using
        ENNReal.toReal_mono hIω hsω.1
    · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hhi hβω), mul_assoc] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hVω) hsω.2
  have hb := dual_negative_increment_kernel_integral P p θlo θhi hp hlo hhi
    (fun ω => (O ω).toReal) (fun ω => β ω*(V ω).toReal) (fun ω => (I ω).toReal)
    hpos (by filter_upwards [hβpos] with ω hω; exact mul_nonneg hω ENNReal.toReal_nonneg)
    hbounds hO.ennreal_toReal (hβ.mul hV.ennreal_toReal) hI.ennreal_toReal hiO
  rw [integral_sub hiK hiO, heK, heO] at hb
  exact hb

end DOZZ.Proofs
