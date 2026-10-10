/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.MaximumParetoLaw
public import DOZZ.FourPoint.Reflected.ParetoCoefficient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
/-! # Integrating the actual maximum law in the signed reflected increment -/
public section
open MeasureTheory ProbabilityTheory Set
namespace DOZZ.Proofs

/-- The Pareto-law expectation is the exact lower-cutoff integral used by Williams' squeeze. -/
theorem reflected_pareto_increment_integral (p a A b : ℝ) (ha : 0 < a)
    (hA : 0 < A) (hb : 0 < b) :
    (∫ v, ((A + b * v) ^ (-p) - A ^ (-p)) ∂paretoMeasure 1 a) =
      a * A ^ (-p) * (b / A) ^ a *
        ∫ w in Ioi (b / A), ((1 + w) ^ (-p) - 1) * w ^ (-a - 1) := by
  let x := b / A
  have hx : 0 < x := div_pos hb hA
  let g : ℝ → ℝ := fun w => ((1 + w) ^ (-p) - 1) * w ^ (-a - 1)
  have hd : ∀ v, (paretoPDF 1 a v).toReal = paretoPDFReal 1 a v := by
    intro v
    exact ENNReal.toReal_ofReal (paretoPDFReal_nonneg (by norm_num) ha.le v)
  rw [paretoMeasure, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (paretoPDF 1 a) from ENNReal.measurable_ofReal.comp
      (measurable_paretoPDFReal 1 a))
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [hd, smul_eq_mul]
  have hid : (fun v : ℝ => paretoPDFReal 1 a v * ((A + b * v) ^ (-p) - A ^ (-p))) =
      (Ici (1 : ℝ)).indicator (fun v => a * v ^ (-a - 1) * ((A + b * v) ^ (-p) - A ^ (-p))) := by
    funext v
    by_cases hv : 1 ≤ v
    · rw [indicator_of_mem (show v ∈ Ici (1 : ℝ) from hv), paretoPDFReal, ite_eq_left hv, Real.one_rpow, mul_one]
      congr 2
      congr 1
      ring
    · rw [indicator_of_notMem (show v ∉ Ici (1 : ℝ) from hv), paretoPDFReal, ite_eq_right hv, zero_mul]
  rw [hid, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hpoint (v : ℝ) (hv : v ∈ Ioi (1 : ℝ)) :
      a * v ^ (-a - 1) * ((A + b * v) ^ (-p) - A ^ (-p)) =
        (a * A ^ (-p) * x ^ (a + 1)) * g (x * v) := by
    have hvp : 0 < v := zero_lt_one.trans hv
    have hsum : A + b * v = A * (1 + x * v) := by
      dsimp only [x]
      field_simp
    have hpw : x ^ (a + 1) * (x * v) ^ (-a - 1) = v ^ (-a - 1) := by
      rw [Real.mul_rpow hx.le hvp.le, ← mul_assoc, ← Real.rpow_add hx]
      have he : (a + 1) + (-a - 1) = 0 := by ring
      rw [he, Real.rpow_zero, one_mul]
    dsimp only [g]
    rw [hsum, Real.mul_rpow hA.le (by positivity : 0 ≤ 1 + x * v)]
    calc
      _ = (a * A ^ (-p)) * v ^ (-a - 1) * ((1 + x * v) ^ (-p) - 1) := by ring
      _ = _ := by rw [← hpw]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul,
    integral_comp_mul_left_Ioi g 1 hx, mul_one, smul_eq_mul]
  have hc : a * A ^ (-p) * x ^ (a + 1) * x⁻¹ = a * A ^ (-p) * x ^ a := by
    rw [Real.rpow_add hx, Real.rpow_one]
    field_simp
  calc
    _ = (a * A ^ (-p) * x ^ (a + 1) * x⁻¹) * ∫ w in Ioi x, g w := by ring
    _ = _ := by rw [hc]

/-- The actual Pareto increment differs from its Gamma coefficient by an explicit first-order term. -/
theorem reflected_pareto_increment_error (p a A b : ℝ) (hp : 0 < p) (ha : 0 < a)
    (ha₁ : a < 1) (hA : 0 < A) (hb : 0 < b) :
    |(∫ v, ((A + b * v) ^ (-p) - A ^ (-p)) ∂paretoMeasure 1 a) -
      (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) *
        A ^ (-p) * (b / A) ^ a| ≤
      (a * p / (1 - a)) * A ^ (-p) * (b / A) := by
  rw [reflected_pareto_increment_integral p a A b ha hA hb]
  exact reflected_pareto_scaled_error p a A (b / A) hp ha ha₁ hA (div_pos hb hA)

end DOZZ.Proofs
