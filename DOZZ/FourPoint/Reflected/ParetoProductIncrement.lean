/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ParetoIncrement
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
/-! Integrating the signed Pareto coefficient against independent outer and reflection masses. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
namespace DOZZ.Proofs

/-- The scalar Pareto expectation is measurable for the actual random mass parameters. -/
theorem reflected_pareto_increment_aestronglyMeasurable
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p a : ℝ) (ha : 0 < a) (A b : Ω → ℝ) (S : Λ → ℝ)
    (hA : AEMeasurable A P) (hb : AEMeasurable b P) (hS : AEMeasurable S R) :
    AEStronglyMeasurable (fun v : Ω × Λ => ∫ w,
      ((A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) ∂paretoMeasure 1 a) (P.prod R) := by
  let _ : IsProbabilityMeasure (paretoMeasure 1 a) := isProbabilityMeasure_paretoMeasure zero_lt_one ha
  have hAp : AEMeasurable (fun v : Ω × Λ => A v.1) (P.prod R) :=
    hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hbp : AEMeasurable (fun v : Ω × Λ => b v.1) (P.prod R) :=
    hb.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hSp : AEMeasurable (fun v : Ω × Λ => S v.2) (P.prod R) :=
    hS.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving
  have hAA := hAp.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := paretoMeasure 1 a)).quasiMeasurePreserving
  have hbb := hbp.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := paretoMeasure 1 a)).quasiMeasurePreserving
  have hSS := hSp.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P.prod R) (ν := paretoMeasure 1 a)).quasiMeasurePreserving
  change AEMeasurable (fun v : (Ω × Λ) × ℝ => A v.1.1)
    ((P.prod R).prod (paretoMeasure 1 a)) at hAA
  change AEMeasurable (fun v : (Ω × Λ) × ℝ => b v.1.1)
    ((P.prod R).prod (paretoMeasure 1 a)) at hbb
  change AEMeasurable (fun v : (Ω × Λ) × ℝ => S v.1.2)
    ((P.prod R).prod (paretoMeasure 1 a)) at hSS
  have hpow : Measurable (fun x : ℝ => x^(-p)) := by fun_prop
  have hK : AEMeasurable (fun v : (Ω × Λ) × ℝ =>
      (A v.1.1+b v.1.1*S v.1.2*v.2)^(-p)-(A v.1.1)^(-p))
        ((P.prod R).prod (paretoMeasure 1 a)) :=
    (hpow.comp_aemeasurable (hAA.add ((hbb.mul hSS).mul measurable_snd.aemeasurable))).sub
      (hpow.comp_aemeasurable hAA)
  exact hK.aestronglyMeasurable.integral_prod_right'

/-- Pareto's leading and first-order weights are exactly the powers supplied by the
Cameron-Martin charge shift and the freezing estimate. -/
theorem reflected_pareto_parameter_weights (p a A b : ℝ) (hA : 0 < A) (hb : 0 ≤ b) :
    A^(-p)*(b/A)^a = b^a*A^(-p-a) ∧ A^(-p)*(b/A) = b*A^(-p-1) := by
  constructor
  · rw [Real.div_rpow hb hA.le, Real.rpow_sub hA]
    ring
  · rw [Real.rpow_sub_one hA.ne']
    ring

/-- The full Pareto increment factors its leading term and keeps the explicit first-order
error after integration over the actual independent outer and reflection carriers. -/
theorem reflected_pareto_product_increment_error
    {Ω Λ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) (ha1 : a < 1)
    (A b : Ω → ℝ) (S : Λ → ℝ)
    (hA : ∀ᵐ ω ∂P, 0 < A ω) (hb : ∀ᵐ ω ∂P, 0 < b ω) (hS : ∀ᵐ v ∂R, 0 < S v)
    (hF0 : Integrable (fun ω => (A ω)^(-p)*(b ω/A ω)^a) P)
    (hF1 : Integrable (fun ω => (A ω)^(-p)*(b ω/A ω)) P)
    (hSa : Integrable (fun v => (S v)^a) R) (hS1 : Integrable S R)
    (hAm : AEMeasurable A P) (hbm : AEMeasurable b P) (hSm : AEMeasurable S R) :
    Integrable (fun v : Ω × Λ => ∫ w,
      ((A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) ∂paretoMeasure 1 a) (P.prod R) ∧
    |(∫ v : Ω × Λ, (∫ w,
      ((A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) ∂paretoMeasure 1 a) ∂P.prod R) -
      (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫ ω, (A ω)^(-p)*(b ω/A ω)^a ∂P)*(∫ v, (S v)^a ∂R)| ≤
      (a*p/(1-a))*(∫ ω, (A ω)^(-p)*(b ω/A ω) ∂P)*(∫ v, S v ∂R) := by
  have hE := reflected_pareto_increment_aestronglyMeasurable P R p a ha A b S hAm hbm hSm
  let E := fun v : Ω × Λ => ∫ w,
    ((A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) ∂paretoMeasure 1 a
  let F0 := fun ω => (A ω)^(-p)*(b ω/A ω)^a
  let F1 := fun ω => (A ω)^(-p)*(b ω/A ω)
  let c := a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p
  let C := a*p/(1-a)
  let L := fun v : Ω × Λ => c*(F0 v.1*(S v.2)^a)
  have hL : Integrable L (P.prod R) := (hF0.mul_prod hSa).const_mul c
  have hdom : Integrable (fun v : Ω × Λ => C*(F1 v.1*S v.2)) (P.prod R) :=
    (hF1.mul_prod hS1).const_mul C
  have hbound : ∀ᵐ v : Ω × Λ ∂P.prod R, ‖E v-L v‖ ≤ C*(F1 v.1*S v.2) := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae hA,
      measurePreserving_fst.quasiMeasurePreserving.ae hb,
      measurePreserving_snd.quasiMeasurePreserving.ae hS] with v hAv hbv hSv
    have hi := reflected_pareto_increment_error p a (A v.1) (b v.1*S v.2)
      hp ha ha1 hAv (mul_pos hbv hSv)
    have hr : (b v.1*S v.2)/A v.1 = (b v.1/A v.1)*S v.2 := by ring
    rw [hr, Real.mul_rpow (div_pos hbv hAv).le hSv.le] at hi
    change |E v-L v| ≤ _
    change |E v-c*(A v.1)^(-p)*((b v.1/A v.1)^a*(S v.2)^a)| ≤
      C*(A v.1)^(-p)*((b v.1/A v.1)*S v.2) at hi
    have heL : c*(A v.1)^(-p)*((b v.1/A v.1)^a*(S v.2)^a) = L v := by
      dsimp only [L,F0]
      ring
    have heD : C*(A v.1)^(-p)*((b v.1/A v.1)*S v.2) = C*(F1 v.1*S v.2) := by
      dsimp only [F1]
      ring
    rw [heL,heD] at hi
    exact hi
  have hD : Integrable (fun v => E v-L v) (P.prod R) :=
    hdom.mono' (hE.sub hL.aestronglyMeasurable) hbound
  have hEi : Integrable E (P.prod R) := by
    have hh := hD.add hL
    change Integrable (fun v => (E v-L v)+L v) (P.prod R) at hh
    simpa only [sub_add_cancel] using hh
  refine ⟨hEi, ?_⟩
  have hi := norm_integral_le_of_norm_le hdom hbound
  rw [integral_sub hEi hL] at hi
  have hlead : (∫ v, L v ∂P.prod R) = c*(∫ ω, F0 ω ∂P)*(∫ v, (S v)^a ∂R) := by
    rw [show L = (fun v : Ω × Λ => c*(F0 v.1*(S v.2)^a)) from rfl,
      integral_const_mul, integral_prod_mul F0 (fun v => (S v)^a), mul_assoc]
  rw [hlead, integral_const_mul, integral_prod_mul] at hi
  simpa only [Real.norm_eq_abs,E,F0,F1,c,C,mul_assoc] using hi

end DOZZ.Proofs
