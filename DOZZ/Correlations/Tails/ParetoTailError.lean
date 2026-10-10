/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsParetoProduct

/-! The exact Pareto identity gives a remainder controlled by a higher moment. -/

@[expose] public section
open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

theorem pareto_scalar_error_le (a x p r : ℝ) (ha : 0 ≤ a)
    (hx : 0 < x) (hp : 0 < p) (hpr : p ≤ r) :
    |(if a ≤ 0 then 0 else if a ≤ x then (a/x)^p else 1)-(a/x)^p| ≤ (a/x)^r := by
  by_cases ha0 : a ≤ 0
  · have ha' : a = 0 := le_antisymm ha0 ha
    simp only [ha', zero_div, Real.zero_rpow hp.ne', ite_eq_left le_rfl,
      sub_zero, abs_zero]
    exact Real.rpow_nonneg (by positivity) _
  · rw [ite_eq_right ha0]
    by_cases hax : a ≤ x
    · rw [ite_eq_left hax, sub_self, abs_zero]
      exact Real.rpow_nonneg (div_nonneg ha hx.le) _
    · rw [ite_eq_right hax]
      have hu : 1 ≤ a/x := (one_le_div hx).mpr (le_of_not_ge hax)
      have hv : 1 ≤ (a/x)^p := Real.one_le_rpow hu hp.le
      rw [abs_of_nonpos (by linarith)]
      linarith [Real.rpow_le_rpow_of_exponent_le hu hpr]

/-- The Pareto remainder in the one-insertion tail estimate uses only the indicated moments of the
independent amplitude. -/
theorem williams_pareto_tail_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → ℝ) (hA : Measurable A) (hA0 : ∀ ω, 0 ≤ A ω)
    (ν γ x r : ℝ) (hν : 0 < ν) (hγ : 0 < γ) (hx : 0 < x)
    (hpr : 2*ν/γ ≤ r)
    (hAp : Integrable (fun ω => A ω^(2*ν/γ)) P)
    (hAr : Integrable (fun ω => A ω^r) P) :
    |(((brownianMaximumReferenceLaw ν).prod P) {q : ℝ × Ω | x < A q.2*Real.exp (γ*q.1)}).toReal -
      x^(-(2*ν/γ)) * ∫ ω, A ω^(2*ν/γ) ∂P| ≤ x^(-r) * ∫ ω, A ω^r ∂P := by
  let p := 2*ν/γ
  have hp : 0 < p := by dsimp [p]; positivity
  let F : Ω → ℝ := fun ω => if A ω ≤ 0 then 0 else if A ω ≤ x then (A ω/x)^p else 1
  have hFm : Measurable F := by
    apply Measurable.ite (measurableSet_le hA measurable_const) measurable_const
    exact Measurable.ite (measurableSet_le hA measurable_const)
      ((hA.div_const x).pow_const p) measurable_const
  have hFb (ω : Ω) : 0 ≤ F ω ∧ F ω ≤ 1 := by
    dsimp [F]
    split_ifs with h0 hax
    · exact ⟨le_rfl, zero_le_one⟩
    · exact ⟨Real.rpow_nonneg (div_nonneg (hA0 ω) hx.le) _,
        Real.rpow_le_one (div_nonneg (hA0 ω) hx.le) ((div_le_one hx).mpr hax) hp.le⟩
    · exact ⟨zero_le_one, le_rfl⟩
  have hFi : Integrable F P := (integrable_const (1 : ℝ)).mono' hFm.aestronglyMeasurable
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hFb ω).1]; exact (hFb ω).2)
  have heq (a : ℝ) (ha : 0 ≤ a) (s : ℝ) : (a/x)^s = x^(-s)*a^s := by
    rw [Real.div_rpow ha hx.le, Real.rpow_neg hx.le]
    ring
  have hpi : Integrable (fun ω => (A ω/x)^p) P := by
    simpa only [heq _ (hA0 _) p] using hAp.const_mul (x^(-p))
  rw [williams_pareto_product_tail P A hA ν γ x hν hγ hx]
  change |(∫ ω, F ω ∂P)-x^(-p)*(∫ ω, A ω^p ∂P)| ≤ _
  rw [← integral_const_mul]
  simp_rw [← heq _ (hA0 _) p]
  rw [← integral_sub hFi hpi]
  have hg : Integrable (fun ω => (A ω/x)^r) P := by
    simpa only [heq _ (hA0 _) r] using hAr.const_mul (x^(-r))
  have hb := norm_integral_le_of_norm_le hg (ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs]
    exact pareto_scalar_error_le (A ω) x p r (hA0 ω) hx hp hpr)
  simp only [Real.norm_eq_abs] at hb
  simpa only [heq _ (hA0 _) r, integral_const_mul] using hb


end DOZZ.Proofs
