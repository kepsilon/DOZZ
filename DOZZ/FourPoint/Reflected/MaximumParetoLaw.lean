/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.MaximumGeometry
public import Mathlib.Probability.Distributions.Pareto
import Mathlib.Tactic
/-! # The actual negative-drift maximum has the Pareto law after exponentiation -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The scale-one Pareto measure has the literal power tail above its lower endpoint. -/
theorem reflected_pareto_tail (a v : ℝ) (ha : 0 < a) (hv : 1 ≤ v) :
    paretoMeasure 1 a (Ioi v) = ENNReal.ofReal (v ^ (-a)) := by
  have hp : 0 < v := zero_lt_one.trans_le hv
  rw [paretoMeasure, withDensity_apply _ measurableSet_Ioi]
  have hid : (∫⁻ y in Ioi v, paretoPDF 1 a y) =
      ∫⁻ y in Ioi v, ENNReal.ofReal (a * y ^ (-(a + 1))) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    rw [paretoPDF_of_le (hv.trans hy.le), Real.one_rpow, mul_one]
  have hi : IntegrableOn (fun y : ℝ => a * y ^ (-(a + 1))) (Ioi v) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith only [ha] : -(a + 1) < -1) hp).const_mul a
  have hb : ∀ᵐ y ∂volume.restrict (Ioi v), 0 ≤ a * y ^ (-(a + 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact mul_nonneg ha.le (Real.rpow_nonneg (hp.trans hy).le _)
  rw [hid, ← ofReal_integral_eq_lintegral_ofReal hi hb, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith only [ha] : -(a + 1) < -1) hp]
  congr 1
  have he : -(a + 1) + 1 = -a := by ring
  rw [he]
  field_simp

/-- The Pareto variable is at least one almost surely. -/
theorem reflected_pareto_ge_one_ae (a : ℝ) : ∀ᵐ v ∂paretoMeasure 1 a, 1 ≤ v := by
  rw [ae_iff]
  simp only [not_le]
  change paretoMeasure 1 a (Iio 1) = 0
  rw [paretoMeasure, withDensity_apply _ measurableSet_Iio]
  exact lintegral_paretoPDF_of_le le_rfl

/-- Exponentiating the literal Brownian maximum gives the scale-one Pareto law of order 2nu/gamma. -/
theorem reflected_brownian_maximum_pareto_law
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) :
    P.map (fun p => Real.exp (γ * driftedBrownianMaximum ν p)) =
      paretoMeasure 1 (2 * ν / γ) := by
  let _ : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have ha : 0 < 2 * ν / γ := div_pos (mul_pos (by norm_num) hν) hγ
  let _ := isProbabilityMeasure_paretoMeasure zero_lt_one ha
  have hmax := aemeasurable_driftedBrownianMaximum P hB ν hν
  have hm : AEMeasurable (fun p => Real.exp (γ * driftedBrownianMaximum ν p)) P :=
    (hmax.const_mul γ).exp
  let _ : IsProbabilityMeasure (P.map (fun p => Real.exp (γ * driftedBrownianMaximum ν p))) :=
    (Measure.isProbabilityMeasure_map_iff hm).mpr inferInstance
  have htail (v : ℝ) : P.map (fun p => Real.exp (γ * driftedBrownianMaximum ν p)) (Ioi v) =
      paretoMeasure 1 (2 * ν / γ) (Ioi v) := by
    rw [Measure.map_apply_of_aemeasurable hm measurableSet_Ioi]
    by_cases hv : 1 ≤ v
    · have hp : 0 < v := zero_lt_one.trans_le hv
      have he : (fun p => Real.exp (γ * driftedBrownianMaximum ν p)) ⁻¹' Ioi v =
          (driftedBrownianMaximum ν) ⁻¹' Ioi (Real.log v / γ) := by
        ext p
        simp only [mem_preimage, mem_Ioi, ← Real.log_lt_iff_lt_exp hp,
          div_lt_iff₀ hγ, mul_comm γ]
      rw [he, ← Measure.map_apply_of_aemeasurable hmax measurableSet_Ioi,
        brownianPath_globalMaximum_Ioi P hB ν (Real.log v / γ) hν
          (div_nonneg (Real.log_nonneg hv) hγ.le), reflected_pareto_tail _ v ha hv]
      congr 1
      rw [Real.rpow_def_of_pos hp]
      congr 1
      ring
    · have hv' : v < 1 := lt_of_not_ge hv
      have he : ∀ᵐ p ∂P, Real.exp (γ * driftedBrownianMaximum ν p) ∈ Ioi v := by
        filter_upwards [brownianPath_globalMaximum_nonneg_ae P hB ν hν] with p hp
        exact hv'.trans_le (Real.one_le_exp_iff.mpr (mul_nonneg hγ.le hp))
      have hy : ∀ᵐ y ∂paretoMeasure 1 (2 * ν / γ), y ∈ Ioi v :=
        (reflected_pareto_ge_one_ae _).mono fun y hy => hv'.trans_le hy
      have hl : P ((fun p => Real.exp (γ * driftedBrownianMaximum ν p)) ⁻¹' Ioi v) = 1 :=
        (measure_congr (he.mono fun p hp => propext ⟨fun _ => mem_univ p, fun _ => hp⟩)).trans
          (measure_univ)
      have hr : paretoMeasure 1 (2 * ν / γ) (Ioi v) = 1 :=
        (measure_congr (hy.mono fun y hy => propext ⟨fun _ => mem_univ y, fun _ => hy⟩)).trans
          (measure_univ)
      exact hl.trans hr.symm
  apply Measure.ext_of_Iic
  intro v
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, htail]

end DOZZ.Proofs
