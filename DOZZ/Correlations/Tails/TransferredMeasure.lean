/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.UnpinnedSourceIdentification

/-! The source measure obtained by translating and removing the equator pin. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The unpinned source measure, carried by the open unit insertion chart. -/
noncomputable def transferredMeasure (μ : Measure ℂ) (z : ℂ) (γ N : ℝ) : Measure ℂ :=
  ((μ.restrict (Metric.ball z 1)).withDensity (fun w => ENNReal.ofReal
    (Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))))).map (fun w => w-z)

/-- The pin-removal density is measurable and bounded on the translated unit chart. -/
theorem transferred_measure_density_bound (z : ℂ) (γ N : ℝ) :
    ∀ w ∈ Metric.ball z 1,
      Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)) ≤
        Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus z + 1)) := by
  intro w hw
  have hwz : ‖w-z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hn : normPlus w ≤ normPlus z + 1 := by
    unfold normPlus
    apply max_le
    · have h := norm_nonneg z
      have h' : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _
      linarith
    · have htri : ‖w‖ ≤ ‖w-z‖ + ‖z‖ := by
        simpa only [sub_add_cancel] using norm_add_le (w-z) z
      exact htri.trans (by linarith [le_max_right (1 : ℝ) ‖z‖])
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.log_le_log (by unfold normPlus; positivity) hn

/-- Translating and removing the pin preserves finiteness of the source measure. -/
theorem transferred_measure_finite (μ : Measure ℂ) [IsFiniteMeasure μ]
    (z : ℂ) (γ N : ℝ) : IsFiniteMeasure (transferredMeasure μ z γ N) := by
  let d : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal
    (Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)))
  let C : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus z + 1)))
  have hb : ∫⁻ w, d w ∂μ.restrict (Metric.ball z 1) ≤
      C * μ (Metric.ball z 1) := by
    have h := lintegral_mono_ae (μ := μ.restrict (Metric.ball z 1)) (g := fun _ => C) (by
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with w hw
      exact ENNReal.ofReal_le_ofReal (transferred_measure_density_bound z γ N w hw))
    simpa only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
      univ_inter, d, C] using h
  have hd : IsFiniteMeasure ((μ.restrict (Metric.ball z 1)).withDensity d) :=
    isFiniteMeasure_withDensity (ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _)) hb)
  let := hd
  change IsFiniteMeasure (((μ.restrict (Metric.ball z 1)).withDensity d).map (fun w => w-z))
  infer_instance

/-- The transferred measure assigns no mass outside the unit chart. -/
theorem transferred_measure_carried (μ : Measure ℂ) (z : ℂ) (γ N : ℝ) :
    transferredMeasure μ z γ N (Metric.ball 0 1)ᶜ = 0 := by
  have htrans : Measurable (fun w : ℂ => w-z) := by fun_prop
  rw [transferredMeasure, Measure.map_apply htrans
    (Metric.isOpen_ball (x := (0 : ℂ)) (ε := (1 : ℝ))).measurableSet.compl]
  have hpre : (fun w : ℂ => w-z) ⁻¹' (Metric.ball 0 1)ᶜ = (Metric.ball z 1)ᶜ := by
    ext w
    simp only [mem_preimage, mem_compl_iff, Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [hpre, withDensity_apply _ Metric.isOpen_ball.measurableSet.compl,
    Measure.restrict_restrict Metric.isOpen_ball.measurableSet.compl]
  simp only [compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]

/-- Every compact test integral of the transferred measure has the exact source-GMC formula. -/
theorem transferred_measure_test_integral (μ : Measure ℂ) (z : ℂ) (γ N : ℝ)
    (f g : BoundedContinuousFunction ℂ ℝ)
    (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1)
    (hg : ∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) :
    (∫ x, f x ∂transferredMeasure μ z γ N) =
      Real.exp (-γ * N) * ∫ w, g w ∂μ := by
  have hd : Measurable (fun w : ℂ => ENNReal.ofReal
      (Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)))) := by
    unfold normPlus
    fun_prop
  have htrans : Measurable (fun w : ℂ => w-z) := by fun_prop
  rw [transferredMeasure, integral_map htrans.aemeasurable
    f.continuous.aestronglyMeasurable, integral_withDensity_eq_integral_toReal_smul hd
    (ae_of_all _ fun w => ENNReal.ofReal_lt_top)]
  have heq : (fun w : ℂ => (ENNReal.ofReal
      (Real.exp (-γ * N) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)))).toReal * f (w-z)) =
      fun w => Real.exp (-γ * N) * g w := by
    funext w
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)), hg w]
    ring
  simp only [smul_eq_mul]
  rw [heq, integral_const_mul]
  congr 1
  apply integral_restrict_eq_integral_of_zero_on_compl μ _ Metric.isOpen_ball.measurableSet
  intro w hw
  rw [hg w]
  have hfw : f (w-z) = 0 := image_eq_zero_of_notMem_tsupport (fun h => hw (by
    have hh := hfU h
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hh))
  rw [hfw, zero_mul]


end DOZZ.Proofs
