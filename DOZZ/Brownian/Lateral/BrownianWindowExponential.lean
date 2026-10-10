/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.RadialWindowUniform
public import DOZZ.Brownian.Barrier.GaussianBounds
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Brownian window exponential moments

Reflection gives a Gaussian tail for the absolute compact-window norm. A direct sum over
integer norm levels proves every exponential moment and keeps the bound uniform over bounded
exponential orders. These are the Brownian unit-increment estimates in the positive conditioned
half-cylinder block argument; no conditioned-process coupling is constructed here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The absolute supremum on the unit Brownian time window. -/
noncomputable def brownianUnitNorm (p : BrownianPath) : ℝ :=
  ‖p.restrict (Icc 0 (1 : ℝ≥0))‖

/-- The window norm is continuous on the full path carrier. -/
theorem continuous_brownianUnitNorm : Continuous brownianUnitNorm :=
  continuous_norm.comp (ContinuousMap.continuous_restrict _)

/-- The unit-window norm is nonnegative on every path, without a stochastic assumption. -/
theorem brownianUnitNorm_nonneg (p : BrownianPath) : 0 ≤ brownianUnitNorm p :=
  norm_nonneg _

/-- The absolute supremum is attained on this compact time window. -/
theorem brownianUnitNorm_attained (p : BrownianPath) :
    ∃ t : ℝ≥0, t ≤ 1 ∧ |p t| = brownianUnitNorm p := by
  obtain ⟨t, ht, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ≥0) ≤ 1))
    (continuous_abs.comp p.continuous).continuousOn
  refine ⟨t, ht.2, le_antisymm ?_ ?_⟩
  · exact (p.restrict (Icc 0 (1 : ℝ≥0))).norm_coe_le_norm ⟨t, ht⟩
  · exact (ContinuousMap.norm_le _ (abs_nonneg _)).mpr (fun s => hmax s.2)

/-- The terminal Gaussian upper tail has its usual optimized Chernoff bound. -/
theorem brownian_unit_terminal_tail_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (r : ℝ) (hr : 0 < r) :
    P {p | r < p 1} ≤ ENNReal.ofReal (Real.exp (-r ^ 2 / 2)) := by
  have hb := brownian_terminal_event_bound hB.toIsPreBrownianReal 1 (-r) (-r ^ 2)
    {p | r < p 1} (fun p hp => by change r < p 1 at hp; nlinarith)
  have he : -r ^ 2 + (-r) ^ 2 * (1 : ℝ) / 2 = -r ^ 2 / 2 := by ring
  simpa only [NNReal.coe_one, he] using hb

/-- The corresponding lower Gaussian tail has the same bound. -/
theorem brownian_unit_negative_terminal_tail_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (r : ℝ) (hr : 0 < r) :
    P {p | r < -p 1} ≤ ENNReal.ofReal (Real.exp (-r ^ 2 / 2)) := by
  have hb := brownian_terminal_event_bound hB.neg.toIsPreBrownianReal 1 (-r) (-r ^ 2)
    {p | r < -p 1} (fun p hp => by
      change r < -p 1 at hp
      change -r * (-p 1) ≤ -r ^ 2
      nlinarith)
  have he : -r ^ 2 + (-r) ^ 2 * (1 : ℝ) / 2 = -r ^ 2 / 2 := by ring
  simpa only [NNReal.coe_one, he] using hb

/-- Reflection on both signs bounds the absolute unit-window norm tail by four Gaussian tails. -/
theorem brownianUnitNorm_tail_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (r : ℝ) (hr : 0 < r) :
    P {p | r ≤ brownianUnitNorm p} ≤
      4 * ENNReal.ofReal (Real.exp (-r ^ 2 / 2)) := by
  have hs : {p : BrownianPath | r ≤ brownianUnitNorm p} ⊆
      {p | ∃ t ≤ (1 : ℝ≥0), r ≤ p t} ∪
        {p | ∃ t ≤ (1 : ℝ≥0), r ≤ -p t} := by
    intro p hp
    obtain ⟨t, ht, he⟩ := brownianUnitNorm_attained p
    change r ≤ brownianUnitNorm p at hp
    rw [← he] at hp
    have h := le_abs.mp hp
    rcases h with h | h
    · exact Or.inl ⟨t, ht, h⟩
    · exact Or.inr ⟨t, ht, h⟩
  calc
    _ ≤ P ({p | ∃ t ≤ (1 : ℝ≥0), r ≤ p t} ∪
        {p | ∃ t ≤ (1 : ℝ≥0), r ≤ -p t}) := measure_mono hs
    _ ≤ P {p | ∃ t ≤ (1 : ℝ≥0), r ≤ p t} +
        P {p | ∃ t ≤ (1 : ℝ≥0), r ≤ -p t} := measure_union_le _ _
    _ = 2 * P {p | r < p 1} + 2 * P {p | r < -p 1} := by
      have hn := brownian_runningMaximum_reflection hB.neg r hr 1 (by norm_num)
      change P {p | ∃ t ≤ (1 : ℝ≥0), r ≤ -p t} = 2 * P {p | r < -p 1} at hn
      rw [brownian_runningMaximum_reflection hB r hr 1 (by norm_num), hn]
    _ ≤ 2 * ENNReal.ofReal (Real.exp (-r ^ 2 / 2)) +
        2 * ENNReal.ofReal (Real.exp (-r ^ 2 / 2)) :=
      add_le_add (mul_le_mul' le_rfl (brownian_unit_terminal_tail_le P hB r hr))
        (mul_le_mul' le_rfl (brownian_unit_negative_terminal_tail_le P hB r hr))
    _ = _ := by ring

/-- The same tail bound also covers the zero integer level with probability normalization. -/
theorem brownianUnitNorm_nat_tail_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (n : ℕ) :
    P {p | (n : ℝ) ≤ brownianUnitNorm p} ≤
      4 * ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2 / 2)) := by
  by_cases hn : n = 0
  · subst n
    let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
    have hb : P {p | (0 : ℝ) ≤ brownianUnitNorm p} ≤ 1 := prob_le_one
    simpa using hb.trans (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  · exact brownianUnitNorm_tail_le P hB n (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))

/-- A nonnegative real variable can be bounded by its integer lower-level exponential sum. -/
theorem ennreal_exp_le_integer_levels (x θ : ℝ) (hx : 0 ≤ x) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (Real.exp (θ * x)) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ * ((n : ℝ) + 1))) *
        ({y : ℝ | (n : ℝ) ≤ y}.indicator (fun _ => (1 : ℝ≥0∞)) x) := by
  let n : ℕ := Nat.floor x
  have hn : (n : ℝ) ≤ x := Nat.floor_le hx
  have hn' : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  calc
    _ ≤ ENNReal.ofReal (Real.exp (θ * ((n : ℝ) + 1))) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hn'.le hθ))
    _ = ENNReal.ofReal (Real.exp (θ * ((n : ℝ) + 1))) *
        ({y : ℝ | (n : ℝ) ≤ y}.indicator (fun _ => (1 : ℝ≥0∞)) x) := by
      rw [indicator_of_mem (show x ∈ {y : ℝ | (n : ℝ) ≤ y} from hn), mul_one]
    _ ≤ _ := ENNReal.le_tsum (f := fun k : ℕ =>
      ENNReal.ofReal (Real.exp (θ * ((k : ℝ) + 1))) *
        ({y : ℝ | (k : ℝ) ≤ y}.indicator (fun _ => (1 : ℝ≥0∞)) x)) n

/-- The quadratic Gaussian tail wins over every exponential weight. -/
theorem summable_brownianWindow_exponential_series (θ : ℝ) :
    Summable (fun n : ℕ => Real.exp (θ * ((n : ℝ) + 1) - (n : ℝ) ^ 2 / 2)) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (θ + 1))
  rw [← summable_nat_add_iff N]
  apply (Real.summable_exp_neg_nat.mul_left (Real.exp θ)).of_nonneg_of_le
    (fun _ => (Real.exp_pos _).le)
  intro n
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ ((n + N : ℕ) : ℝ) := Nat.cast_nonneg _
  have hnN : (N : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left N n
  have hm := mul_le_mul_of_nonneg_right (hN.trans hnN) hx
  have hnn : (n : ℝ) ≤ ((n + N : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right n N
  nlinarith

/-- The deterministic series constant for a unit-window exponential moment. -/
noncomputable def brownianWindowExponentialConstant (θ : ℝ) : ℝ≥0∞ :=
  4 * ∑' n : ℕ, ENNReal.ofReal
    (Real.exp (θ * ((n : ℝ) + 1) - (n : ℝ) ^ 2 / 2))

/-- Every such deterministic constant is finite. -/
theorem brownianWindowExponentialConstant_lt_top (θ : ℝ) :
    brownianWindowExponentialConstant θ < ⊤ := by
  exact ENNReal.mul_lt_top (by norm_num)
    (summable_brownianWindow_exponential_series θ).tsum_ofReal_lt_top

/-- The actual unit-window exponential moment has the explicit finite Gaussian-series bound. -/
theorem brownianUnitNorm_exponential_moment_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p)) ∂P) ≤
      brownianWindowExponentialConstant θ := by
  let f : ℕ → BrownianPath → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (Real.exp (θ * ((n : ℝ) + 1))) *
      ({p : BrownianPath | (n : ℝ) ≤ brownianUnitNorm p}.indicator (fun _ => 1) p)
  have hm : ∀ n, Measurable (f n) := fun n => measurable_const.mul
    (measurable_const.indicator
      (measurableSet_le measurable_const continuous_brownianUnitNorm.measurable))
  have hb : (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p)) ∂P) ≤
      ∫⁻ p, ∑' n, f n p ∂P := by
    apply lintegral_mono
    intro p
    exact ennreal_exp_le_integer_levels _ θ (norm_nonneg _) hθ
  calc
    _ ≤ ∫⁻ p, ∑' n, f n p ∂P := hb
    _ = ∑' n, ∫⁻ p, f n p ∂P := lintegral_tsum (fun n => (hm n).aemeasurable)
    _ ≤ ∑' n : ℕ, 4 * ENNReal.ofReal
        (Real.exp (θ * ((n : ℝ) + 1) - (n : ℝ) ^ 2 / 2)) := by
      apply ENNReal.tsum_le_tsum
      intro n
      dsimp [f]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_indicator
        (measurableSet_le measurable_const continuous_brownianUnitNorm.measurable),
        setLIntegral_const, one_mul]
      have he : ENNReal.ofReal (Real.exp (θ * ((n : ℝ) + 1))) *
          (4 * ENNReal.ofReal (Real.exp (-(n : ℝ) ^ 2 / 2))) =
          4 * ENNReal.ofReal (Real.exp (θ * ((n : ℝ) + 1) - (n : ℝ) ^ 2 / 2)) := by
        rw [← mul_assoc, mul_comm _ (4 : ℝ≥0∞), mul_assoc,
          ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, sub_eq_add_neg, neg_div]
      exact (mul_le_mul' le_rfl (brownianUnitNorm_nat_tail_le P hB n)).trans_eq he
    _ = _ := by rw [ENNReal.tsum_mul_left]; rfl

/-- The exponential window bound is uniform over every bounded nonnegative order range. -/
theorem brownianUnitNorm_uniform_exponential_moment_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (θ Θ : ℝ)
    (hθ : 0 ≤ θ) (hθΘ : θ ≤ Θ) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p)) ∂P) ≤
      brownianWindowExponentialConstant Θ := by
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (Θ * brownianUnitNorm p)) ∂P := by
      apply lintegral_mono
      intro p
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right hθΘ (norm_nonneg _)))
    _ ≤ _ := brownianUnitNorm_exponential_moment_le P hB Θ (hθ.trans hθΘ)

/-- All nonnegative exponential window moments are finite on the actual Brownian path law. -/
theorem brownianUnitNorm_exponential_moment_lt_top (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p)) ∂P) < ⊤ :=
  lt_of_le_of_lt (brownianUnitNorm_exponential_moment_le P hB θ hθ)
    (brownianWindowExponentialConstant_lt_top θ)

/-- A deterministic restart preserves the full continuous Brownian path law. -/
theorem brownianPath_deterministic_shift_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (s : ℝ≥0) :
    P.map (brownianShiftPath s) = P := by
  apply brownianPath_measure_eq_of_process_map_eq
  have hm : Measurable (brownianShiftPath s) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map
    (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)) hm]
  exact brownian_shift_process_map_eq hB.toIsPreBrownianReal
    (fun t => ContinuousMap.measurable_eval t) s

/-- The unit-increment exponential estimate is uniform over every deterministic block start. -/
theorem brownianUnitIncrement_exponential_moment_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (s : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath s p))) ∂P) ≤
      brownianWindowExponentialConstant θ := by
  have hm : Measurable (fun p : BrownianPath =>
      ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p))) := by
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul continuous_brownianUnitNorm.measurable))
  have hs : Measurable (brownianShiftPath s) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have he := lintegral_map hm hs (μ := P)
  change (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p))
      ∂P.map (brownianShiftPath s)) =
    (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath s p))) ∂P) at he
  rw [brownianPath_deterministic_shift_map P hB s] at he
  rw [← he]
  exact brownianUnitNorm_exponential_moment_le P hB θ hθ

/-- Dropping the survival event except for its endpoint leaves an exponentially decaying
truncated drifted Gaussian moment, exactly as in the positive-block source argument. -/
theorem brownian_drift_truncated_exponential_moment_le
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (t : ℝ≥0) (ν θ : ℝ) (hν : 0 ≤ ν) (hθ : 0 ≤ θ) :
    (∫⁻ p in {p | p t - ν * t ≤ 1},
      ENNReal.ofReal (Real.exp (θ * (p t - ν * t))) ∂P) ≤
        ENNReal.ofReal (Real.exp (-θ * ν * t / 2)) +
          ENNReal.ofReal (Real.exp (θ - ν ^ 2 * t / 8)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Set BrownianPath := {p | -ν * t / 2 < p t - ν * t}
  have hE : MeasurableSet E := measurableSet_lt measurable_const
    ((ContinuousMap.measurable_eval t).sub measurable_const)
  have htail : P E ≤ ENNReal.ofReal (Real.exp (-ν ^ 2 * t / 8)) := by
    have hb := brownian_terminal_event_bound hB.toIsPreBrownianReal t (-ν / 2)
      (-ν ^ 2 * t / 4) E (fun p hp => by
        change -ν * t / 2 < p t - ν * t at hp
        have hn : 0 ≤ ν * (p t - ν * t / 2) := by
          apply mul_nonneg hν
          linarith
        nlinarith)
    have he : -ν ^ 2 * (t : ℝ) / 4 + (-ν / 2) ^ 2 * t / 2 = -ν ^ 2 * t / 8 := by ring
    simpa only [he] using hb
  have hcut : MeasurableSet {p : BrownianPath | p t - ν * t ≤ 1} :=
    measurableSet_le ((ContinuousMap.measurable_eval t).sub measurable_const) measurable_const
  rw [← lintegral_indicator hcut]
  have hbound : ∀ p : BrownianPath,
      {p | p t - ν * t ≤ 1}.indicator
        (fun p => ENNReal.ofReal (Real.exp (θ * (p t - ν * t)))) p ≤
      ENNReal.ofReal (Real.exp (-θ * ν * t / 2)) +
        E.indicator (fun _ => ENNReal.ofReal (Real.exp θ)) p := by
    intro p
    by_cases hp : p t - ν * t ≤ 1
    · rw [indicator_of_mem (show p ∈ {p : BrownianPath | p t - ν * t ≤ 1} from hp)]
      by_cases hpe : p ∈ E
      · rw [indicator_of_mem hpe]
        exact (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
          (by nlinarith))).trans (le_add_left le_rfl)
      · rw [indicator_of_notMem hpe, add_zero]
        change ¬ -ν * t / 2 < p t - ν * t at hpe
        have hprod := mul_le_mul_of_nonneg_left (le_of_not_gt hpe) hθ
        exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith))
    · rw [indicator_of_notMem (show p ∉ {p : BrownianPath | p t - ν * t ≤ 1} from hp)]
      exact bot_le
  calc
    _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (-θ * ν * t / 2)) +
        E.indicator (fun _ => ENNReal.ofReal (Real.exp θ)) p ∂P := lintegral_mono hbound
    _ = ENNReal.ofReal (Real.exp (-θ * ν * t / 2)) +
        ENNReal.ofReal (Real.exp θ) * P E := by
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_indicator hE, setLIntegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (Real.exp (-θ * ν * t / 2)) +
        ENNReal.ofReal (Real.exp θ) *
          ENNReal.ofReal (Real.exp (-ν ^ 2 * t / 8)) :=
      add_le_add le_rfl (mul_le_mul' le_rfl htail)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 3
      ring


/-- The two geometric decay sequences in the source block estimate are summable. -/
theorem summable_brownian_drift_exponential_decay (ν θ : ℝ)
    (hν : 0 < ν) (hθ : 0 < θ) :
    Summable (fun n : ℕ => Real.exp (-θ * ν * (n : ℝ) / 2) +
      Real.exp (θ - ν ^ 2 * (n : ℝ) / 8)) := by
  have ha : Summable (fun n : ℕ => Real.exp ((-θ * ν / 2) * (n : ℝ))) :=
    by
      simpa only [mul_comm] using
        (Real.summable_exp_nat_mul_iff (a := -θ * ν / 2)).mpr
          (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos hθ) hν) (by norm_num))
  have hb : Summable (fun n : ℕ => Real.exp ((-ν ^ 2 / 8) * (n : ℝ))) :=
    by
      simpa only [mul_comm] using
        (Real.summable_exp_nat_mul_iff (a := -ν ^ 2 / 8)).mpr
          (div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos hν)) (by norm_num))
  have he : (fun n : ℕ => Real.exp (-θ * ν * (n : ℝ) / 2) +
      Real.exp (θ - ν ^ 2 * (n : ℝ) / 8)) =
      fun n : ℕ => Real.exp ((-θ * ν / 2) * (n : ℝ)) +
        Real.exp θ * Real.exp ((-ν ^ 2 / 8) * (n : ℝ)) := by
    funext n
    rw [← Real.exp_add]
    congr 2 <;> ring
  rw [he]
  exact ha.add (hb.mul_left _)


/-- Every real exponential order is covered by the bound at its absolute value. -/
theorem brownianUnitNorm_exponential_moment_lt_top_all (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (θ : ℝ) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p)) ∂P) < ⊤ := by
  apply lt_of_le_of_lt (lintegral_mono (fun p =>
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (le_abs_self θ) (norm_nonneg _)))))
  exact brownianUnitNorm_exponential_moment_lt_top P hB |θ| (abs_nonneg _)



/-- The deterministic Gaussian-series constant increases with the exponential order. -/
theorem brownianWindowExponentialConstant_mono : Monotone brownianWindowExponentialConstant := by
  intro θ Θ hθ
  apply mul_le_mul' le_rfl
  apply ENNReal.tsum_le_tsum
  intro n
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ (n : ℝ) + 1)
  linarith

end DOZZ.Proofs
