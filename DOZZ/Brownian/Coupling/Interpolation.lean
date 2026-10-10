/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.FiniteGrid

/-!
# Continuous interpolation of the shared entrance grids

Join the zero entrance point to the first sampled value, interpolate consecutive grid values,
and extend constantly beyond the last grid time. The construction uses continuous clipped ramps,
so measurability on the compact-open path carrier follows directly from evaluation measurability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- A clipped affine ramp joining zero at `a` to one at `a + δ`. -/
noncomputable def couplingRamp (a δ t : ℝ) : ℝ := min 1 (max 0 ((t - a) / δ))

theorem continuous_couplingRamp (a δ : ℝ) : Continuous (couplingRamp a δ) := by
  unfold couplingRamp
  fun_prop

theorem couplingRamp_nonneg (a δ t : ℝ) : 0 ≤ couplingRamp a δ t :=
  le_min zero_le_one (le_max_left _ _)

theorem couplingRamp_le_one (a δ t : ℝ) : couplingRamp a δ t ≤ 1 := min_le_left _ _

theorem couplingRamp_eq_zero {a δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ a) :
    couplingRamp a δ t = 0 := by
  rw [couplingRamp, max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hδ.le)]
  norm_num

theorem couplingRamp_eq_one {a δ t : ℝ} (hδ : 0 < δ) (ht : a + δ ≤ t) :
    couplingRamp a δ t = 1 := by
  have hdiv : 1 ≤ (t - a) / δ := (le_div_iff₀ hδ).mpr (by linarith)
  exact min_eq_left (hdiv.trans (le_max_right _ _))

/-- The ramp's contribution to elapsed time never exceeds the elapsed time itself. -/
theorem couplingRamp_time_budget {a δ t : ℝ} (hδ : 0 < δ) (hat : a ≤ t) :
    couplingRamp a δ t * δ ≤ t - a := by
  have hdiv : 0 ≤ (t - a) / δ := div_nonneg (sub_nonneg.mpr hat) hδ.le
  rw [couplingRamp, max_eq_right hdiv]
  exact (mul_le_mul_of_nonneg_right (min_le_right _ _) hδ.le).trans_eq (div_mul_cancel₀ _ hδ.ne')

/-- Regard the ramp as an actual continuous path on nonnegative time. -/
noncomputable def couplingRampPath (a δ : ℝ) : BrownianPath :=
  ⟨fun t => couplingRamp a δ t, (continuous_couplingRamp a δ).comp NNReal.continuous_coe⟩

/-- Linearly interpolate positive finite entrance samples at times `(i+1)δ`. -/
noncomputable def couplingGridInterpolant (δ : ℝ) :
    (n : ℕ) → ConditionedEntranceGridPath n → BrownianPath
  | 0, x => (ContinuousMap.const _ (x 0).1) * couplingRampPath 0 δ
  | n + 1, x => couplingGridInterpolant δ n (Fin.init x) +
      (ContinuousMap.const _ ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1)) *
        couplingRampPath (((n : ℝ) + 1) * δ) δ

/-- The interpolated path depends measurably on every finite vector of sampled values. -/
theorem measurable_couplingGridInterpolant (δ : ℝ) (n : ℕ) :
    Measurable (couplingGridInterpolant δ n) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  induction n with
  | zero =>
      change Measurable (fun x : ConditionedEntranceGridPath 0 =>
        (x 0).1 * couplingRamp 0 δ (t : ℝ))
      exact (measurable_subtype_coe.comp (measurable_pi_apply 0)).mul_const _
  | succ n ih =>
      have hinit : Measurable (Fin.init : ConditionedEntranceGridPath (n + 1) →
          ConditionedEntranceGridPath n) :=
        measurable_pi_iff.mpr fun i => measurable_pi_apply i.castSucc
      change Measurable (fun x : ConditionedEntranceGridPath (n + 1) =>
        couplingGridInterpolant δ n (Fin.init x) t +
          ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) *
            couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ))
      exact (ih.comp hinit).add (((measurable_subtype_coe.comp
        (measurable_pi_apply (Fin.last (n + 1)))).sub
          (measurable_subtype_coe.comp (measurable_pi_apply (Fin.last n).castSucc))).mul_const _)

/-- Interpolation starts at the singular entrance point, on every finite sample vector. -/
theorem couplingGridInterpolant_zero {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : ConditionedEntranceGridPath n) : couplingGridInterpolant δ n x 0 = 0 := by
  induction n with
  | zero =>
      change (x 0).1 * couplingRamp 0 δ 0 = 0
      rw [couplingRamp_eq_zero hδ (le_refl 0), mul_zero]
  | succ n ih =>
      change couplingGridInterpolant δ n (Fin.init x) 0 + _ *
        couplingRamp (((n : ℝ) + 1) * δ) δ 0 = 0
      rw [ih, couplingRamp_eq_zero hδ (by positivity), mul_zero, add_zero]

/-- Beyond the terminal grid time, the interpolant is exactly its last sampled value. -/
theorem couplingGridInterpolant_terminal {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : ConditionedEntranceGridPath n) (t : ℝ≥0)
    (ht : ((n : ℝ) + 1) * δ ≤ (t : ℝ)) :
    couplingGridInterpolant δ n x t = (x (Fin.last n)).1 := by
  induction n with
  | zero =>
      change (x 0).1 * couplingRamp 0 δ (t : ℝ) = (x (Fin.last 0)).1
      rw [couplingRamp_eq_one hδ (by simpa using ht), mul_one]
      rfl
  | succ n ih =>
      have hprev : ((n : ℝ) + 1) * δ ≤ (t : ℝ) := by
        push_cast at ht
        nlinarith
      have hramp : couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = 1 :=
        couplingRamp_eq_one hδ (by push_cast at ht; nlinarith)
      change couplingGridInterpolant δ n (Fin.init x) t +
        ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) *
          couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
      rw [ih (Fin.init x) hprev, hramp, mul_one]
      change (x (Fin.last n).castSucc).1 +
        ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) = _
      ring

/-- Before a new segment begins, appending it leaves the old interpolation unchanged. -/
theorem couplingGridInterpolant_before_append {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : ConditionedEntranceGridPath (n + 1)) (t : ℝ≥0)
    (ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ) :
    couplingGridInterpolant δ (n + 1) x t = couplingGridInterpolant δ n (Fin.init x) t := by
  change couplingGridInterpolant δ n (Fin.init x) t + _ *
    couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
  rw [couplingRamp_eq_zero hδ ht, mul_zero, add_zero]

/-- On the new segment the interpolant is a convex combination of its two endpoint values. -/
theorem couplingGridInterpolant_after_append {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : ConditionedEntranceGridPath (n + 1)) (t : ℝ≥0)
    (ht : ((n : ℝ) + 1) * δ ≤ (t : ℝ)) :
    couplingGridInterpolant δ (n + 1) x t =
      (1 - couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ)) * (x (Fin.last n).castSucc).1 +
        couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) * (x (Fin.last (n + 1))).1 := by
  change couplingGridInterpolant δ n (Fin.init x) t + _ *
    couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
  rw [couplingGridInterpolant_terminal hδ n (Fin.init x) t ht]
  simp only [ContinuousMap.const_apply]
  change (x (Fin.last n).castSucc).1 +
    ((x (Fin.last (n + 1))).1 - (x (Fin.last n).castSucc).1) *
      couplingRamp (((n : ℝ) + 1) * δ) δ (t : ℝ) = _
  ring

/-- Grid interpolation preserves the two quantitative drift inequalities at every real time. -/
theorem couplingGridInterpolant_order {δ d : ℝ} (hδ : 0 < δ) (hd : 0 ≤ d)
    (n : ℕ) (x y : ConditionedEntranceGridPath n)
    (hxy : ∀ i : Fin (n + 1), (x i).1 ≤ (y i).1 ∧
      (y i).1 ≤ (x i).1 + d * (((i.val : ℝ) + 1) * δ))
    (t : ℝ≥0) : couplingGridInterpolant δ n x t ≤ couplingGridInterpolant δ n y t ∧
      couplingGridInterpolant δ n y t ≤ couplingGridInterpolant δ n x t + d * (t : ℝ) := by
  induction n with
  | zero =>
      have hx0 := hxy 0
      have hramp0 := couplingRamp_nonneg 0 δ (t : ℝ)
      have hbudget := couplingRamp_time_budget hδ t.2
      change (x 0).1 * couplingRamp 0 δ (t : ℝ) ≤
          (y 0).1 * couplingRamp 0 δ (t : ℝ) ∧
        (y 0).1 * couplingRamp 0 δ (t : ℝ) ≤
          (x 0).1 * couplingRamp 0 δ (t : ℝ) + d * (t : ℝ)
      have hupper := mul_le_mul_of_nonneg_right hx0.2 hramp0
      have hbudget' := mul_le_mul_of_nonneg_left hbudget hd
      simp only [Fin.val_zero, Nat.cast_zero, zero_add, one_mul, sub_zero] at hupper hbudget'
      constructor
      · exact mul_le_mul_of_nonneg_right hx0.1 hramp0
      · calc
          _ ≤ ((x 0).1 + d * δ) * couplingRamp 0 δ (t : ℝ) := hupper
          _ = (x 0).1 * couplingRamp 0 δ (t : ℝ) +
              d * (couplingRamp 0 δ (t : ℝ) * δ) := by ring
          _ ≤ _ := add_le_add_right hbudget' _
  | succ n ih =>
      by_cases ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ
      · rw [couplingGridInterpolant_before_append hδ n x t ht,
          couplingGridInterpolant_before_append hδ n y t ht]
        exact ih (Fin.init x) (Fin.init y) (fun i => hxy i.castSucc)
      · have ht' := (le_of_not_ge ht)
        rw [couplingGridInterpolant_after_append hδ n x t ht',
          couplingGridInterpolant_after_append hδ n y t ht']
        have hold := hxy (Fin.last n).castSucc
        have hnew := hxy (Fin.last (n + 1))
        simp only [Fin.val_castSucc, Fin.val_last, Nat.cast_add, Nat.cast_one] at hold hnew
        have hramp0 := couplingRamp_nonneg (((n : ℝ) + 1) * δ) δ (t : ℝ)
        have hramp1 := couplingRamp_le_one (((n : ℝ) + 1) * δ) δ (t : ℝ)
        have hbudget := couplingRamp_time_budget hδ ht'
        have hlold := mul_le_mul_of_nonneg_left hold.1 (sub_nonneg.mpr hramp1)
        have hlnew := mul_le_mul_of_nonneg_left hnew.1 hramp0
        have huold := mul_le_mul_of_nonneg_left hold.2 (sub_nonneg.mpr hramp1)
        have hunew := mul_le_mul_of_nonneg_left hnew.2 hramp0
        have hbudget' := mul_le_mul_of_nonneg_left hbudget hd
        constructor <;> nlinarith


/-- A positive sample vector gives a nonnegative interpolated path at every time. -/
theorem couplingGridInterpolant_nonneg {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : ConditionedEntranceGridPath n) (t : ℝ≥0) :
    0 ≤ couplingGridInterpolant δ n x t := by
  induction n with
  | zero =>
      change 0 ≤ (x 0).1 * couplingRamp 0 δ (t : ℝ)
      exact mul_nonneg (x 0).2.le (couplingRamp_nonneg _ _ _)
  | succ n ih =>
      by_cases ht : (t : ℝ) ≤ ((n : ℝ) + 1) * δ
      · rw [couplingGridInterpolant_before_append hδ n x t ht]
        exact ih (Fin.init x)
      · rw [couplingGridInterpolant_after_append hδ n x t (le_of_not_ge ht)]
        exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr (couplingRamp_le_one _ _ _))
            (x (Fin.last n).castSucc).2.le)
          (mul_nonneg (couplingRamp_nonneg _ _ _) (x (Fin.last (n + 1))).2.le)

/-- Uniform-grid elapsed times match the affine interpolation endpoints exactly. -/
theorem coupledEntranceGridTime_uniform (δ : ℝ) (n : ℕ) :
    coupledEntranceGridTime δ (fun _ => δ) n = ((n : ℝ) + 1) * δ := by
  simp only [coupledEntranceGridTime, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Reflect all finite-grid interpolants into the negative path convention. -/
noncomputable def couplingInterpolatedFamily {J : Type*} (δ : ℝ) (n : ℕ)
    (x : CoupledEntranceGridPath J n) : J → BrownianPath :=
  fun j => -(couplingGridInterpolant δ n (x j))

theorem measurable_couplingInterpolatedFamily {J : Type*} (δ : ℝ) (n : ℕ) :
    Measurable (couplingInterpolatedFamily (J := J) δ n) :=
  measurable_pi_iff.mpr fun j =>
    ((measurable_couplingGridInterpolant δ n).comp (measurable_pi_apply j)).neg

/-- Simultaneous grid order yields simultaneous continuous-path order, at every time. -/
theorem couplingInterpolatedFamily_mem_orderSet {J : Type*}
    (v : J → ℝ≥0) {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : CoupledEntranceGridPath J n)
    (hx : x ∈ coupledEntranceGridOrderSet v δ (fun _ => δ) n) :
    couplingInterpolatedFamily δ n x ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  intro j k _ hjk t
  have hjk' : v j ≤ v k := hjk
  have hxy : ∀ i : Fin (n + 1), (x j i).1 ≤ (x k i).1 ∧
      (x k i).1 ≤ (x j i).1 + ((v k : ℝ) - (v j : ℝ)) * (((i.val : ℝ) + 1) * δ) := by
    intro i
    simpa only [coupledEntranceGridTime_uniform] using hx j k hjk' i
  obtain ⟨hlo, hhi⟩ := couplingGridInterpolant_order hδ (sub_nonneg.mpr hjk) n
    (x j) (x k) hxy t
  change -couplingGridInterpolant δ n (x k) t ≤ -couplingGridInterpolant δ n (x j) t ∧
    -couplingGridInterpolant δ n (x j) t ≤
      -couplingGridInterpolant δ n (x k) t + ((v k : ℝ) - (v j : ℝ)) * (t : ℝ)
  constructor <;> linarith

/-- The actual continuous-path joint grid law. -/
noncomputable def couplingInterpolatedGridMeasure {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : Measure (J → BrownianPath) :=
  (coupledEntranceGridMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n).map
    (couplingInterpolatedFamily δ n)

theorem couplingInterpolatedGridMeasure_isProbabilityMeasure {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    IsProbabilityMeasure (couplingInterpolatedGridMeasure v δ hδ n) := by
  let _ := coupledEntranceGridMeasure_isProbabilityMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_couplingInterpolatedFamily δ n).aemeasurable).mpr inferInstance

/-- Continuous interpolation introduces no error into the full marginal finite-grid law. -/
theorem couplingInterpolatedGridMeasure_coordinate_map {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) (j : J) :
    (couplingInterpolatedGridMeasure v δ hδ n).map (fun F => F j) =
    (conditionedPositiveEntranceGridMeasure (v j) δ (fun _ => δ) (NNReal.coe_nonneg (v j))
      hδ (fun _ => hδ) n).map (fun x => -(couplingGridInterpolant δ n x)) := by
  rw [couplingInterpolatedGridMeasure, Measure.map_map (measurable_pi_apply j)
    (measurable_couplingInterpolatedFamily δ n)]
  change (coupledEntranceGridMeasure v δ (fun _ => δ) hδ (fun _ => hδ) n).map
    ((fun x => -(couplingGridInterpolant δ n x)) ∘ (fun x => x j)) = _
  have hnegative : Measurable (fun x : ConditionedEntranceGridPath n =>
      -(couplingGridInterpolant δ n x)) := (measurable_couplingGridInterpolant δ n).neg
  rw [← Measure.map_map hnegative (measurable_pi_apply j),
    coupledEntranceGridMeasure_coordinate_map]

/-- The common all-time order event is preserved by the actual interpolation pushforward. -/
theorem couplingInterpolatedGridMeasure_order_ae {J : Type*} [Countable J]
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∀ᵐ F ∂couplingInterpolatedGridMeasure v δ hδ n,
      F ∈ negativeEntranceOrderSet (fun j => (v j : ℝ)) := by
  apply (ae_map_iff (measurable_couplingInterpolatedFamily δ n).aemeasurable
    (isClosed_negativeEntranceOrderSet (fun j => (v j : ℝ))).measurableSet).mpr
  exact (coupledEntranceGridMeasure_order_ae v δ (fun _ => δ) hδ (fun _ => hδ) n).mono
    fun x hx => couplingInterpolatedFamily_mem_orderSet v hδ n x hx

/-- The samplewise interpolation has a zero start in every drift coordinate. -/
theorem couplingInterpolatedFamily_zero {J : Type*} {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : CoupledEntranceGridPath J n) (j : J) : couplingInterpolatedFamily δ n x j 0 = 0 := by
  change -couplingGridInterpolant δ n (x j) 0 = 0
  rw [couplingGridInterpolant_zero hδ, neg_zero]

/-- Every interpolated negative half-path stays nonpositive samplewise. -/
theorem couplingInterpolatedFamily_nonpos {J : Type*} {δ : ℝ} (hδ : 0 < δ) (n : ℕ)
    (x : CoupledEntranceGridPath J n) (j : J) (t : ℝ≥0) :
    couplingInterpolatedFamily δ n x j t ≤ 0 := by
  change -couplingGridInterpolant δ n (x j) t ≤ 0
  exact neg_nonpos.mpr (couplingGridInterpolant_nonneg hδ n (x j) t)


/-- The joint interpolation law in the probability-measure carrier used by Prokhorov. -/
noncomputable def couplingInterpolatedGridProbability {J : Type*}
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ProbabilityMeasure (J → BrownianPath) :=
  ⟨couplingInterpolatedGridMeasure v δ hδ n,
    couplingInterpolatedGridMeasure_isProbabilityMeasure v δ hδ n⟩

/-- All-time nonpositivity is a closed constraint on the countable product path carrier. -/
theorem isClosed_couplingNegativeFamily {J : Type*} :
    IsClosed {F : J → BrownianPath | ∀ j (t : ℝ≥0), F j t ≤ 0} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro j
  exact isClosed_iInter fun t => isClosed_le
    ((continuous_eval_const t).comp (continuous_apply j)) continuous_const

/-- The actual joint interpolated grid law is supported on nonpositive half-paths. -/
theorem couplingInterpolatedGridMeasure_nonpos_ae {J : Type*} [Countable J]
    (v : J → ℝ≥0) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    ∀ᵐ F ∂couplingInterpolatedGridMeasure v δ hδ n, ∀ j (t : ℝ≥0), F j t ≤ 0 := by
  apply (ae_map_iff (measurable_couplingInterpolatedFamily δ n).aemeasurable
    (isClosed_couplingNegativeFamily (J := J)).measurableSet).mpr
  exact ae_of_all _ fun x j t => couplingInterpolatedFamily_nonpos hδ n x j t





end DOZZ.Proofs
