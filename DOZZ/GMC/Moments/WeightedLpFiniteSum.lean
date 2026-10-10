/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Finite-sum Minkowski inequality for extended nonnegative random variables. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The `Lᵖ` size of a finite sum of nonnegative extended-valued functions is bounded by the
sum of the individual `Lᵖ` sizes, for every `p ≥ 1`. -/
theorem ennreal_lintegral_rpow_finset_sum_root_le
    {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (s : Finset ι) (f : ι → Ω → ℝ≥0∞) (p : ℝ) (hp : 1 ≤ p)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    (∫⁻ ω, (∑ i ∈ s, f i ω) ^ p ∂μ) ^ (1 / p) ≤
      ∑ i ∈ s, (∫⁻ ω, f i ω ^ p ∂μ) ^ (1 / p) := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro hf
      have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
      simp_all [lintegral_const, ENNReal.zero_rpow_of_pos]
  | @insert i s his ih =>
      intro hf
      have hsum : AEMeasurable (fun ω => ∑ j ∈ s, f j ω) μ :=
        Finset.aemeasurable_fun_sum s (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hadd := ENNReal.lintegral_Lp_add_le
        (hf i (Finset.mem_insert_self i s)) hsum hp
      simp_rw [Finset.sum_insert his]
      calc
        _ ≤ (∫⁻ ω, f i ω ^ p ∂μ) ^ (1 / p) +
            (∫⁻ ω, (∑ j ∈ s, f j ω) ^ p ∂μ) ^ (1 / p) := hadd
        _ ≤ (∫⁻ ω, f i ω ^ p ∂μ) ^ (1 / p) +
            ∑ j ∈ s, (∫⁻ ω, f j ω ^ p ∂μ) ^ (1 / p) := by
          exact add_le_add le_rfl
            (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The finite-sum Minkowski bound extends to a countable nonnegative sum whenever the series of
the individual `Lᵖ` roots is finite. -/
theorem ennreal_lintegral_rpow_tsum_le_of_roots_summable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ℕ → Ω → ℝ≥0∞) (p : ℝ) (hp : 1 ≤ p)
    (hf : ∀ n, AEMeasurable (f n) μ) :
    ∫⁻ ω, (∑' n : ℕ, f n ω) ^ p ∂μ ≤
      (∑' n : ℕ, (∫⁻ ω, f n ω ^ p ∂μ) ^ (1 / p)) ^ p := by
  classical
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let partialSum (N : ℕ) (ω : Ω) : ℝ≥0∞ := ∑ n ∈ Finset.range N, f n ω
  let partialPow (N : ℕ) (ω : Ω) : ℝ≥0∞ := partialSum N ω ^ p
  let root (n : ℕ) : ℝ≥0∞ := (∫⁻ ω, f n ω ^ p ∂μ) ^ (1 / p)
  let roots : ℝ≥0∞ := ∑' n : ℕ, root n
  have hpartialMeas (N : ℕ) : AEMeasurable (partialSum N) μ := by
    exact Finset.aemeasurable_fun_sum _ (fun n hn => hf n)
  have hpartialPowMeas (N : ℕ) : AEMeasurable (partialPow N) μ := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hpartialMeas N)
  have hpartialMono : Monotone partialSum := by
    intro N M hNM ω
    dsimp [partialSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      (fun _ _ _ => bot_le)
  have hpowMono : Monotone (fun x : ℝ≥0∞ => x ^ p) := fun _ _ h =>
    ENNReal.rpow_le_rpow h hp0.le
  have hpowZero : (0 : ℝ≥0∞) ^ p = 0 := ENNReal.zero_rpow_of_pos hp0
  have hpowCont : Continuous (fun x : ℝ≥0∞ => x ^ p) :=
    ENNReal.continuous_rpow_const
  have hpoint (ω : Ω) : (∑' n : ℕ, f n ω) ^ p = ⨆ N, partialPow N ω := by
    calc
      (∑' n : ℕ, f n ω) ^ p = (⨆ N, partialSum N ω) ^ p := by
        rw [ENNReal.tsum_eq_iSup_nat]
      _ = ⨆ N, partialSum N ω ^ p :=
        hpowMono.map_iSup_of_continuousAt hpowCont.continuousAt hpowZero
      _ = _ := rfl
  have hmonoPow : Monotone partialPow := by
    intro N M hNM ω
    exact ENNReal.rpow_le_rpow (hpartialMono hNM ω) hp0.le
  have htotal : (∫⁻ ω, (∑' n : ℕ, f n ω) ^ p ∂μ) =
      ⨆ N, ∫⁻ ω, partialPow N ω ∂μ := by
    calc
      _ = ∫⁻ ω, ⨆ N, partialPow N ω ∂μ := by
        apply lintegral_congr
        exact hpoint
      _ = _ := lintegral_iSup' hpartialPowMeas
        (ae_of_all μ fun ω => fun N M hNM => hmonoPow hNM ω)
  rw [htotal]
  apply iSup_le
  intro N
  have hmink := ennreal_lintegral_rpow_finset_sum_root_le
    (Finset.range N) f p hp (fun n hn => hf n)
  have hfiniteRoots : (∑ n ∈ Finset.range N, root n) ≤ roots := by
    dsimp [roots, root]
    exact ENNReal.sum_le_tsum _
  have hrootBound : (∫⁻ ω, partialSum N ω ^ p ∂μ) ^ (1 / p) ≤ roots := by
    exact hmink.trans hfiniteRoots
  have hpowId : (∫⁻ ω, partialSum N ω ^ p ∂μ) =
      ((∫⁻ ω, partialSum N ω ^ p ∂μ) ^ (1 / p)) ^ p := by
    rw [← ENNReal.rpow_mul]
    rw [show 1 / p * p = 1 by field_simp [ne_of_gt hp0], ENNReal.rpow_one]
  rw [hpowId]
  exact ENNReal.rpow_le_rpow hrootBound hp0.le

end DOZZ.Proofs
