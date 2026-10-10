/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Prod
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace DOZZ.Proofs

/-- A finite correlated scalar preserves convergence in probability. No independence is used. -/
theorem tendstoInMeasure_mul_same_space
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {l : Filter ι} (f : ι → Ω → ℝ) (g W : Ω → ℝ)
    (hW : Measurable W) (hfg : TendstoInMeasure P f l g) :
    TendstoInMeasure P (fun i ω => W ω * f i ω) l (fun ω => W ω * g ω) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  let T : ℕ → Set Ω := fun n => {ω | (n : ℝ) < |W ω|}
  have hTmeas n : MeasurableSet (T n) :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp hW)
  have hTanti : Antitone T := by
    intro n m hnm ω hω
    change (m : ℝ) < |W ω| at hω
    change (n : ℝ) < |W ω|
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hω
  have hTinter : (⋂ n, T n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro h
    obtain ⟨n, hn⟩ := exists_nat_gt |W ω|
    exact (not_lt_of_ge hn.le) (h n)
  have htail : Tendsto (fun n => P (T n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := P) (s := T)
      (fun n => (hTmeas n).nullMeasurableSet) hTanti ⟨0, measure_ne_top P _⟩
    simpa only [hTinter, measure_empty, Function.comp_def] using h
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp htail) (δ / 2)
    (ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩)
  let K : ℝ := (N : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKtail : P {ω | K < |W ω|} ≤ δ / 2 := by
    simpa [T, K, Nat.cast_add, Nat.cast_one] using hN (N + 1) (by omega)
  have hbase := (tendstoInMeasure_iff_norm.mp hfg) (ε / K) (div_pos hε hK)
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hbase) (δ / 2)
    (ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩)] with i hi
  have hsubset : {ω | ε ≤ ‖W ω * f i ω - W ω * g ω‖} ⊆
      {ω | K < |W ω|} ∪ {ω | ε / K ≤ ‖f i ω - g ω‖} := by
    intro ω hω
    by_contra hnot
    have hnot' := not_or.mp hnot
    have hW' : |W ω| ≤ K := le_of_not_gt hnot'.1
    have hd : ‖f i ω - g ω‖ < ε / K := lt_of_not_ge hnot'.2
    have hh : ‖W ω * f i ω - W ω * g ω‖ < ε := by
      rw [← mul_sub, norm_mul, Real.norm_eq_abs]
      calc
        _ ≤ K * ‖f i ω - g ω‖ := mul_le_mul_of_nonneg_right hW' (norm_nonneg _)
        _ < K * (ε / K) := mul_lt_mul_of_pos_left hd hK
        _ = ε := mul_div_cancel₀ ε hK.ne'
    exact (not_le_of_gt hh) hω
  calc
    _ ≤ P ({ω | K < |W ω|} ∪ {ω | ε / K ≤ ‖f i ω - g ω‖}) := measure_mono hsubset
    _ ≤ P {ω | K < |W ω|} + P {ω | ε / K ≤ ‖f i ω - g ω‖} := measure_union_le _ _
    _ ≤ δ / 2 + δ / 2 := add_le_add hKtail hi
    _ = δ := ENNReal.add_halves δ

/-- Correlated real differences preserve convergence in probability. -/
theorem tendstoInMeasure_sub_same_space
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} {l : Filter ι}
    (f g : ι → Ω → ℝ) (F G : Ω → ℝ)
    (hf : TendstoInMeasure P f l F) (hg : TendstoInMeasure P g l G) :
    TendstoInMeasure P (fun i ω => f i ω - g i ω) l (fun ω => F ω - G ω) := by
  rw [tendstoInMeasure_iff_norm] at hf hg ⊢
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have ht : Tendsto (fun i => P {ω | ε / 2 ≤ ‖f i ω - F ω‖} +
      P {ω | ε / 2 ≤ ‖g i ω - G ω‖}) l (𝓝 0) := by
    simpa only [zero_add] using (hf (ε / 2) hhalf).add (hg (ε / 2) hhalf)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ≥0∞)) l (𝓝 0)) ht (fun _ => bot_le)
  intro i
  calc
    _ ≤ P ({ω | ε / 2 ≤ ‖f i ω - F ω‖} ∪ {ω | ε / 2 ≤ ‖g i ω - G ω‖}) := by
      apply measure_mono
      intro ω hω
      by_contra hnot
      have hn := not_or.mp hnot
      have h1 : ‖f i ω - F ω‖ < ε / 2 := lt_of_not_ge hn.1
      have h2 : ‖g i ω - G ω‖ < ε / 2 := lt_of_not_ge hn.2
      have heq : (f i ω - g i ω) - (F ω - G ω) =
          (f i ω - F ω) - (g i ω - G ω) := by ring
      have hb := norm_sub_le (f i ω - F ω) (g i ω - G ω)
      change ε ≤ ‖(f i ω - g i ω) - (F ω - G ω)‖ at hω
      rw [heq] at hω
      exact (not_le_of_gt (lt_of_le_of_lt hb (by linarith only [h1, h2]))) hω
    _ ≤ _ := measure_union_le _ _
end DOZZ.Proofs
