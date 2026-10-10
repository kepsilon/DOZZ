/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-! Convergence in measure is stable under an independent finite scalar multiplier. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- Multiplying a sequence converging in measure by a finite random scalar on an independent
product space preserves convergence in measure. The proof truncates the scalar and controls its
tail using continuity from above for a finite measure. -/
theorem tendstoInMeasure_mul_snd_of_tendstoInMeasure
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (W : Ω' → ℝ)
    (hW : Measurable W) (hfg : TendstoInMeasure P f atTop g) :
    TendstoInMeasure (P.prod Q) (fun n p => W p.2 * f n p.1)
      atTop (fun p => W p.2 * g p.1) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro δ hδ
  let T : ℕ → Set Ω' := fun n => {w | (n : ℝ) < |W w|}
  have hTmeas (n : ℕ) : MeasurableSet (T n) := by
    dsimp [T]
    measurability
  have hTanti : Antitone T := by
    intro n m hnm w hw
    change (m : ℝ) < |W w| at hw
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hw
  have hTinter : (⋂ n, T n) = ∅ := by
    ext w
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hw
    obtain ⟨n, hn⟩ := exists_nat_gt (|W w|)
    have hwn := hw n
    change (n : ℝ) < |W w| at hwn
    exact (not_lt_of_ge (le_of_lt hn)) hwn
  have hTlimit : Tendsto (fun n => Q (T n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := Q) (s := T)
      (fun n => (hTmeas n).nullMeasurableSet) hTanti ⟨0, measure_ne_top Q _⟩
    change Tendsto (fun n => Q (T n)) atTop (𝓝 (Q (⋂ n, T n))) at h
    rw [hTinter, measure_empty] at h
    exact h
  obtain ⟨N₁, hN₁⟩ := (ENNReal.tendsto_atTop_zero.mp hTlimit) (δ / 2)
    (ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩)
  let K : ℝ := (N₁ : ℝ) + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hKtail : Q {w | K < |W w|} ≤ δ / 2 := by
    have h := hN₁ (N₁ + 1) (by omega)
    simpa [T, K, Nat.cast_add, Nat.cast_one] using h
  have hbase : Tendsto (fun n => P {ω | ε / K ≤ ‖f n ω - g ω‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_norm.mp hfg) (ε / K) (div_pos hε hK)
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp hbase) (δ / 2)
    (ENNReal.div_pos_iff.mpr ⟨hδ.ne', by simp⟩)
  refine ⟨N₂, fun n hn => ?_⟩
  let B : Set Ω := {ω | ε / K ≤ ‖f n ω - g ω‖}
  let bad : Set (Ω × Ω') := {p | ε ≤ ‖W p.2 * f n p.1 - W p.2 * g p.1‖}
  have hsubset : bad ⊆ (Set.univ ×ˢ {w | K < |W w|}) ∪ (B ×ˢ Set.univ) := by
    intro p hp
    by_contra hnot
    have hnotT : ¬ K < |W p.2| := by
      intro h
      exact hnot (Or.inl ⟨Set.mem_univ _, h⟩)
    have hnotB : ¬ ε / K ≤ ‖f n p.1 - g p.1‖ := by
      intro h
      exact hnot (Or.inr ⟨h, Set.mem_univ _⟩)
    have hW : |W p.2| ≤ K := le_of_not_gt hnotT
    have hdiff : ‖f n p.1 - g p.1‖ < ε / K := lt_of_not_ge hnotB
    have hmul : |W p.2| * ‖f n p.1 - g p.1‖ < ε := by
      calc
        |W p.2| * ‖f n p.1 - g p.1‖ ≤ K * ‖f n p.1 - g p.1‖ :=
          mul_le_mul_of_nonneg_right hW (norm_nonneg _)
        _ < K * (ε / K) := mul_lt_mul_of_pos_left hdiff hK
        _ = ε := by field_simp
    change ε ≤ ‖W p.2 * f n p.1 - W p.2 * g p.1‖ at hp
    have hfactor : W p.2 * f n p.1 - W p.2 * g p.1 =
        W p.2 * (f n p.1 - g p.1) := by ring
    rw [hfactor, Real.norm_eq_abs, abs_mul] at hp
    have hmul' : |W p.2| * |f n p.1 - g p.1| < ε := by
      simpa only [Real.norm_eq_abs] using hmul
    exact (not_le_of_gt hmul') hp
  calc
    (P.prod Q) bad ≤ (P.prod Q)
        ((Set.univ ×ˢ {w | K < |W w|}) ∪ (B ×ˢ Set.univ)) := measure_mono hsubset
    _ ≤ (P.prod Q) (Set.univ ×ˢ {w | K < |W w|}) +
        (P.prod Q) (B ×ˢ Set.univ) := measure_union_le _ _
    _ = Q {w | K < |W w|} + P B := by simp [Measure.prod_prod]
    _ ≤ δ / 2 + δ / 2 := add_le_add hKtail (hN₂ n hn)
    _ = δ := ENNReal.add_halves δ

end DOZZ.Proofs
