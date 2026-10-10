/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Convergence in probability toolkit

A small toolkit about convergence in measure of real random variables on a finite measure space.
It contains a continuous mapping theorem (for one and for two sequences) together with its
consequences for sums, products, deterministic scalar multiples and finite sums, an approximation
lemma, a lemma turning domination by a sequence converging in measure into smallness in
probability, and the dominated convergence theorem for convergence in measure.  The proofs go
through the subsequence criterion `MeasureTheory.exists_seq_tendstoInMeasure_atTop_iff`. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- Continuous mapping theorem for convergence in measure of two real sequences. -/
theorem bpz_tendstoInMeasure_map₂ {f g : ℕ → Ω → ℝ} {f₀ g₀ : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hfc : TendstoInMeasure P f atTop f₀) (hgc : TendstoInMeasure P g atTop g₀)
    (Φ : ℝ → ℝ → ℝ) (hΦm : Measurable (Function.uncurry Φ))
    (hΦ : ∀ᵐ ω ∂P, ContinuousAt (Function.uncurry Φ) (f₀ ω, g₀ ω)) :
    TendstoInMeasure P (fun n ω => Φ (f n ω) (g n ω)) atTop (fun ω => Φ (f₀ ω) (g₀ ω)) := by
  have hmeas : ∀ n, AEStronglyMeasurable (fun ω => Φ (f n ω) (g n ω)) P := fun n =>
    (hΦm.comp_aemeasurable ((hf n).aemeasurable.prodMk (hg n).aemeasurable)).aestronglyMeasurable
  rw [exists_seq_tendstoInMeasure_atTop_iff hmeas]
  intro ns hns
  obtain ⟨ns', hns', hfae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hf).1 hfc ns hns
  obtain ⟨ns'', hns'', hgae⟩ :=
    (exists_seq_tendstoInMeasure_atTop_iff hg).1 hgc (ns ∘ ns') (hns.comp hns')
  refine ⟨ns' ∘ ns'', hns'.comp hns'', ?_⟩
  filter_upwards [hfae, hgae, hΦ] with ω hfω hgω hΦω
  exact hΦω.tendsto.comp ((hfω.comp hns''.tendsto_atTop).prodMk_nhds hgω)


theorem bpz_tendstoInMeasure_add {f g : ℕ → Ω → ℝ} {f₀ g₀ : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hfc : TendstoInMeasure P f atTop f₀) (hgc : TendstoInMeasure P g atTop g₀) :
    TendstoInMeasure P (fun n ω => f n ω + g n ω) atTop (fun ω => f₀ ω + g₀ ω) :=
  bpz_tendstoInMeasure_map₂ hf hg hfc hgc (fun x y => x + y) measurable_add
    (Eventually.of_forall fun _ => continuous_add.continuousAt)

theorem bpz_tendstoInMeasure_mul {f g : ℕ → Ω → ℝ} {f₀ g₀ : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hfc : TendstoInMeasure P f atTop f₀) (hgc : TendstoInMeasure P g atTop g₀) :
    TendstoInMeasure P (fun n ω => f n ω * g n ω) atTop (fun ω => f₀ ω * g₀ ω) :=
  bpz_tendstoInMeasure_map₂ hf hg hfc hgc (fun x y => x * y) measurable_mul
    (Eventually.of_forall fun _ => continuous_mul.continuousAt)

/-- A deterministic convergent scalar sequence times a sequence converging in measure. -/
theorem bpz_tendstoInMeasure_const_mul_of_tendsto {c : ℕ → ℝ} {c₀ : ℝ}
    (hc : Tendsto c atTop (𝓝 c₀)) {f : ℕ → Ω → ℝ} {f₀ : Ω → ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) P) (hfc : TendstoInMeasure P f atTop f₀) :
    TendstoInMeasure P (fun n ω => c n * f n ω) atTop (fun ω => c₀ * f₀ ω) := by
  have hcm : ∀ n, AEStronglyMeasurable (fun _ : Ω => c n) P := fun _ => aestronglyMeasurable_const
  exact bpz_tendstoInMeasure_mul hcm hf
    (tendstoInMeasure_of_tendsto_ae hcm (Eventually.of_forall fun _ => hc)) hfc

theorem bpz_tendstoInMeasure_finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℕ → Ω → ℝ}
    {f₀ : ι → Ω → ℝ} (hf : ∀ i n, AEStronglyMeasurable (f i n) P)
    (hc : ∀ i ∈ s, TendstoInMeasure P (f i) atTop (f₀ i)) :
    TendstoInMeasure P (fun n ω => ∑ i ∈ s, f i n ω) atTop (fun ω => ∑ i ∈ s, f₀ i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => tendsto_const_nhds)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact bpz_tendstoInMeasure_add (hf a)
      (fun n => Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i n)
      (hc a (Finset.mem_insert_self a s))
      (ih fun i hi => hc i (Finset.mem_insert_of_mem hi))

omit [IsFiniteMeasure P]

/-- Approximation lemma: uniform-in-probability approximation by convergent sequences. -/
theorem bpz_tendstoInMeasure_of_approx {Z : ℕ → Ω → ℝ} {Z₀ : Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (A : ℕ → Ω → ℝ) (A₀ : Ω → ℝ), TendstoInMeasure P A atTop A₀ ∧
      (∀ᶠ n in atTop, P {ω | ε ≤ |Z n ω - A n ω|} ≤ ENNReal.ofReal ε) ∧
      P {ω | ε ≤ |Z₀ ω - A₀ ω|} ≤ ENNReal.ofReal ε) :
    TendstoInMeasure P Z atTop Z₀ := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨r, -, hr0, hrδ⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hr : 0 < r := ENNReal.ofReal_pos.1 hr0
  have hε' : 0 < min (ε / 3) (r / 3) := lt_min (by positivity) (by positivity)
  obtain ⟨A, A₀, hA, hZA, hZA₀⟩ := h _ hε'
  have hAc := ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_norm.1 hA) _ hε') _
    (ENNReal.ofReal_pos.2 hε')
  filter_upwards [hZA, hAc] with n hn1 hn2
  have hsub : {ω | ε ≤ ‖Z n ω - Z₀ ω‖} ⊆
      ({ω | min (ε / 3) (r / 3) ≤ |Z n ω - A n ω|} ∪
        {ω | min (ε / 3) (r / 3) ≤ ‖A n ω - A₀ ω‖}) ∪
        {ω | min (ε / 3) (r / 3) ≤ |Z₀ ω - A₀ ω|} := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs] at hcon hω
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    rw [abs_sub_comm] at h3
    have htri : |Z n ω - Z₀ ω| ≤ |Z n ω - A n ω| + |A n ω - A₀ ω| + |A₀ ω - Z₀ ω| := by
      calc |Z n ω - Z₀ ω| = |(Z n ω - A n ω) + (A n ω - A₀ ω) + (A₀ ω - Z₀ ω)| := by
            congr 1; ring
        _ ≤ |(Z n ω - A n ω) + (A n ω - A₀ ω)| + |A₀ ω - Z₀ ω| := abs_add_le _ _
        _ ≤ |Z n ω - A n ω| + |A n ω - A₀ ω| + |A₀ ω - Z₀ ω| := by
            gcongr; exact abs_add_le _ _
    have hm1 : min (ε / 3) (r / 3) ≤ ε / 3 := min_le_left _ _
    linarith
  have hm : min (ε / 3) (r / 3) + min (ε / 3) (r / 3) + min (ε / 3) (r / 3) ≤ r := by
    have := min_le_right (ε / 3) (r / 3)
    linarith
  calc P {ω | ε ≤ ‖Z n ω - Z₀ ω‖}
      ≤ P (({ω | min (ε / 3) (r / 3) ≤ |Z n ω - A n ω|} ∪
        {ω | min (ε / 3) (r / 3) ≤ ‖A n ω - A₀ ω‖}) ∪
        {ω | min (ε / 3) (r / 3) ≤ |Z₀ ω - A₀ ω|}) := measure_mono hsub
    _ ≤ (P {ω | min (ε / 3) (r / 3) ≤ |Z n ω - A n ω|} +
          P {ω | min (ε / 3) (r / 3) ≤ ‖A n ω - A₀ ω‖}) +
          P {ω | min (ε / 3) (r / 3) ≤ |Z₀ ω - A₀ ω|} :=
        (measure_union_le _ _).trans (add_le_add_left (measure_union_le _ _) _)
    _ ≤ (ENNReal.ofReal (min (ε / 3) (r / 3)) + ENNReal.ofReal (min (ε / 3) (r / 3))) +
          ENNReal.ofReal (min (ε / 3) (r / 3)) := by gcongr
    _ = ENNReal.ofReal (min (ε / 3) (r / 3) + min (ε / 3) (r / 3) + min (ε / 3) (r / 3)) := by
        rw [ENNReal.ofReal_add (add_nonneg hε'.le hε'.le) hε'.le,
          ENNReal.ofReal_add hε'.le hε'.le]
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hm
    _ ≤ δ := hrδ.le

/-- An error dominated by a sequence converging in measure is eventually small in probability
when the limit is small in probability. -/
theorem bpz_eventually_measure_le_of_le_tendstoInMeasure {E B : ℕ → Ω → ℝ} {B₀ : Ω → ℝ}
    (hB : TendstoInMeasure P B atTop B₀) (hEB : ∀ n, ∀ᵐ ω ∂P, |E n ω| ≤ B n ω) {ε : ℝ}
    (hε : 0 < ε) (hB₀ : P {ω | ε / 2 ≤ B₀ ω} < ENNReal.ofReal ε) :
    ∀ᶠ n in atTop, P {ω | ε ≤ |E n ω|} ≤ ENNReal.ofReal ε := by
  have hg : 0 < ENNReal.ofReal ε - P {ω | ε / 2 ≤ B₀ ω} := tsub_pos_of_lt hB₀
  have hBc := ENNReal.tendsto_nhds_zero.1 ((tendstoInMeasure_iff_norm.1 hB) (ε / 2) (half_pos hε))
    _ hg
  filter_upwards [hBc] with n hn
  have hsub : {ω | ε ≤ |E n ω|} ≤ᵐ[P]
      ({ω | ε / 2 ≤ B₀ ω} ∪ {ω | ε / 2 ≤ ‖B n ω - B₀ ω‖} : Set Ω) := by
    filter_upwards [hEB n] with ω hω hεω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, Real.norm_eq_abs] at hcon
    obtain ⟨h1, h2⟩ := hcon
    have h3 : B n ω - B₀ ω ≤ |B n ω - B₀ ω| := le_abs_self _
    linarith
  calc P {ω | ε ≤ |E n ω|}
      ≤ P ({ω | ε / 2 ≤ B₀ ω} ∪ {ω | ε / 2 ≤ ‖B n ω - B₀ ω‖}) := measure_mono_ae hsub
    _ ≤ P {ω | ε / 2 ≤ B₀ ω} + P {ω | ε / 2 ≤ ‖B n ω - B₀ ω‖} := measure_union_le _ _
    _ ≤ P {ω | ε / 2 ≤ B₀ ω} + (ENNReal.ofReal ε - P {ω | ε / 2 ≤ B₀ ω}) := by gcongr
    _ = ENNReal.ofReal ε := add_tsub_cancel_of_le hB₀.le

/-- Dominated convergence for convergence in measure. -/
theorem bpz_tendsto_integral_of_tendstoInMeasure {Z : ℕ → Ω → ℝ} {Z₀ : Ω → ℝ} {W : Ω → ℝ}
    (hZm : ∀ n, AEStronglyMeasurable (Z n) P) (hc : TendstoInMeasure P Z atTop Z₀)
    (hW : Integrable W P) (hb : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ W ω) :
    Tendsto (fun n => ∫ ω, Z n ω ∂P) atTop (𝓝 (∫ ω, Z₀ ω ∂P)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, -, hae⟩ := (hc.comp hns).exists_seq_tendsto_ae
  exact ⟨ms, tendsto_integral_of_dominated_convergence W (fun k => hZm (ns (ms k))) hW
    (fun k => by simpa only [Real.norm_eq_abs] using hb (ns (ms k))) hae⟩

/-- Two sequences with equal expectations and dominated, in-measure convergent integrands have
limits with equal expectations. -/
theorem bpz_integral_eq_of_tendstoInMeasure {Z W : ℕ → Ω → ℝ} {Z₀ W₀ : Ω → ℝ} {B : Ω → ℝ}
    (hZm : ∀ n, AEStronglyMeasurable (Z n) P) (hWm : ∀ n, AEStronglyMeasurable (W n) P)
    (hZ : TendstoInMeasure P Z atTop Z₀) (hW : TendstoInMeasure P W atTop W₀)
    (hB : Integrable B P) (hZb : ∀ n, ∀ᵐ ω ∂P, |Z n ω| ≤ B ω)
    (hWb : ∀ n, ∀ᵐ ω ∂P, |W n ω| ≤ B ω)
    (heq : ∀ᶠ n in atTop, ∫ ω, Z n ω ∂P = ∫ ω, W n ω ∂P) :
    ∫ ω, Z₀ ω ∂P = ∫ ω, W₀ ω ∂P :=
  tendsto_nhds_unique (bpz_tendsto_integral_of_tendstoInMeasure hZm hZ hB hZb)
    ((bpz_tendsto_integral_of_tendstoInMeasure hWm hW hB hWb).congr'
      (heq.mono fun _ hn => hn.symm))

end DOZZ.Proofs
