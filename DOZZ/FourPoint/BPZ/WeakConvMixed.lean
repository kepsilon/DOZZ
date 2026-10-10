/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WeakConvDouble

/-! # Random test functions under weak convergence in probability

If `μ n → μ₀` weakly in probability, then `∫ g_n(ω, x) dμ_n(x) → ∫ g₀(ω, x) dμ₀(x)` in probability
for random test functions supported in a fixed ball, equicontinuous in `x` with a modulus scaled
by a finite random variable `V`, and converging uniformly in the same scale. This handles
integrands that depend on the sample through another random measure, such as
`x ↦ ∫ A(x, y) dν(y)`. The proof compares with grid sums `∑ μ(Q_i) g₀(c_i)`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Pathwise error of the grid approximation of a single integral. -/
theorem bpz_single_grid_error (m : Measure ℂ) [IsFiniteMeasure m] (G G₀ : ℂ → ℝ)
    (hGm : Measurable G) {R δ h ε₁ V : ℝ} (hR : 0 ≤ R) (hh : 0 < h) (hh1 : h ≤ 1 / 4)
    (hhδ : 2 * h ≤ δ) (hε₁ : 0 ≤ ε₁) (hV : 0 ≤ V) (hGb : ∀ x, |G x| ≤ V)
    (hG₀b : ∀ x, |G₀ x| ≤ V)
    (hGs : ∀ x, R < ‖x‖ → G x = 0) (hGG : ∀ x, |G x - G₀ x| ≤ ε₁ * V)
    (hcδ : ∀ x x', ‖x - x'‖ ≤ δ → |G₀ x - G₀ x'| ≤ ε₁ * V) :
    |∫ x, G x ∂m - ∑ i ∈ bpzGridBox ⌈R / h⌉₊,
        m.real (bpzGridIdx h ⁻¹' {i}) * G₀ (bpzGridCorner h i)| ≤
      2 * ε₁ * V * m.real (Metric.closedBall 0 (2 * R + 1)) := by
  set S := bpzGridBox ⌈R / h⌉₊ with hS
  rw [← integral_bpzGrid_step h S (fun i => G₀ (bpzGridCorner h i))]
  set st : ℂ → ℝ := fun x =>
    if bpzGridIdx h x ∈ S then G₀ (bpzGridCorner h (bpzGridIdx h x)) else 0 with hst
  have hstm : Measurable st := measurable_bpzGrid_step h S (fun i => G₀ (bpzGridCorner h i))
  have hstb : ∀ x, |st x| ≤ V := by
    intro x
    simp only [hst]
    split_ifs
    · exact hG₀b _
    · simpa using hV
  set B₂ : Set ℂ := Metric.closedBall 0 (2 * R + 1)
  have hpt : ∀ x, |G x - st x| ≤ 2 * ε₁ * V * B₂.indicator 1 x := by
    intro x
    by_cases hxS : bpzGridIdx h x ∈ S
    · have hx2 : ‖x‖ ≤ 2 * R + 1 :=
        (norm_le_of_bpzGridIdx_mem_box hh hxS).trans (bpzGrid_box_radius hR hh hh1)
      have hi : B₂.indicator (1 : ℂ → ℝ) x = 1 := Set.indicator_of_mem (by simpa [B₂] using hx2) _
      have hst' : st x = G₀ (bpzGridCorner h (bpzGridIdx h x)) := by
        simp only [hst]; exact ite_eq_left hxS
      have hxc : ‖x - bpzGridCorner h (bpzGridIdx h x)‖ ≤ δ :=
        (norm_sub_bpzGridCorner_le hh x).trans hhδ
      rw [hi, hst', mul_one]
      calc |G x - G₀ (bpzGridCorner h (bpzGridIdx h x))|
          ≤ |G x - G₀ x| + |G₀ x - G₀ (bpzGridCorner h (bpzGridIdx h x))| := abs_sub_le _ _ _
        _ ≤ ε₁ * V + ε₁ * V := add_le_add (hGG x) (hcδ x _ hxc)
        _ = 2 * ε₁ * V := by ring
    · have hx : R < ‖x‖ := by
        by_contra hcon
        push Not at hcon
        exact hxS (bpzGridIdx_mem_box hh hcon)
      have hst' : st x = 0 := by simp only [hst]; exact ite_eq_right hxS
      rw [hGs x hx, hst', sub_zero, abs_zero]
      exact mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)
  have hIG : Integrable G m := integrable_of_bdd_finite hGm hGb
  have hIst : Integrable st m := integrable_of_bdd_finite hstm hstb
  rw [← integral_sub hIG hIst, ← Real.norm_eq_abs]
  calc ‖∫ x, (G x - st x) ∂m‖ ≤ ∫ x, 2 * ε₁ * V * B₂.indicator 1 x ∂m := by
        refine norm_integral_le_of_norm_le
          ((((integrable_const (1 : ℝ)).indicator measurableSet_closedBall).const_mul
            (2 * ε₁ * V))) (Eventually.of_forall fun x => ?_)
        rw [Real.norm_eq_abs]
        exact hpt x
    _ = 2 * ε₁ * V * m.real B₂ := by
        rw [integral_const_mul, integral_indicator_one measurableSet_closedBall]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : ℕ → Ω → Measure ℂ}
  {μ₀ : Ω → Measure ℂ}

namespace BPZWeakConv

/-- Integrals of jointly measurable random integrands against a measurable family of finite
measures are measurable. -/
theorem measurable_integral_random {m : Ω → Measure ℂ} (hm : Measurable m)
    (hmfin : ∀ ω, IsFiniteMeasure (m ω)) {g : Ω → ℂ → ℝ}
    (hg : Measurable (fun p : Ω × ℂ => g p.1 p.2)) :
    Measurable (fun ω => ∫ x, g ω x ∂m ω) :=
  (measurable_integral_finite_family m hm hmfin g hg).comp (measurable_id.prodMk measurable_id)

/-- **Random test functions under weak convergence in probability.** -/
theorem tendstoInMeasure_random_test [IsProbabilityMeasure P] (hμ : BPZWeakConv P μ μ₀)
    (g : ℕ → Ω → ℂ → ℝ) (g₀ : Ω → ℂ → ℝ)
    (hgm : ∀ n, Measurable (fun p : Ω × ℂ => g n p.1 p.2))
    (hg₀m : Measurable (fun p : Ω × ℂ => g₀ p.1 p.2))
    {R : ℝ} (hR : 0 ≤ R) {V : Ω → ℝ} (hVm : Measurable V) (hV0 : ∀ ω, 0 ≤ V ω)
    (hgb : ∀ n, ∀ᵐ ω ∂P, ∀ x, |g n ω x| ≤ V ω) (hg₀b : ∀ᵐ ω ∂P, ∀ x, |g₀ ω x| ≤ V ω)
    (hsupp : ∀ n ω x, R < ‖x‖ → g n ω x = 0) (hsupp₀ : ∀ ω x, R < ‖x‖ → g₀ ω x = 0)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ ω ∂P, ∀ x x', ‖x - x'‖ ≤ δ →
      |g₀ ω x - g₀ ω x'| ≤ ε * V ω)
    (hunif : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ᵐ ω ∂P, ∀ x, |g n ω x - g₀ ω x| ≤ ε * V ω) :
    TendstoInMeasure P (fun n ω => ∫ x, g n ω x ∂μ n ω) atTop
      (fun ω => ∫ x, g₀ ω x ∂μ₀ ω) := by
  set B₂ : Set ℂ := Metric.closedBall 0 (2 * R + 1) with hB₂
  have hB₂m : MeasurableSet B₂ := measurableSet_closedBall
  have hmassm : ∀ (s : Set ℂ), MeasurableSet s → ∀ n, Measurable fun ω => (μ n ω).real s :=
    fun s hs n => ((Measure.measurable_coe hs).comp (hμ.meas n)).ennreal_toReal
  have hmassm₀ : ∀ (s : Set ℂ), MeasurableSet s → Measurable fun ω => (μ₀ ω).real s :=
    fun s hs => ((Measure.measurable_coe hs).comp hμ.meas₀).ennreal_toReal
  have hg₀pt : ∀ x, Measurable fun ω => g₀ ω x := fun x =>
    hg₀m.comp (measurable_id.prodMk measurable_const)
  refine bpz_tendstoInMeasure_of_approx fun ε hε => ?_
  have hWm : Measurable (fun ω => V ω * (μ₀ ω).real B₂) := hVm.mul (hmassm₀ B₂ hB₂m)
  obtain ⟨k, hk⟩ := bpz_exists_scale_small (P := P) hWm
    (s := ε / 4) (by positivity) (t := ENNReal.ofReal (ε / 2))
    (ENNReal.ofReal_pos.2 (by positivity))
  set ε₁ : ℝ := 1 / ((k : ℝ) + 1) with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨δ, hδ, hcδ⟩ := hcont ε₁ hε₁0
  set h : ℝ := min (1 / 4) (δ / 2) with hhdef
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 / 4 := min_le_left _ _
  have hhδ : 2 * h ≤ δ := by have := min_le_right (1 / 4 : ℝ) (δ / 2); linarith
  set S := bpzGridBox ⌈R / h⌉₊ with hS
  set c := bpzGridCorner h with hc
  set cell : ℤ × ℤ → Set ℂ := fun i => bpzGridIdx h ⁻¹' {i} with hcell
  have hcellm : ∀ i, MeasurableSet (cell i) := measurableSet_bpzGridCell h
  set A : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ S, (μ n ω).real (cell i) * g₀ ω (c i) with hA
  set A₀ : Ω → ℝ := fun ω => ∑ i ∈ S, (μ₀ ω).real (cell i) * g₀ ω (c i) with hA₀
  have hAconv : TendstoInMeasure P A atTop A₀ := by
    refine bpz_tendstoInMeasure_finset_sum S
      (fun i n => ((hmassm _ (hcellm i) n).mul (hg₀pt (c i))).aestronglyMeasurable)
      fun i _ => ?_
    have hmass : TendstoInMeasure P (fun n ω => (μ n ω).real (cell i)) atTop
        (fun ω => (μ₀ ω).real (cell i)) := by
      have h := hμ.conv ((cell i).indicator 1) (measurable_one.indicator (hcellm i)) 1
        (‖c i‖ + 2 * h) (fun x => bpz_indicator_one_abs_le _ x)
        (fun x hx => bpz_indicator_one_eq_zero_of_subset (bpzGrid_cell_subset h hh0 i) x hx)
      simp only [integral_indicator_one (hcellm i)] at h
      exact h
    exact bpz_tendstoInMeasure_mul (fun n => (hmassm _ (hcellm i) n).aestronglyMeasurable)
      (fun _ => (hg₀pt (c i)).aestronglyMeasurable) hmass
      (tendstoInMeasure_of_tendsto_ae (fun _ => (hg₀pt (c i)).aestronglyMeasurable)
        (Eventually.of_forall fun _ => tendsto_const_nhds))
  set Bn : ℕ → Ω → ℝ := fun n ω => 2 * ε₁ * V ω * (μ n ω).real B₂ with hBn
  set B₀ : Ω → ℝ := fun ω => 2 * ε₁ * V ω * (μ₀ ω).real B₂ with hB₀
  have hBconv : TendstoInMeasure P Bn atTop B₀ := by
    have hmass : TendstoInMeasure P (fun n ω => (μ n ω).real B₂) atTop
        (fun ω => (μ₀ ω).real B₂) := by
      have h := hμ.conv (B₂.indicator 1) (measurable_one.indicator hB₂m) 1 (2 * R + 1)
        (fun x => bpz_indicator_one_abs_le _ x)
        (fun x hx => bpz_indicator_one_eq_zero_of_subset subset_rfl x hx)
      simp only [integral_indicator_one hB₂m] at h
      exact h
    have hV2 : TendstoInMeasure P (fun (_ : ℕ) ω => 2 * ε₁ * V ω) atTop
        (fun ω => 2 * ε₁ * V ω) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => (hVm.const_mul _).aestronglyMeasurable)
        (Eventually.of_forall fun _ => tendsto_const_nhds)
    exact bpz_tendstoInMeasure_mul (fun _ => (hVm.const_mul _).aestronglyMeasurable)
      (fun n => (hmassm _ hB₂m n).aestronglyMeasurable) hV2 hmass
  have hP₀ : P {ω | ε / 2 ≤ B₀ ω} ≤ ENNReal.ofReal (ε / 2) := by
    refine le_trans (measure_mono fun ω hω => ?_) hk
    simp only [Set.mem_ofPred_eq, hB₀] at hω ⊢
    have hpos : 0 ≤ ε₁ * (V ω * (μ₀ ω).real B₂) :=
      mul_nonneg hε₁0.le (mul_nonneg (hV0 ω) measureReal_nonneg)
    rw [abs_of_nonneg hpos]
    linarith
  refine ⟨A, A₀, hAconv, ?_, ?_⟩
  · obtain ⟨n₀, hn₀⟩ := (hunif ε₁ hε₁0).exists_forall_of_atTop
    set E : ℕ → Ω → ℝ := fun n ω => if n₀ ≤ n then (∫ x, g n ω x ∂μ n ω) - A n ω else 0
      with hE
    have hEB : ∀ n, ∀ᵐ ω ∂P, |E n ω| ≤ Bn n ω := by
      intro n
      have hBn0 : ∀ ω, 0 ≤ Bn n ω := fun ω => by
        simp only [hBn]
        exact mul_nonneg (mul_nonneg (by positivity) (hV0 ω)) measureReal_nonneg
      by_cases hn : n₀ ≤ n
      · filter_upwards [hgb n, hg₀b, hcδ, hn₀ n hn] with ω h1 h2 h3 h4
        have := hμ.fin n ω
        simp only [hE, ite_eq_left hn]
        exact bpz_single_grid_error (μ n ω) (g n ω) (g₀ ω)
          ((hgm n).comp (measurable_const.prodMk measurable_id)) hR hh0 hh1 hhδ hε₁0.le
          (hV0 ω) h1 h2 (hsupp n ω) h4 h3
      · refine Eventually.of_forall fun ω => ?_
        simp only [hE, ite_eq_right hn, abs_zero]
        exact hBn0 ω
    have hfin := bpz_eventually_measure_le_of_le_tendstoInMeasure hBconv hEB hε
      (lt_of_le_of_lt hP₀ ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)))
    filter_upwards [hfin, eventually_ge_atTop n₀] with n hn hn'
    simp only [hE, ite_eq_left hn'] at hn
    exact hn
  · have hle : ∀ᵐ ω ∂P, |(∫ x, g₀ ω x ∂μ₀ ω) - A₀ ω| ≤ B₀ ω := by
      filter_upwards [hg₀b, hcδ] with ω h2 h3
      have := hμ.fin₀ ω
      have := bpz_single_grid_error (μ₀ ω) (g₀ ω) (g₀ ω)
        (hg₀m.comp (measurable_const.prodMk measurable_id)) hR hh0 hh1 hhδ hε₁0.le (hV0 ω)
        h2 h2 (hsupp₀ ω)
        (fun x => by rw [sub_self, abs_zero]; exact mul_nonneg hε₁0.le (hV0 ω)) h3
      simpa [hB₀] using this
    calc P {ω | ε ≤ |(∫ x, g₀ ω x ∂μ₀ ω) - A₀ ω|}
        ≤ P {ω | ε / 2 ≤ B₀ ω} := measure_mono_ae (hle.mono fun ω hω hεω => by
          simp only [Set.mem_ofPred_eq] at hεω ⊢
          linarith)
      _ ≤ ENNReal.ofReal (ε / 2) := hP₀
      _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by linarith)

end BPZWeakConv

end DOZZ.Proofs
