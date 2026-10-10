/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
public import DOZZ.Statements.ShiftEquations.PoleSubtractedObservable
public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
import DOZZ.ShiftEquations.PoleSubtracted.RealLimit

/-!
# The pole-subtracted observable extends holomorphically

This is [KRV, Lemma 10.3], with a conjugate-Hölder allocation of the mixed moments on the full
window. Around each point `x₀` of the interval `(-2η - δ, 1/γ)` the Cauchy estimate of the cutoff
family holds uniformly on a rectangle `|Re z - x₀| < ρ`, `|Im z| < h`, with `h² ≤ κ/2` so that the
Gaussian growth `e^{(n+1)(Im z)²/2}` is beaten by the decay `e^{-κn}`. The union `V` of these
rectangles is open and contains the interval; the cutoff family converges geometrically, hence
locally uniformly, on `V` to a holomorphic `F`, which at real points is the pole-subtracted
observable. On a compact subset of `V` finitely many rectangles give one exponential rate.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- **Cauchy bounds on a rectangle** around a point of the interval. -/
theorem exists_rectangle_cauchy_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    (x₀ : Ioo (-2 * η - δ) (1 / γ)) :
    ∃ ρ h K κ : ℝ, 0 < ρ ∧ 0 < h ∧ 0 ≤ K ∧ 0 < κ ∧ -2 * η - δ < (x₀ : ℝ) - ρ ∧
      (x₀ : ℝ) + ρ < 1 / γ ∧ ∀ z : ℂ, |z.re - x₀| < ρ → |z.im| < h → ∀ n : ℕ,
        ‖poleSubtractedCutoff P Xc M γ η (n + 1) z -
            poleSubtractedCutoff P Xc M γ η n z‖ ≤ K * Real.exp (-κ * n) := by
  obtain ⟨x, hx1, hx2⟩ := x₀
  set ρ : ℝ := min (x - (-2 * η - δ)) (1 / γ - x) / 2 with hρ
  have hρ0 : 0 < ρ := by
    rw [hρ]
    have : 0 < min (x - (-2 * η - δ)) (1 / γ - x) := lt_min (by linarith) (by linarith)
    linarith
  have hlo : -2 * η - δ < x - ρ := by
    have : ρ ≤ (x - (-2 * η - δ)) / 2 := by
      rw [hρ]
      exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hhi : x + ρ < 1 / γ := by
    have : ρ ≤ (1 / γ - x) / 2 := by
      rw [hρ]
      exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  obtain ⟨C, κ, hC, hκ, hb⟩ :=
    exists_cutoff_cauchy_bound P X hX γ hγ hγ2 M hM Xc hXc hW hlo hhi
  set h : ℝ := min 1 (κ / 2) with hh
  set W : ℝ := 1 + (|x| + ρ + 1) / γ with hWdef
  refine ⟨ρ, h, W * C * Real.exp (κ / 4), 3 * κ / 4, hρ0, lt_min one_pos (by linarith),
    by positivity, by linarith, hlo, hhi, fun z hzre hzim n => ?_⟩
  have hz : z.re ∈ Icc (x - ρ) (x + ρ) := by
    rw [abs_lt] at hzre
    constructor <;> linarith
  refine (hb z hz n).trans ?_
  have him1 : |z.im| ≤ 1 := hzim.le.trans (min_le_left _ _)
  have him2 : |z.im| ≤ κ / 2 := hzim.le.trans (min_le_right _ _)
  have himsq : z.im ^ 2 ≤ κ / 2 := by
    rw [← sq_abs]
    calc |z.im| ^ 2 = |z.im| * |z.im| := sq _
      _ ≤ 1 * (κ / 2) := mul_le_mul him1 him2 (abs_nonneg _) zero_le_one
      _ = κ / 2 := one_mul _
  have hexp : Real.exp (((n + 1 : ℕ) : ℝ) * z.im ^ 2 / 2) ≤
      Real.exp (κ / 4) * Real.exp (κ / 4 * n) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have hn : (0 : ℝ) ≤ (n + 1 : ℕ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left himsq hn
    push_cast at this ⊢
    nlinarith
  have hnorm : ‖1 - z / γ‖ ≤ W := by
    have hzn : ‖z‖ ≤ |x| + ρ + 1 := by
      have hre : |z.re| ≤ |x| + ρ := by
        have := abs_sub_abs_le_abs_sub z.re x
        rw [abs_lt] at hzre
        rw [abs_le]
        constructor <;> cases abs_cases x <;> cases abs_cases z.re <;> linarith
      linarith [Complex.norm_le_abs_re_add_abs_im z]
    calc ‖1 - z / γ‖ ≤ ‖(1 : ℂ)‖ + ‖z / γ‖ := norm_sub_le _ _
      _ = 1 + ‖z‖ / γ := by
          rw [norm_one, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
      _ ≤ W := by
          rw [hWdef]
          gcongr
  calc Real.exp (((n + 1 : ℕ) : ℝ) * z.im ^ 2 / 2) * ‖1 - z / γ‖ * (C * Real.exp (-κ * n))
      ≤ (Real.exp (κ / 4) * Real.exp (κ / 4 * n)) * W * (C * Real.exp (-κ * n)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hexp hnorm (norm_nonneg _) (by positivity)
    _ = W * C * Real.exp (κ / 4) * Real.exp (-(3 * κ / 4) * n) := by
        rw [show Real.exp (-(3 * κ / 4) * n) = Real.exp (κ / 4 * n) * Real.exp (-κ * n) by
          rw [← Real.exp_add]
          ring_nf]
        ring

/-- After subtracting the two local masses, the real observable of [KRV, Lemma 10.3] extends
holomorphically to a neighborhood of the entire interval of that lemma. The last conjunct records
the compact-uniform Cauchy decay of the limit-chaos analytic approximants; the corrected Markov
threshold (erratum K4, see docs/ERRATA-AND-DEVIATIONS.md) is part of this assertion. -/
theorem poleSubtractedObservable_holomorphic
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ η δ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hM : IsGMCOf P X γ M) (hWindow : TwoPoleWindow γ η δ) :
    ∃ V : Set ℂ, IsOpen V ∧
      (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V) ∧
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F V ∧
        (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ →
          F (x : ℂ) =
            (poleSubtractedObservable P M γ η x : ℂ)) ∧
        (∀ n : ℕ, DifferentiableOn ℂ
          (poleSubtractedCutoff P Xc M γ η n) V) ∧
        TendstoLocallyUniformlyOn (poleSubtractedCutoff P Xc M γ η) F atTop V ∧
          ∀ K : Set ℂ, IsCompact K → K ⊆ V →
            ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
              ∀ n : ℕ, ∀ z ∈ K,
                ‖poleSubtractedCutoff P Xc M γ η (n + 1) z -
                    poleSubtractedCutoff P Xc M γ η n z‖ ≤
                  C * Real.exp (-κ * n) := by
  set F : ℕ → ℂ → ℂ := poleSubtractedCutoff P Xc M γ η with hFdef
  have hrect := fun x₀ : Ioo (-2 * η - δ) (1 / γ) =>
    exists_rectangle_cauchy_bound P X hX γ hγ hγ2 M hM Xc hXc hWindow x₀
  choose ρ hgt Kb κ hρ hhgt hKb hκ hlo _ hbound using hrect
  set R : Ioo (-2 * η - δ) (1 / γ) → Set ℂ :=
    fun x₀ => {z : ℂ | |z.re - x₀| < ρ x₀ ∧ |z.im| < hgt x₀} with hRdef
  have hRopen : ∀ x₀, IsOpen (R x₀) := fun x₀ =>
    (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const))
      continuous_const).inter (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        continuous_const)
  set V : Set ℂ := ⋃ x₀, R x₀ with hVdef
  have hVopen : IsOpen V := isOpen_iUnion hRopen
  have hVH : V ⊆ cutoffHalfPlane η δ := by
    intro z hz
    obtain ⟨x₀, hz⟩ := mem_iUnion.1 hz
    have h1 := hz.1
    rw [abs_lt] at h1
    change -2 * η - δ < z.re
    linarith [hlo x₀]
  have hmemR : ∀ x : ℝ, ∀ hx : -2 * η - δ < x ∧ x < 1 / γ, (x : ℂ) ∈ R ⟨x, hx⟩ :=
    fun x hx => by
      simp only [hRdef, mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im, sub_self,
        abs_zero]
      exact ⟨hρ _, hhgt _⟩
  have hr1 : ∀ x₀, Real.exp (-κ x₀) < 1 := fun x₀ =>
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (hκ x₀))
  have hgeom : ∀ x₀, ∀ z ∈ R x₀, ∀ n : ℕ,
      dist (F n z) (F (n + 1) z) ≤ Kb x₀ * Real.exp (-κ x₀) ^ n := by
    intro x₀ z hz n
    rw [dist_comm, dist_eq_norm, ← Real.exp_nat_mul, mul_comm (n : ℝ)]
    exact hbound x₀ z hz.1 hz.2 n
  have hconv : ∀ z ∈ V, ∃ L, Tendsto (fun n => F n z) atTop (𝓝 L) := by
    intro z hz
    obtain ⟨x₀, hz⟩ := mem_iUnion.1 hz
    exact cauchySeq_tendsto_of_complete
      (cauchySeq_of_le_geometric _ _ (hr1 x₀) (hgeom x₀ z hz))
  set Flim : ℂ → ℂ := fun z => limUnder atTop (fun n => F n z) with hFlim
  have hlim : ∀ z ∈ V, Tendsto (fun n => F n z) atTop (𝓝 (Flim z)) := fun z hz =>
    tendsto_nhds_limUnder (hconv z hz)
  have hdist : ∀ x₀, ∀ z ∈ R x₀, ∀ n : ℕ, dist (F n z) (Flim z) ≤
      Kb x₀ * Real.exp (-κ x₀) ^ n / (1 - Real.exp (-κ x₀)) := fun x₀ z hz n =>
    dist_le_of_le_geometric_of_tendsto _ _ (hr1 x₀) (hgeom x₀ z hz)
      (hlim z (mem_iUnion.2 ⟨x₀, hz⟩)) n
  have hFdiff : ∀ n, DifferentiableOn ℂ (F n) V := fun n => by
    have h1 := (differentiableOn_cutoffFamily P X hX γ hγ hγ2 M hM Xc hXc hWindow
      (le_refl n)).1
    rw [← poleSubtractedCutoff_eq_cutoffFamily] at h1
    exact h1.mono hVH
  have hTLU : TendstoLocallyUniformlyOn F Flim atTop V := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε z hz
    obtain ⟨x₀, hzR⟩ := mem_iUnion.1 hz
    refine ⟨R x₀, mem_nhdsWithin_of_mem_nhds ((hRopen x₀).mem_nhds hzR), ?_⟩
    have htend : Tendsto (fun n : ℕ => Kb x₀ * Real.exp (-κ x₀) ^ n /
        (1 - Real.exp (-κ x₀))) atTop (𝓝 0) := by
      have h1 := ((tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
        (hr1 x₀)).const_mul (Kb x₀)).div_const (1 - Real.exp (-κ x₀))
      simpa using h1
    filter_upwards [htend.eventually (gt_mem_nhds hε)] with n hn y hy
    rw [dist_comm]
    exact (hdist x₀ y hy n).trans_lt hn
  refine ⟨V, hVopen, fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, hmemR x hx⟩, Flim,
    hTLU.differentiableOn (Eventually.of_forall hFdiff) hVopen, ?_, hFdiff, hTLU, ?_⟩
  · intro x hx
    exact cutoff_real_limit_eq_observable P X hX γ hγ hγ2 M hM Xc hXc hWindow hx.1 hx.2
      (hlim x (mem_iUnion.2 ⟨⟨x, hx⟩, hmemR x hx⟩))
  · intro Kc hKc hKV
    obtain ⟨t, ht⟩ := hKc.elim_finite_subcover R hRopen hKV
    have hsum : 0 ≤ ∑ i ∈ t, 1 / κ i :=
      Finset.sum_nonneg fun i _ => (one_div_pos.2 (hκ i)).le
    refine ⟨∑ i ∈ t, Kb i, 1 / (1 + ∑ i ∈ t, 1 / κ i),
      Finset.sum_nonneg fun i _ => hKb i, one_div_pos.2 (by linarith), fun n z hz => ?_⟩
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 (ht hz)
    have hκmin : 1 / (1 + ∑ j ∈ t, 1 / κ j) ≤ κ i := by
      have h1 : 1 / κ i ≤ ∑ j ∈ t, 1 / κ j :=
        Finset.single_le_sum (fun j _ => (one_div_pos.2 (hκ j)).le) hi
      rw [div_le_iff₀ (by linarith)]
      have h2 : κ i * (1 / κ i) = 1 := mul_one_div_cancel (hκ i).ne'
      nlinarith [hκ i]
    calc ‖F (n + 1) z - F n z‖ ≤ Kb i * Real.exp (-κ i * n) := hbound i z hzi.1 hzi.2 n
      _ ≤ (∑ j ∈ t, Kb j) * Real.exp (-(1 / (1 + ∑ j ∈ t, 1 / κ j)) * n) := by
        apply mul_le_mul (Finset.single_le_sum (fun j _ => hKb j) hi) _ (Real.exp_pos _).le
          (Finset.sum_nonneg fun j _ => hKb j)
        apply Real.exp_le_exp.2
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith

end DOZZ.Proofs

end
