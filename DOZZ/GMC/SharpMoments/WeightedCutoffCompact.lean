/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.WeightedCutoff.UniformGamma

/-! # Weighted cutoff bounds over compact coupled parameter sets

The γ-uniform weighted cutoff bound is stated over product sets `Γ × T` of couplings and
(charge, order) pairs on which every combination is admissible. Admissibility is an open
condition, so every point of a compact admissible set of triples `(γ, α, t)` has a closed product
box around it that is still admissible; a finite subcover gives one constant for the whole set. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The admissibility slack of a triple `(γ, α, t)`. -/
noncomputable def weightedCutoffSlack (q : ℝ × ℝ × ℝ) : ℝ :=
  min (min q.1 (2 - q.1)) (min (min (Q q.1 - q.2.1) q.2.2)
    (min (4 / q.1 ^ 2 - q.2.2) (2 / q.1 * (Q q.1 - q.2.1) - q.2.2)))

theorem weightedCutoffSlack_pos_iff (q : ℝ × ℝ × ℝ) :
    0 < weightedCutoffSlack q ↔ 0 < q.1 ∧ q.1 < 2 ∧ q.2.1 < Q q.1 ∧ 0 < q.2.2 ∧
      q.2.2 < min (4 / q.1 ^ 2) (2 / q.1 * (Q q.1 - q.2.1)) := by
  simp only [weightedCutoffSlack, lt_min_iff, sub_pos]
  tauto

theorem continuousAt_weightedCutoffSlack {p : ℝ × ℝ × ℝ} (hp : p.1 ≠ 0) :
    ContinuousAt weightedCutoffSlack p := by
  unfold weightedCutoffSlack Q
  fun_prop (disch := simp [hp])

/-- Around each admissible triple there is a closed product box of admissible triples. -/
theorem exists_admissible_box {p : ℝ × ℝ × ℝ} (hp : 0 < weightedCutoffSlack p) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : ℝ × ℝ × ℝ, dist q p < 2 * ε → 0 < weightedCutoffSlack q := by
  have hp1 : p.1 ≠ 0 := ((weightedCutoffSlack_pos_iff p).mp hp).1.ne'
  have hev : ∀ᶠ q in 𝓝 p, 0 < weightedCutoffSlack q :=
    (continuousAt_weightedCutoffSlack hp1).eventually (lt_mem_nhds hp)
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ε' / 2, half_pos hε', fun q hq => hball (by linarith)⟩

/-- The γ-uniform weighted cutoff bound over a compact set of admissible triples
`(γ, α, t)`. -/
theorem weightedCutoff_bound_uniform_compact
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Sc : Set (ℝ × ℝ × ℝ)) (hSc : IsCompact Sc)
    (hadm : ∀ p ∈ Sc, 0 < weightedCutoffSlack p)
    (K : Set ℂ) (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ p ∈ Sc, ∀ z ∈ K, ∀ δ R : ℝ, 0 < δ → δ ≤ R → R ≤ r₀ →
      (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc p.1 p.2.1 z R δ ω) p.2.2 ∂P) ≤
        ENNReal.ofReal (C * Real.rpow R
          (p.1 * (Q p.1 - p.2.1) * p.2.2 - p.1 ^ 2 * p.2.2 ^ 2 / 2)) := by
  classical
  -- boxes and their constants
  have hbox : ∀ p : Sc, ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ × ℝ × ℝ, dist q p.1 ≤ ε → ∀ z ∈ K, ∀ δ R : ℝ, 0 < δ → δ ≤ R → R ≤ r₀ →
        (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc q.1 q.2.1 z R δ ω) q.2.2 ∂P) ≤
          ENNReal.ofReal (C * Real.rpow R
            (q.1 * (Q q.1 - q.2.1) * q.2.2 - q.1 ^ 2 * q.2.2 ^ 2 / 2)) := by
    rintro ⟨p, hpS⟩
    obtain ⟨ε, hε, hε'⟩ := exists_admissible_box (hadm p hpS)
    have hin : ∀ γ ∈ closedBall p.1 ε, ∀ t ∈ closedBall p.2 ε,
        0 < weightedCutoffSlack (γ, t) := by
      intro γ hγ t ht
      refine hε' _ ?_
      rw [Prod.dist_eq]
      exact lt_of_le_of_lt (max_le (mem_closedBall.mp hγ) (mem_closedBall.mp ht)) (by linarith)
    obtain ⟨C, hC, hCb⟩ := equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma P X hX
      (closedBall p.1 ε) (isCompact_closedBall _ _)
      (fun γ hγ => by
        have h := (weightedCutoffSlack_pos_iff (γ, p.2)).mp (hin γ hγ p.2 (mem_closedBall_self
          hε.le))
        exact ⟨h.1, h.2.1⟩)
      Xc hXc (closedBall p.2 ε) (isCompact_closedBall _ _)
      (fun γ hγ t ht => by
        have h := (weightedCutoffSlack_pos_iff (γ, t)).mp (hin γ hγ t ht)
        exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)
      K hK r₀ hr₀
    refine ⟨ε, hε, C, hC, fun q hq z hz δ R hδ hδR hRr => ?_⟩
    have hq' : dist q p ≤ ε := hq
    rw [Prod.dist_eq] at hq'
    exact hCb q.1 (mem_closedBall.mpr ((le_max_left _ _).trans hq')) q.2
      (mem_closedBall.mpr ((le_max_right _ _).trans hq')) z hz δ R hδ hδR hRr
  choose ε hε C hC hCb using hbox
  -- a finite subcover of the compact set
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun p : Sc => ball p.1 (ε p))
    (fun _ => isOpen_ball) (fun q hq => Set.mem_iUnion.mpr ⟨⟨q, hq⟩, mem_ball_self (hε _)⟩)
  have hsum0 : 0 ≤ ∑ p ∈ t, C p := Finset.sum_nonneg fun p _ => (hC p).le
  refine ⟨1 + ∑ p ∈ t, C p, by linarith, fun q hq z hz δ R hδ hδR hRr => ?_⟩
  obtain ⟨p, hpt, hqp⟩ := Set.mem_iUnion₂.mp (ht hq)
  refine (hCb p q (mem_ball.mp hqp).le z hz δ R hδ hδR hRr).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg
      (hδ.le.trans hδR) _)))
  calc C p ≤ ∑ p ∈ t, C p := Finset.single_le_sum (fun p _ => (hC p).le) hpt
    _ ≤ 1 + ∑ p ∈ t, C p := le_add_of_nonneg_left zero_le_one

end DOZZ.Proofs
