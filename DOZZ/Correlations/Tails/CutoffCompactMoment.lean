/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.WeightedCutoff.Bound

/-! Uniform compact-support cutoff moments used in the correlated pin-weight limit. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The weighted cutoff bound `DOZZ.equatorGFF_GMC_weighted_cutoff_bound`, with zero charge,
bounds every compact-support cutoff mass at every integer cutoff and every positive subcritical
order. -/
theorem regularized_compact_mass_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ q R : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q)
    (hqc : q < 4 / γ^2) (hR : 0 ≤ R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n : ℕ,
      (∫⁻ ω, (regularizedGMC P Xc γ n ω (Metric.closedBall 0 R)) ^ q ∂P) ≤ C := by
  have hQ : 0 < Q γ := by unfold Q; positivity
  have heq : 2 / γ * (Q γ - 0) = 4 / γ^2 + 1 := by
    unfold Q
    field_simp
    ring
  have hadm : ∀ t ∈ ({(0,q)} : Set (ℝ × ℝ)), t.1 < Q γ ∧ 0 < t.2 ∧
      t.2 < min (4 / γ^2) (2 / γ * (Q γ - t.1)) := by
    intro t ht
    obtain rfl := Set.mem_singleton_iff.mp ht
    exact ⟨hQ, hq, lt_min hqc (by rw [heq]; linarith)⟩
  obtain ⟨C, hC, hbound⟩ := equatorGFF_GMC_weighted_cutoff_bound P X hX γ hγ hγ2 Xc hc
    {(0,q)} isCompact_singleton hadm {0} isCompact_singleton (R+1) (by linarith)
  refine ⟨ENNReal.ofReal (C * (R+1) ^ (γ*Q γ*q - γ^2*q^2/2)),
    ENNReal.ofReal_lt_top, fun n => ?_⟩
  have hd : Real.exp (-(n : ℝ)) ≤ R+1 := by
    have he : Real.exp (-(n : ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
    linarith
  have ht : Real.log (1 / Real.exp (-(n : ℝ))) = (n : ℝ) := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  have hb := hbound (0,q) (Set.mem_singleton _) 0 (Set.mem_singleton _)
    (Real.exp (-(n : ℝ))) (R+1) (Real.exp_pos _) hd le_rfl
  have hmass (ω : Ω) : cutoffWeightedGmcBallMass P Xc γ 0 0 (R+1)
      (Real.exp (-(n : ℝ))) ω = regularizedGMC P Xc γ n ω (Metric.ball 0 (R+1)) := by
    simp only [cutoffWeightedGmcBallMass, ht, mul_zero, Real.rpow_zero,
      ENNReal.ofReal_one, lintegral_one, Measure.restrict_apply_univ]
  simp only [hmass, sub_zero] at hb
  refine (lintegral_mono (fun ω => ENNReal.rpow_le_rpow (measure_mono ?_) hq.le)).trans hb
  exact Metric.closedBall_subset_ball (by linarith)


end DOZZ.Proofs
