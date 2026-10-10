/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesTerms

/-! Uniform tail estimates for the parameter-dependent ordinary Gauss series. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Once the denominator index dominates all three parameter norms, successive ordinary-series
terms contract at a rate controlled by the elementary hypergeometric coefficient ratio. -/
theorem gaussParameterSeriesTerm_norm_succ_le
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) (R q : ℝ)
    (hR : 0 ≤ R) (hRn : R < n)
    (hA : ‖p.1‖ ≤ R) (hB : ‖p.2.1‖ ≤ R) (hC : ‖p.2.2‖ ≤ R)
    (hRatio : ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ q)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    ‖gaussParameterSeriesTerm p z (n + 1)‖ ≤
      q * ‖gaussParameterSeriesTerm p z n‖ := by
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt hR hRn
  have hnc : (n : ℂ) + p.2.2 ≠ 0 := by
    intro h
    have hcEq : p.2.2 = -((n : ℂ)) :=
      eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using h)
    have hnorm : (n : ℝ) = ‖p.2.2‖ := by
      rw [hcEq, norm_neg, Complex.norm_natCast]
    linarith
  have hn1 : (n + 1 : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hden : (n + 1 : ℂ) * ((n : ℂ) + p.2.2) ≠ 0 :=
    mul_ne_zero hn1 hnc
  have hsolve : gaussParameterSeriesTerm p z (n + 1) =
      (((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z /
        ((n + 1 : ℂ) * ((n : ℂ) + p.2.2))) *
        gaussParameterSeriesTerm p z n := by
    field_simp [hden]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      gaussParameterSeriesTerm_recurrence p z n hc
  have hAnorm : ‖(n : ℂ) + p.1‖ ≤ (n : ℝ) + R := by
    calc
      ‖(n : ℂ) + p.1‖ ≤ ‖(n : ℂ)‖ + ‖p.1‖ := norm_add_le _ _
      _ ≤ (n : ℝ) + R := by rw [Complex.norm_natCast]; exact add_le_add (by norm_num) hA
  have hBnorm : ‖(n : ℂ) + p.2.1‖ ≤ (n : ℝ) + R := by
    calc
      ‖(n : ℂ) + p.2.1‖ ≤ ‖(n : ℂ)‖ + ‖p.2.1‖ := norm_add_le _ _
      _ ≤ (n : ℝ) + R := by rw [Complex.norm_natCast]; exact add_le_add (by norm_num) hB
  have hCnorm : (n : ℝ) - R ≤ ‖(n : ℂ) + p.2.2‖ := by
    have htriangle := norm_sub_norm_le (n : ℂ) ((n : ℂ) + p.2.2)
    have hnormN : ‖(n : ℂ)‖ = (n : ℝ) := by rw [Complex.norm_natCast]
    rw [show (n : ℂ) - ((n : ℂ) + p.2.2) = -p.2.2 by abel,
      norm_neg, hnormN] at htriangle
    linarith
  have hdenpos : 0 < ((n : ℝ) + 1) * ((n : ℝ) - R) := by
    exact mul_pos (by linarith) (by linarith)
  have hnorm :
      ‖gaussParameterSeriesTerm p z (n + 1)‖ =
        (‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ /
          (((n : ℝ) + 1) * ‖(n : ℂ) + p.2.2‖)) *
          ‖gaussParameterSeriesTerm p z n‖ := by
    rw [hsolve]
    simp only [norm_mul, norm_div]
    rw [show ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 by norm_cast]
  have hdennorm : ((n : ℝ) + 1) * ((n : ℝ) - R) ≤
      ((n : ℝ) + 1) * ‖(n : ℂ) + p.2.2‖ :=
    mul_le_mul_of_nonneg_left hCnorm (by positivity)
  have hnum : ‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ ≤
      ‖z‖ * ((n : ℝ) + R) ^ 2 := by
    calc
      ‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ ≤
          ((n : ℝ) + R) * ((n : ℝ) + R) * ‖z‖ := by gcongr
      _ = ‖z‖ * ((n : ℝ) + R) ^ 2 := by ring
  have hratio :
      (‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ /
          (((n : ℝ) + 1) * ‖(n : ℂ) + p.2.2‖)) ≤
        ‖z‖ * ((n : ℝ) + R) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) - R)) := by
    apply div_le_div₀
      (mul_nonneg (norm_nonneg z) (sq_nonneg ((n : ℝ) + R))) hnum hdenpos hdennorm
  calc
    ‖gaussParameterSeriesTerm p z (n + 1)‖ =
        (‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ /
          (((n : ℝ) + 1) * ‖(n : ℂ) + p.2.2‖)) *
          ‖gaussParameterSeriesTerm p z n‖ := hnorm
    _ ≤ (‖z‖ * ((n : ℝ) + R) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) - R))) *
          ‖gaussParameterSeriesTerm p z n‖ := by
      exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
    _ ≤ q * ‖gaussParameterSeriesTerm p z n‖ :=
      mul_le_mul_of_nonneg_right hRatio (norm_nonneg _)

/-- A uniform tail threshold for the elementary term-ratio bound on a disk strictly inside the
unit circle. -/
theorem exists_nat_uniform_gaussParameterSeries_ratio_bound
    (z : ℂ) (hz : ‖z‖ < 1) (R : ℝ) (hR : 0 ≤ R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → R < (n : ℝ) ∧
      ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ (1 + ‖z‖) / 2 := by
  let q : ℝ := (1 + ‖z‖) / 2
  let g : ℝ → ℝ := fun t => ‖z‖ * (1 + t) ^ 2 / (1 - t)
  have hq : ‖z‖ < q := by dsimp [q]; linarith
  have hg0 : g 0 = ‖z‖ := by simp [g]
  have hgcont : ContinuousAt g 0 := by
    dsimp [g]
    fun_prop (disch := norm_num)
  obtain ⟨ε, hε, hnear⟩ :=
    (Metric.continuousAt_iff.mp hgcont) ((q - ‖z‖) / 2) (by linarith)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (R / ε) R)
  refine ⟨N, ?_⟩
  intro n hNn
  have hNreal : max (R / ε) R < (N : ℝ) := by exact_mod_cast hN
  have hnreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnR : R < (n : ℝ) := lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hNreal) hnreal
  have hnpos : 0 < (n : ℝ) := by linarith
  have hRat : R / ε < (n : ℝ) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hNreal) hnreal
  have hRlt : R < ε * (n : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hRat
  have ht : 0 ≤ R / (n : ℝ) := div_nonneg hR hnpos.le
  have htn : R / (n : ℝ) < ε := (div_lt_iff₀ hnpos).2 hRlt
  have hnear' := hnear (x := R / (n : ℝ)) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht]
    exact htn)
  have hgBound : g (R / (n : ℝ)) < q := by
    rw [Real.dist_eq, hg0, abs_sub_lt_iff] at hnear'
    dsimp [q] at hnear' hq ⊢
    linarith
  have htnlt1 : R / (n : ℝ) < 1 := by
    apply (div_lt_iff₀ hnpos).2
    simpa using hnR
  have hdenpos : 0 < 1 - R / (n : ℝ) := by linarith
  have hdenlarger : 1 - R / (n : ℝ) ≤
      (1 + 1 / (n : ℝ)) * (1 - R / (n : ℝ)) := by
    have hInv : 0 ≤ 1 / (n : ℝ) := by positivity
    nlinarith [mul_nonneg hInv (le_of_lt hdenpos)]
  have hnumNonneg : 0 ≤ ‖z‖ * (1 + R / (n : ℝ)) ^ 2 :=
    mul_nonneg (norm_nonneg _) (sq_nonneg _)
  have hquot :
      ‖z‖ * (1 + R / (n : ℝ)) ^ 2 /
          ((1 + 1 / (n : ℝ)) * (1 - R / (n : ℝ))) ≤
        g (R / (n : ℝ)) := by
    dsimp [g]
    exact div_le_div_of_nonneg_left hnumNonneg hdenpos hdenlarger
  have hratioEq :
      ‖z‖ * ((n : ℝ) + R) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) - R)) =
        ‖z‖ * (1 + R / (n : ℝ)) ^ 2 /
          ((1 + 1 / (n : ℝ)) * (1 - R / (n : ℝ))) := by
    field_simp [hnpos.ne']
  refine ⟨hnR, ?_⟩
  rw [hratioEq]
  exact hquot.trans hgBound.le


/-- Compactness bounds every fixed finite prefix of the parameterized Gauss series uniformly. -/
theorem exists_finite_prefix_uniform_gaussParameterSeriesTerm_bound
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hc : ∀ p ∈ K, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (z : ℂ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ K,
      ‖gaussParameterSeriesTerm p z n‖ ≤ C := by
  have hb : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K,
      ‖gaussParameterSeriesTerm p z n‖ ≤ B := by
    intro n
    let f : ℂ × ℂ × ℂ → ℝ := fun p => ‖gaussParameterSeriesTerm p z n‖
    have hf : ContinuousOn f K := by
      exact (gaussParameterSeriesTerm_differentiableOn hc z n).continuousOn.norm
    obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hf)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro p hp
    have hle := hB (f p) ⟨p, hp, rfl⟩
    exact le_trans hle (le_max_left _ _)
  choose B hBnonneg hB using hb
  let C : ℝ := ∑ n ∈ Finset.range (N + 1), B n
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun k hk => hBnonneg k
  refine ⟨C, hC, ?_⟩
  intro n hn p hp
  have hnmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  calc
    ‖gaussParameterSeriesTerm p z n‖ ≤ B n := hB n p hp
    _ ≤ ∑ k ∈ Finset.range (N + 1), B k := by
      exact Finset.single_le_sum (s := Finset.range (N + 1))
        (fun k hk => hBnonneg k) hnmem

end DOZZ.Proofs
