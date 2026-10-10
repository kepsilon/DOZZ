/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.MomentExponent
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Geometric summability of positive weighted GMC annular exponents. -/

@[expose] public section

open scoped ENNReal

namespace DOZZ.Proofs

/-- The ratio corresponding to one dyadic annulus for the weighted GMC moment exponent. -/
noncomputable def weightedGmcAnnularRatio (γ α p : ℝ) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) ^
    (γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2)

/-- The exact insertion threshold makes the dyadic annular ratio strictly smaller than one. -/
theorem weightedGmcAnnularRatio_lt_one
    {γ α p : ℝ} (hγ : 0 < γ) (hp : 0 < p)
    (hpThreshold : p < 2 * (Q γ - α) / γ) :
    weightedGmcAnnularRatio γ α p < 1 := by
  have hξ : 0 < γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 :=
    (weightedGmcMomentExponent_pos_iff hγ hp).2 hpThreshold
  exact ENNReal.rpow_lt_one (by norm_num) hξ

/-- A finite annular sum with termwise geometric moment decay is bounded uniformly in the
number of annuli. The ratio is the weighted exponent ratio from the positive-threshold lemma. -/
theorem finite_annular_moment_series_bound
    (q C : ℝ≥0∞) (hq : q < 1) (N : ℕ) (b : ℕ → ℝ≥0∞)
    (hb : ∀ k ∈ Finset.range N, b k ≤ C * q ^ k) :
    (∑ k ∈ Finset.range N, b k ≤ C * (1 - q)⁻¹) ∧ (1 - q)⁻¹ ≠ ∞ := by
  have hden : 1 - q ≠ 0 := by
    intro hzero
    exact (not_le_of_gt hq) (tsub_eq_zero_iff_le.mp hzero)
  have hfinite : (1 - q)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hden
  have hgeom : ∑ k ∈ Finset.range N, q ^ k ≤ (1 - q)⁻¹ := by
    calc
      ∑ k ∈ Finset.range N, q ^ k ≤ ∑' k : ℕ, q ^ k :=
        ENNReal.sum_le_tsum _
      _ = (1 - q)⁻¹ := ENNReal.tsum_geometric q
  refine ⟨?_, hfinite⟩
  calc
    ∑ k ∈ Finset.range N, b k ≤ ∑ k ∈ Finset.range N, C * q ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hb k hk
    _ = C * ∑ k ∈ Finset.range N, q ^ k := by rw [Finset.mul_sum]
    _ ≤ C * (1 - q)⁻¹ := by gcongr


end DOZZ.Proofs
