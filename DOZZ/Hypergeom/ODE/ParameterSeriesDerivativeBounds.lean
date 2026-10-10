/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesDerivativeTerms
public import DOZZ.Hypergeom.ODE.ParameterSeriesBounds
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Normed.Module.Connected

/-! Locally uniform summable bounds for parameter derivatives of the Gauss series. -/

@[expose] public section

open scoped RightActions
open Nat Polynomial

namespace DOZZ.Proofs

/-- Parameters away from denominator poles form an open subset of the three-parameter space. -/
def gaussParameterPoleFreeDomain : Set (ℂ × ℂ × ℂ) :=
  {p | ∀ n : ℕ, p.2.2 ≠ -(n : ℂ)}

private theorem gaussNegNatCastRange_isClosed :
    IsClosed (Set.range (fun n : ℕ => -(n : ℂ))) := by
  have hIso : Isometry (fun n : ℕ => -(n : ℂ)) := by
    apply Isometry.of_dist_eq
    intro m n
    calc
      dist (-(m : ℂ)) (-(n : ℂ)) = dist (m : ℂ) (n : ℂ) := by simp
      _ = dist (m : ℤ) (n : ℤ) := by
        exact Complex.isometry_intCast.dist_eq m n
      _ = dist m n := by norm_cast
  exact hIso.isClosedEmbedding.isClosed_range

theorem gaussParameterPoleFreeDomain_isOpen :
    IsOpen gaussParameterPoleFreeDomain := by
  have hpre : gaussParameterPoleFreeDomain =
      (fun p : ℂ × ℂ × ℂ => p.2.2) ⁻¹'
        (Set.range (fun n : ℕ => -(n : ℂ)))ᶜ := by
    ext p
    simp [gaussParameterPoleFreeDomain, eq_comm]
  rw [hpre]
  exact gaussNegNatCastRange_isClosed.isOpen_compl.preimage
    (continuous_snd.comp continuous_snd)

/-- The scalar term multiplier contracts uniformly once the index dominates a compact parameter
bound and the point lies strictly inside the unit disk. -/
theorem gaussParameterSeriesRatio_norm_le
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) (R q : ℝ)
    (hR : 0 ≤ R) (hRn : R < (n : ℝ))
    (hA : ‖p.1‖ ≤ R) (hB : ‖p.2.1‖ ≤ R) (hC : ‖p.2.2‖ ≤ R)
    (hRatio : ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ q) :
    ‖gaussParameterSeriesRatio p z n‖ ≤ q := by
  have hn0 : 0 < (n : ℝ) := lt_of_le_of_lt hR hRn
  have hAnorm : ‖(n : ℂ) + p.1‖ ≤ (n : ℝ) + R := by
    calc
      ‖(n : ℂ) + p.1‖ ≤ ‖(n : ℂ)‖ + ‖p.1‖ := norm_add_le _ _
      _ = (n : ℝ) + ‖p.1‖ := by simp
      _ ≤ (n : ℝ) + R := by linarith
  have hBnorm : ‖(n : ℂ) + p.2.1‖ ≤ (n : ℝ) + R := by
    calc
      ‖(n : ℂ) + p.2.1‖ ≤ ‖(n : ℂ)‖ + ‖p.2.1‖ := norm_add_le _ _
      _ = (n : ℝ) + ‖p.2.1‖ := by simp
      _ ≤ (n : ℝ) + R := by linarith
  have hCnorm : (n : ℝ) - R ≤ ‖(n : ℂ) + p.2.2‖ := by
    have htriangle := norm_sub_norm_le (n : ℂ) ((n : ℂ) + p.2.2)
    have hnormN : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    rw [show (n : ℂ) - ((n : ℂ) + p.2.2) = -p.2.2 by abel,
      norm_neg, hnormN] at htriangle
    linarith
  have hdenpos : 0 < ((n : ℝ) + 1) * ((n : ℝ) - R) :=
    mul_pos (by linarith) (by linarith)
  have hdennorm : ((n : ℝ) + 1) * ((n : ℝ) - R) ≤
      ((n : ℝ) + 1) * ‖(n : ℂ) + p.2.2‖ :=
    mul_le_mul_of_nonneg_left hCnorm (by positivity)
  have hnum : ‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ ≤
      ‖z‖ * ((n : ℝ) + R) ^ 2 := by
    calc
      ‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖ ≤
          ((n : ℝ) + R) * ((n : ℝ) + R) * ‖z‖ := by gcongr
      _ = ‖z‖ * ((n : ℝ) + R) ^ 2 := by ring
  have hratioNorm : ‖gaussParameterSeriesRatio p z n‖ =
      (‖(n : ℂ) + p.1‖ * ‖(n : ℂ) + p.2.1‖ * ‖z‖) /
        (((n : ℝ) + 1) * ‖(n : ℂ) + p.2.2‖) := by
    rw [gaussParameterSeriesRatio, norm_div, norm_mul, norm_mul, norm_mul]
    have hn1 : ‖(n + 1 : ℂ)‖ = (n : ℝ) + 1 := by norm_cast
    rw [hn1]
  have hratio := div_le_div₀
    (mul_nonneg (norm_nonneg z) (sq_nonneg ((n : ℝ) + R))) hnum hdenpos hdennorm
  rw [hratioNorm]
  exact hratio.trans hRatio

/-- A uniform scalar recurrence for the derivatives of successive parameter-series terms. -/
theorem gaussParameterSeriesTerm_fderiv_norm_succ_le
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) (R q : ℝ)
    (hR : 0 ≤ R) (hRn : R < (n : ℝ)) (h3R : 3 * R ≤ (n : ℝ))
    (hA : ‖p.1‖ ≤ R) (hB : ‖p.2.1‖ ≤ R) (hC : ‖p.2.2‖ ≤ R)
    (hRatio : ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ q)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z (n + 1)) p‖ ≤
      q * ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ +
        (8 * ‖z‖) * ‖gaussParameterSeriesTerm p z n‖ := by
  have hratio := gaussParameterSeriesRatio_norm_le p z n R q hR hRn hA hB hC hRatio
  have hratioDeriv := gaussParameterSeriesRatioDeriv_norm_le
    p z n R hR hRn h3R hA hB hC
  rw [gaussParameterSeriesTerm_fderiv_succ p z n hc]
  calc
    ‖gaussParameterSeriesRatio p z n •
        fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p +
          gaussParameterSeriesTerm p z n •> gaussParameterSeriesRatioDeriv p z n‖ ≤
        ‖gaussParameterSeriesRatio p z n •
          fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ +
        ‖gaussParameterSeriesTerm p z n •> gaussParameterSeriesRatioDeriv p z n‖ :=
      norm_add_le _ _
    _ = ‖gaussParameterSeriesRatio p z n‖ *
          ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ +
        ‖gaussParameterSeriesRatioDeriv p z n‖ *
          ‖gaussParameterSeriesTerm p z n‖ := by
      rw [norm_smul, norm_smul]
      ring
    _ ≤ q * ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ +
        (8 * ‖z‖) * ‖gaussParameterSeriesTerm p z n‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hratio (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hratioDeriv (norm_nonneg _))

/-- On a bounded pole-free parameter set, a finite differentiated prefix and the product recurrence
give a summable uniform majorant for all parameter derivatives of the ordinary Gauss terms. -/
theorem exists_summable_uniform_gaussParameterSeriesTerm_fderiv_bound
    {K : Set (ℂ × ℂ × ℂ)} (N : ℕ) (C D R : ℝ) (z : ℂ)
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hz : ‖z‖ < 1)
    (hparams : ∀ p ∈ K,
      ‖p.1‖ ≤ R ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ R)
    (hc : ∀ p ∈ K, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ))
    (hN : ∀ n : ℕ, N ≤ n → R < (n : ℝ) ∧ 3 * R ≤ (n : ℝ) ∧
      ‖z‖ * ((n : ℝ) + R) ^ 2 /
        (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ (1 + ‖z‖) / 2)
    (hbase : ∀ n : ℕ, n ≤ N → ∀ p ∈ K,
      ‖gaussParameterSeriesTerm p z n‖ ≤ C)
    (hderivBase : ∀ n : ℕ, n ≤ N → ∀ p ∈ K,
      ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ ≤ D) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n : ℕ, ∀ p ∈ K,
        ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ ≤ u n := by
  let q : ℝ := (1 + ‖z‖) / 2
  let A : ℝ := (8 * ‖z‖ * C) / q
  let u : ℕ → ℝ := fun n => D * q ^ (n - N) +
    A * ((n - N : ℕ) : ℝ) * q ^ (n - N)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hqnonneg : 0 ≤ q := hq0.le
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hAnonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAq : A * q = 8 * ‖z‖ * C := by
    dsimp [A]
    field_simp [ne_of_gt hq0]
  have hterm : ∀ n : ℕ, ∀ p ∈ K,
      ‖gaussParameterSeriesTerm p z n‖ ≤ C * q ^ (n - N) := by
    intro n
    induction n with
    | zero =>
        intro p hp
        have hb := hbase 0 (Nat.zero_le N) p hp
        simpa [Nat.sub_eq_zero_of_le (Nat.zero_le N)] using hb
    | succ n ih =>
        intro p hp
        by_cases hn : N ≤ n
        · rcases hN n hn with ⟨hRn, h3R, hRatio⟩
          rcases hparams p hp with ⟨hAparam, hBparam, hCparam⟩
          have hstep := gaussParameterSeriesTerm_norm_succ_le
            p z n R q hR hRn hAparam hBparam hCparam hRatio (hc p hp)
          calc
            ‖gaussParameterSeriesTerm p z (n + 1)‖ ≤
                q * ‖gaussParameterSeriesTerm p z n‖ := hstep
            _ ≤ q * (C * q ^ (n - N)) :=
              mul_le_mul_of_nonneg_left (ih p hp) hqnonneg
            _ = C * q ^ ((n + 1) - N) := by
              have hsub : (n + 1) - N = (n - N) + 1 := by omega
              rw [hsub, pow_succ]
              ring
        · have hsucc : n + 1 ≤ N := by omega
          have hb := hbase (n + 1) hsucc p hp
          simpa [Nat.sub_eq_zero_of_le hsucc, pow_zero, mul_one] using hb
  have htailDeriv : ∀ k : ℕ, ∀ p ∈ K,
      ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z (N + k)) p‖ ≤
        D * q ^ k + A * (k : ℝ) * q ^ k := by
    intro k
    induction k with
    | zero =>
        intro p hp
        have hb := hderivBase N le_rfl p hp
        simpa using hb
    | succ k ih =>
        intro p hp
        have hNk : N ≤ N + k := Nat.le_add_right N k
        rcases hN (N + k) hNk with ⟨hRn, h3R, hRatio⟩
        rcases hparams p hp with ⟨hAparam, hBparam, hCparam⟩
        have hstep := gaussParameterSeriesTerm_fderiv_norm_succ_le
          p z (N + k) R q hR hRn h3R hAparam hBparam hCparam hRatio (hc p hp)
        have htermBound := hterm (N + k) p hp
        have hLnonneg : 0 ≤ 8 * ‖z‖ := by positivity
        calc
          ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z (N + (k + 1))) p‖ =
              ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z ((N + k) + 1)) p‖ := by
                congr 1
          _ ≤ q * ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z (N + k)) p‖ +
              (8 * ‖z‖) * ‖gaussParameterSeriesTerm p z (N + k)‖ := hstep
          _ ≤ q * (D * q ^ k + A * (k : ℝ) * q ^ k) +
              (8 * ‖z‖) * (C * q ^ k) := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left (ih p hp) hqnonneg)
                  (mul_le_mul_of_nonneg_left
                    (by simpa [Nat.add_sub_cancel_right] using htermBound) hLnonneg)
          _ = D * q ^ (k + 1) + A * ((k + 1 : ℕ) : ℝ) * q ^ (k + 1) := by
                rw [pow_succ]
                push_cast
                calc
                  q * (D * q ^ k + A * (k : ℝ) * q ^ k) +
                      (8 * ‖z‖) * (C * q ^ k) =
                      D * (q ^ k * q) + A * (k : ℝ) * (q ^ k * q) +
                      (8 * ‖z‖ * C) * q ^ k := by ring_nf
                  _ = D * (q ^ k * q) +
                      A * ((k : ℝ) + 1) * (q ^ k * q) := by
                    rw [← hAq]
                    ring_nf
  have hgeom : Summable (fun k : ℕ => q ^ k) :=
    summable_geometric_of_lt_one hqnonneg hq1
  have hpoly : Summable (fun k : ℕ => (k : ℝ) * q ^ k) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1 (r := q) (by
      simpa [Real.norm_eq_abs, abs_of_nonneg hqnonneg] using hq1)
    simpa [pow_one] using h
  have htail : Summable (fun k : ℕ => u (k + N)) := by
    convert (hgeom.mul_left D).add (hpoly.mul_left A) using 1
    funext k
    simp [u, mul_comm, mul_left_comm, mul_assoc, add_comm]
  have hu : Summable u := (summable_nat_add_iff N).1 htail
  refine ⟨u, hu, ?_⟩
  intro n p hp
  by_cases hn : N ≤ n
  · have hrepr : n = N + (n - N) := by omega
    rw [hrepr]
    simpa [u] using htailDeriv (n - N) p hp
  · have hle : n ≤ N := le_of_not_ge hn
    have hb := hderivBase n hle p hp
    have hsub : n - N = 0 := Nat.sub_eq_zero_of_le hle
    simpa [u, hsub, hqnonneg, hAnonneg] using hb

/-- Each finite Gauss-series term is smooth in parameters on the pole-free domain. -/
theorem gaussParameterSeriesTerm_contDiffOn
    {U : Set (ℂ × ℂ × ℂ)} (hU : ∀ p ∈ U, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ))
    (z : ℂ) (n : ℕ) :
    ContDiffOn ℂ 1 (fun p => gaussParameterSeriesTerm p z n) U := by
  have hden : ∀ p ∈ U, (ascPochhammer ℂ n).eval p.2.2 ≠ 0 := by
    intro p hp
    exact ordinaryHypergeometric_pochhammer_denominator_ne_zero n (hU p hp)
  have hpolyA : ContDiff ℂ 1 (fun x : ℂ => (ascPochhammer ℂ n).aeval x) :=
    (ascPochhammer ℂ n).contDiff_aeval (1 : WithTop ℕ∞)
  have hpoly : ContDiff ℂ 1 (fun x : ℂ => (ascPochhammer ℂ n).eval x) := by
    convert hpolyA using 1
    funext x
    simp
  have hA : ContDiffOn ℂ 1
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.1) U := by
    exact (hpoly.comp contDiff_fst).contDiffOn
  have hB : ContDiffOn ℂ 1
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.1) U := by
    exact (hpoly.comp (contDiff_fst.comp contDiff_snd)).contDiffOn
  have hC : ContDiffOn ℂ 1
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.2) U := by
    exact (hpoly.comp (contDiff_snd.comp contDiff_snd)).contDiffOn
  have hCinv := hC.inv hden
  change ContDiffOn ℂ 1
    (fun p : ℂ × ℂ × ℂ =>
      (n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval p.1 *
        (ascPochhammer ℂ n).eval p.2.1 *
          ((ascPochhammer ℂ n).eval p.2.2)⁻¹ * z ^ n) U
  exact (((contDiffOn_const.mul hA).mul hB).mul hCinv).mul contDiffOn_const

/-- Compactness bounds the Fréchet derivatives of every fixed finite prefix of the parameterized
Gauss series. -/
theorem exists_finite_prefix_uniform_gaussParameterSeriesTerm_fderiv_bound
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hc : ∀ p ∈ K, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (z : ℂ) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, n ≤ N → ∀ p ∈ K,
      ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ ≤ D := by
  have hb : ∀ n : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ K,
      ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ ≤ B := by
    intro n
    let f : ℂ × ℂ × ℂ → ℝ := fun p =>
      ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖
    have hf : ContinuousOn f K := by
      have hdomain : ∀ p ∈ gaussParameterPoleFreeDomain, ∀ k : ℕ,
          p.2.2 ≠ -(k : ℂ) := by
        intro p hp k
        exact hp k
      have hKdomain : K ⊆ gaussParameterPoleFreeDomain := by
        intro p hp k
        exact hc p hp k
      have hsmooth := gaussParameterSeriesTerm_contDiffOn
        (U := gaussParameterPoleFreeDomain) hdomain z n
      have hf' : ContinuousOn (fderiv ℂ (fun p => gaussParameterSeriesTerm p z n))
          gaussParameterPoleFreeDomain :=
        ContDiffOn.continuousOn_fderiv_of_isOpen hsmooth
          gaussParameterPoleFreeDomain_isOpen (by norm_num)
      exact hf'.norm.mono hKdomain
    obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hf)
    refine ⟨max B 0, le_max_right _ _, ?_⟩
    intro p hp
    have hle := hB (f p) ⟨p, hp, rfl⟩
    exact le_trans hle (le_max_left _ _)
  choose B hBnonneg hB using hb
  let D : ℝ := ∑ n ∈ Finset.range (N + 1), B n
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun k hk => hBnonneg k
  refine ⟨D, hD, ?_⟩
  intro n hn p hp
  have hnmem : n ∈ Finset.range (N + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le hn)
  calc
    ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ ≤ B n := hB n p hp
    _ ≤ ∑ k ∈ Finset.range (N + 1), B k := by
      exact Finset.single_le_sum (s := Finset.range (N + 1))
        (fun k hk => hBnonneg k) hnmem

/-- A compact pole-free parameter set admits a summable uniform majorant for the derivatives of
all ordinary Gauss-series terms, at every point strictly inside the unit disk. -/
theorem exists_summable_uniform_gaussParameterSeriesTerm_fderiv_bound_of_isCompact
    {K : Set (ℂ × ℂ × ℂ)} (hK : IsCompact K)
    (hc : ∀ p ∈ K, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n : ℕ, ∀ p ∈ K,
        ‖fderiv ℂ (fun p => gaussParameterSeriesTerm p z n) p‖ ≤ u n := by
  let f : ℂ × ℂ × ℂ → ℝ := fun p => max ‖p.1‖ (max ‖p.2.1‖ ‖p.2.2‖)
  have hf : Continuous f := by fun_prop
  obtain ⟨B, hB⟩ := bddAbove_def.mp (hK.bddAbove_image hf.continuousOn)
  let R : ℝ := max B 0
  have hR : 0 ≤ R := le_max_right _ _
  have hparams : ∀ p ∈ K,
      ‖p.1‖ ≤ R ∧ ‖p.2.1‖ ≤ R ∧ ‖p.2.2‖ ≤ R := by
    intro p hp
    have hfp : f p ≤ B := hB (f p) ⟨p, hp, rfl⟩
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · calc
        ‖p.1‖ ≤ f p := le_max_left _ _
        _ ≤ B := hfp
        _ ≤ R := le_max_left _ _
    · calc
        ‖p.2.1‖ ≤ max ‖p.2.1‖ ‖p.2.2‖ := le_max_left _ _
        _ ≤ f p := le_max_right _ _
        _ ≤ B := hfp
        _ ≤ R := le_max_left _ _
    · calc
        ‖p.2.2‖ ≤ max ‖p.2.1‖ ‖p.2.2‖ := le_max_right _ _
        _ ≤ f p := le_max_right _ _
        _ ≤ B := hfp
        _ ≤ R := le_max_left _ _
  obtain ⟨N₀, hN₀⟩ := exists_nat_uniform_gaussParameterSeries_ratio_bound z hz R hR
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (3 * R)
  let N : ℕ := max N₀ N₁
  have hN : ∀ n : ℕ, N ≤ n →
      R < (n : ℝ) ∧ 3 * R ≤ (n : ℝ) ∧
        ‖z‖ * ((n : ℝ) + R) ^ 2 /
          (((n : ℝ) + 1) * ((n : ℝ) - R)) ≤ (1 + ‖z‖) / 2 := by
    intro n hn
    have hN₀n : N₀ ≤ n := (le_max_left N₀ N₁).trans hn
    have hN₁n : N₁ ≤ n := (le_max_right N₀ N₁).trans hn
    rcases hN₀ n hN₀n with ⟨hRn, hRatio⟩
    have h3R : 3 * R ≤ (n : ℝ) :=
      le_of_lt (lt_of_lt_of_le hN₁ (by exact_mod_cast hN₁n))
    exact ⟨hRn, h3R, hRatio⟩
  obtain ⟨C, hC, hbase⟩ :=
    exists_finite_prefix_uniform_gaussParameterSeriesTerm_bound hK hc z N
  obtain ⟨D, _, hderivBase⟩ :=
    exists_finite_prefix_uniform_gaussParameterSeriesTerm_fderiv_bound hK hc z N
  exact exists_summable_uniform_gaussParameterSeriesTerm_fderiv_bound
    (K := K) N C D R z hC hR hz hparams hc hN hbase hderivBase

/-- The ordinary Gauss parameter series converges absolutely inside the unit disk whenever its
denominator parameter avoids its poles; terminating numerator parameters have infinite radius. -/
theorem gaussParameterSeriesTerm_summable
    (p : ℂ × ℂ × ℂ) (z : ℂ)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    Summable (fun n : ℕ => gaussParameterSeriesTerm p z n) := by
  let S := ordinaryHypergeometricSeries ℂ p.1 p.2.1 p.2.2
  have hrad : (1 : ENNReal) ≤ S.radius := by
    by_cases ha : ∃ k : ℕ, p.1 = -(k : ℂ)
    · obtain ⟨k, hk⟩ := ha
      have htop :
          (ordinaryHypergeometricSeries ℂ (-(k : ℂ)) p.2.1 p.2.2).radius = ⊤ :=
        ordinaryHypergeometric_radius_top_of_neg_nat₁ ℂ p.2.1 p.2.2
      dsimp [S]
      rw [hk, htop]
      exact le_top
    · by_cases hb : ∃ k : ℕ, p.2.1 = -(k : ℂ)
      · obtain ⟨k, hk⟩ := hb
        have htop :
            (ordinaryHypergeometricSeries ℂ p.1 (-(k : ℂ)) p.2.2).radius = ⊤ :=
          ordinaryHypergeometric_radius_top_of_neg_nat₂ ℂ p.1 p.2.2
        dsimp [S]
        rw [hk, htop]
        exact le_top
      · have habc : ∀ k : ℕ,
            (k : ℂ) ≠ -p.1 ∧ (k : ℂ) ≠ -p.2.1 ∧ (k : ℂ) ≠ -p.2.2 := by
          intro k
          refine ⟨?_, ?_, ?_⟩
          · intro h
            exact ha ⟨k, by linear_combination h⟩
          · intro h
            exact hb ⟨k, by linear_combination h⟩
          · intro h
            exact hc k (by linear_combination h)
        have hEq := ordinaryHypergeometricSeries_radius_eq_one ℂ
          p.1 p.2.1 p.2.2 habc
        dsimp [S]
        rw [hEq]
  have hzrad : (‖z‖₊ : ENNReal) < S.radius := by
    exact (ENNReal.coe_lt_coe.mpr hz).trans_le hrad
  have hmem : z ∈ Metric.eball (0 : ℂ) S.radius := by
    rw [mem_eball_zero_iff]
    exact hzrad
  have hseries : Summable (fun n : ℕ => S n fun _ => z) := S.summable hmem
  have hterms : ∀ n : ℕ, S n (fun _ => z) = gaussParameterSeriesTerm p z n := by
    intro n
    change ordinaryHypergeometricSeries ℂ p.1 p.2.1 p.2.2 n (fun _ => z) = _
    rw [ordinaryHypergeometricSeries_apply_eq]
    simp [gaussParameterSeriesTerm, smul_eq_mul, mul_assoc]
  exact hseries.congr fun n => hterms n

/-- Inside the unit disk, the ordinary Gauss function is Fréchet differentiable in all three
parameters at every tuple away from denominator poles. -/
theorem ordinaryHypergeometric_differentiableAt_params
    (p : ℂ × ℂ × ℂ) (z : ℂ)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      ordinaryHypergeometric q.1 q.2.1 q.2.2 z) p := by
  have hp : p ∈ gaussParameterPoleFreeDomain := hc
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp gaussParameterPoleFreeDomain_isOpen p hp
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hrε : r < ε := by dsimp [r]; linarith
  let K : Set (ℂ × ℂ × ℂ) := Metric.closedBall p r
  have hKcompact : IsCompact K := by
    exact isCompact_closedBall p r
  have hKpole : ∀ q ∈ K, ∀ k : ℕ, q.2.2 ≠ -(k : ℂ) := by
    intro q hq k
    have hqball : q ∈ Metric.ball p ε := Metric.closedBall_subset_ball hrε hq
    have hqdomain : q ∈ gaussParameterPoleFreeDomain := hball hqball
    exact hqdomain k
  obtain ⟨u, hu, huBound⟩ :=
    exists_summable_uniform_gaussParameterSeriesTerm_fderiv_bound_of_isCompact
      hKcompact hKpole z hz
  have hpK : p ∈ K := by
    exact Metric.mem_closedBall_self (le_of_lt hr)
  have hsum0 := gaussParameterSeriesTerm_summable p z hc hz
  have htermsDiff : ∀ n : ℕ, ∀ q ∈ Metric.ball p r,
      HasFDerivAt (fun x => gaussParameterSeriesTerm x z n)
        (fderiv ℂ (fun x => gaussParameterSeriesTerm x z n) q) q := by
    intro n q hq
    have hqK : q ∈ K := Metric.ball_subset_closedBall hq
    have hqPole := hKpole q hqK
    exact (gaussParameterSeriesTerm_differentiableAt q z n hqPole).hasFDerivAt
  have htermsBound : ∀ n : ℕ, ∀ q ∈ Metric.ball p r,
      ‖fderiv ℂ (fun x => gaussParameterSeriesTerm x z n) q‖ ≤ u n := by
    intro n q hq
    exact huBound n q (Metric.ball_subset_closedBall hq)
  have hsumDeriv := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    Metric.isPreconnected_ball htermsDiff htermsBound
    (Metric.mem_ball_self hr) hsum0 (Metric.mem_ball_self hr)
  have hsumEq :
      (fun q : ℂ × ℂ × ℂ => ordinaryHypergeometric q.1 q.2.1 q.2.2 z) =
        (fun q => ∑' n : ℕ, gaussParameterSeriesTerm q z n) := by
    funext q
    exact gaussParameterSeriesTerm_sum q.1 q.2.1 q.2.2 z
  rw [hsumEq]
  exact hsumDeriv.differentiableAt

end DOZZ.Proofs
