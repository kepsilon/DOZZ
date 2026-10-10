/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.MetricSpace.Basic

/-!
# DOZZ — reflection coefficient shift identities
-/

@[expose] public section

open Complex Filter Metric Set Topology

namespace DOZZ.Proofs

private lemma closedEmbedding_affine_nat {c d : ℂ} (hc : c ≠ 0) :
    IsClosedEmbedding (fun n : ℕ => c * (n : ℂ) + d) := by
  apply Metric.isClosedEmbedding_of_pairwise_le_dist (norm_pos_iff.mpr hc)
  intro m n hmn
  have hnat : (1 : ℝ) ≤ dist m n := Nat.pairwise_one_le_dist hmn
  have hnat' : (1 : ℝ) ≤ |(m : ℝ) - n| := by
    simpa only [Nat.dist_eq] using hnat
  have hnorm : ‖(m : ℂ) - n‖ = |(m : ℝ) - n| := by
    have hcast : (m : ℂ) - (n : ℂ) = (((m : ℝ) - n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [dist_eq_norm]
  calc
    ‖c‖ = ‖c‖ * 1 := by ring
    _ ≤ ‖c‖ * |(m : ℝ) - n| := mul_le_mul_of_nonneg_left hnat' (norm_nonneg _)
    _ = ‖c * ((m : ℂ) - n)‖ := by rw [norm_mul, hnorm]
    _ = ‖c * (m : ℂ) + d - (c * n + d)‖ := by congr 1; ring

private lemma eventually_affine_ne_neg_nat {c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, ∀ n : ℕ, c * α + d ≠ -(n : ℂ) := by
  let f : ℕ → ℂ := fun n => -(c⁻¹) * (n : ℂ) - d / c
  have hf : IsClosedEmbedding f := by
    simpa [f, sub_eq_add_neg, neg_div] using closedEmbedding_affine_nat (c := -(c⁻¹)) (d := -d / c)
      (neg_ne_zero.mpr (inv_ne_zero hc))
  have hbad : (Set.range f)ᶜ ∈ codiscrete ℂ := by
    apply compl_mem_codiscrete_iff.mpr
    exact ⟨hf.isClosed_range, hf.isEmbedding.isInducing.isDiscrete_range⟩
  filter_upwards [hbad] with α hα n
  intro heq
  apply hα
  refine ⟨n, ?_⟩
  have hsolve : α = f n := by
    calc
      α = (-(n : ℂ) - d) / c := by
        apply (eq_div_iff hc).2
        calc
          α * c = c * α := mul_comm _ _
          _ = -(n : ℂ) - d := by linear_combination heq
      _ = f n := by
        dsimp [f]
        field_simp [hc]
  exact hsolve.symm

private lemma eventually_affine_Gamma_ne_zero {c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * α + d) ≠ 0 := by
  filter_upwards [eventually_affine_ne_neg_nat hc] with α hα
  apply Complex.Gamma_ne_zero
  intro n hn
  exact hα n hn

private lemma lFun_one_sub {z : ℂ} (hz : z ≠ 0) :
    lFun (1 - z) = -z * (Complex.Gamma (-z) / Complex.Gamma z) := by
  have hnum : Complex.Gamma (1 - z) = -z * Complex.Gamma (-z) := by
    calc
      Complex.Gamma (1 - z) = Complex.Gamma (-z + 1) := by congr 1; ring
      _ = -z * Complex.Gamma (-z) :=
        Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)
  have hden : 1 - (1 - z) = z := by ring
  unfold lFun
  rw [hnum, hden]
  simp only [div_eq_mul_inv]
  ring

private lemma lFun_one_add {z : ℂ} (hz : z ≠ 0) :
    lFun (1 + z) = z * (Complex.Gamma z / Complex.Gamma (-z)) := by
  have hnum : Complex.Gamma (1 + z) = z * Complex.Gamma z := by
    calc
      Complex.Gamma (1 + z) = Complex.Gamma (z + 1) := by congr 1; ring
      _ = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  have hden : 1 - (1 + z) = -z := by ring
  unfold lFun
  rw [hnum, hden]
  simp only [div_eq_mul_inv]
  ring

private lemma eventually_Gamma_Qsub_affine {Q c d : ℂ} (hc : c ≠ 0) :
    ∀ᶠ α : ℂ in codiscrete ℂ, Complex.Gamma (c * (Q - α) + d) ≠ 0 := by
  have h := eventually_affine_Gamma_ne_zero (c := -c) (d := c * Q + d)
    (neg_ne_zero.mpr hc)
  filter_upwards [h] with α hα
  have heq : c * (Q - α) + d = -c * α + (c * Q + d) := by ring
  rw [heq]
  exact hα

private lemma lFun_mul_neg {q : ℂ} (hq : q ≠ 0)
    (hΓq : Complex.Gamma q ≠ 0) (hΓnegq : Complex.Gamma (-q) ≠ 0) :
    lFun q * lFun (-q) = -1 / q ^ 2 := by
  have hrec₁ : Complex.Gamma (1 - q) = -q * Complex.Gamma (-q) := by
    simpa [sub_eq_add_neg, add_comm] using
      Complex.Gamma_add_one (-q) (neg_ne_zero.mpr hq)
  have hrec₂ : Complex.Gamma (1 + q) = q * Complex.Gamma q := by
    simpa [add_comm] using Complex.Gamma_add_one q hq
  unfold lFun
  rw [hrec₁, show 1 - -q = 1 + q by simp, hrec₂]
  field_simp [hq, hΓq, hΓnegq]

private lemma gamma_ratio_shift_b {t p q : ℂ} (htq : t = q * p)
    (hΓt : Complex.Gamma t ≠ 0) (hΓnegT : Complex.Gamma (-t) ≠ 0)
    (hΓtq : Complex.Gamma (t + q) ≠ 0) (hΓnegTq : Complex.Gamma (-t - q) ≠ 0)
    (hΓp : Complex.Gamma p ≠ 0)
    (hΓp1 : Complex.Gamma (p + 1) ≠ 0) (hΓnegP1 : Complex.Gamma (-p - 1) ≠ 0) :
    (Complex.Gamma (-t - q) / Complex.Gamma (t + q) *
      (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))) *
        (lFun (1 - t) * lFun (1 + t + q)) =
      q ^ 2 * (Complex.Gamma (-t) / Complex.Gamma t *
        (Complex.Gamma (-p) / Complex.Gamma p)) := by
  have ht : t ≠ 0 := by
    intro h
    simp [h] at hΓt
  have htq' : t + q ≠ 0 := by
    intro h
    simp [h] at hΓtq
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hΓp
  have hp1 : p + 1 ≠ 0 := by
    intro h
    simp [h] at hΓp1
  have hrecN : Complex.Gamma (-p) = (-p - 1) * Complex.Gamma (-p - 1) := by
    have hzero : -p - 1 ≠ 0 := by
      intro h
      simp [h] at hΓnegP1
    have harg : (-p - 1) + 1 = -p := by ring
    calc
      Complex.Gamma (-p) = Complex.Gamma ((-p - 1) + 1) :=
        congrArg Complex.Gamma harg.symm
      _ = (-p - 1) * Complex.Gamma (-p - 1) :=
        Complex.Gamma_add_one (-p - 1) hzero
  have hrecP : Complex.Gamma (p + 1) = p * Complex.Gamma p := by
    exact Complex.Gamma_add_one p hp
  have hΓt' : Complex.Gamma (q * p) ≠ 0 := by
    simpa [htq] using hΓt
  have hΓnegT' : Complex.Gamma (-(q * p)) ≠ 0 := by
    simpa [htq] using hΓnegT
  have hΓtq' : Complex.Gamma (q * p + q) ≠ 0 := by
    simpa [htq] using hΓtq
  have hΓnegTq' : Complex.Gamma (-q - q * p) ≠ 0 := by
    have heq : -q - q * p = -t - q := by rw [htq]; ring
    rw [heq]
    exact hΓnegTq
  have hΓqp1 : Complex.Gamma (q * (p + 1)) ≠ 0 := by
    have heq : q * (p + 1) = q * p + q := by ring
    rw [heq]
    exact hΓtq'
  have hΓnegqp1 : Complex.Gamma (-(q * (p + 1))) ≠ 0 := by
    have heq : -(q * (p + 1)) = -q - q * p := by ring
    rw [heq]
    exact hΓnegTq'
  have harg : 1 + t + q = 1 + (t + q) := by ring
  rw [lFun_one_sub ht, harg, lFun_one_add htq', hrecN, hrecP, htq]
  field_simp [hΓt', hΓnegT', hΓtq', hΓnegTq', hΓp, hΓp1, hΓnegP1,
    hΓqp1, hΓnegqp1, hp, hp1, ht, htq']
  rw [show q * (-p - 1) = -(q * (p + 1)) by ring]
  field_simp [hΓqp1, hΓnegqp1]
  ring

private lemma lFun_gammaSq_real (γ : ℝ) :
    lFun ((γ : ℂ) ^ 2 / 4) =
      ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ) := by
  have harg : ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg]
  unfold lFun
  have hden : Complex.Gamma (1 - (γ ^ 2 / 4 : ℝ)) =
      (Real.Gamma (1 - γ ^ 2 / 4) : ℂ) := by
    convert Complex.Gamma_ofReal (1 - γ ^ 2 / 4) using 1
    simp
  rw [Complex.Gamma_ofReal, hden]
  exact (Complex.ofReal_div _ _).symm

private lemma complexGamma_neg_sq_ne_zero {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Complex.Gamma (-((γ : ℂ) ^ 2 / 4)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have hq : γ ^ 2 / 4 = (n : ℝ) := by
    have hreal : - (γ ^ 2 / 4) = -(n : ℝ) := by exact_mod_cast hn
    exact neg_inj.mp hreal
  have hγsq_pos : 0 < γ ^ 2 / 4 := by positivity
  have hγsq_lt : γ ^ 2 / 4 < 1 := by linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst n
    norm_num at hq
    linarith
  · have hnle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    linarith

variable {γ : ℝ}

/-- First reflection shift [KRV, (shift1DOZZ)] (correct as printed). -/
theorem reflectionDOZZ_shift_b (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ (α - γ / 2) =
        -(μ * Real.pi) * reflectionDOZZ γ μ α /
          (lFun (-(γ ^ 2 / 4)) * lFun (γ * α / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * α / 2)) := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hqRpos : 0 < γ ^ 2 / 4 := by positivity
  have hqRlt : γ ^ 2 / 4 < 1 := by
    linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  let qR : ℝ := γ ^ 2 / 4
  let q : ℂ := (γ : ℂ) ^ 2 / 4
  let b : ℂ := (γ : ℂ) / 2
  let c : ℂ := 2 / (γ : ℂ)
  let Qc : ℂ := (Q γ : ℂ)
  have hqCast : (qR : ℂ) = q := by
    dsimp [q, qR]
    push_cast
    ring
  have hqpos : 0 < qR := by exact hqRpos
  have hΓq : Complex.Gamma q ≠ 0 := by
    rw [← hqCast, Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hqpos).ne'
  have hΓ1q : Complex.Gamma (1 + q) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [add_re, one_re]
    rw [← hqCast]
    simp only [Complex.ofReal_re]
    linarith
  have hqArg : (qR : ℂ) = (γ : ℂ) ^ 2 / 4 := by
    dsimp [qR]
    push_cast
    ring
  have hΓnegq : Complex.Gamma (-q) ≠ 0 := by
    rw [← hqCast, hqArg]
    exact complexGamma_neg_sq_ne_zero hγ hγ2
  have hqne : q ≠ 0 := by
    dsimp [q]
    exact div_ne_zero (pow_ne_zero 2 hγc) (by norm_num)
  have hLneg : lFun (-q) ≠ 0 := by
    unfold lFun
    apply div_ne_zero hΓnegq
    have hΓ1negq : Complex.Gamma (1 - -q) ≠ 0 := by
      rw [show 1 - -q = 1 + q by ring]
      exact hΓ1q
    exact hΓ1negq
  have hLprod := lFun_mul_neg hqne hΓq hΓnegq
  have hLreal := lFun_gammaSq_real γ
  have hLpos : 0 < (lFun q).re := by
    rw [hLreal, Complex.ofReal_re]
    exact div_pos (Real.Gamma_pos_of_pos hqRpos)
      (Real.Gamma_pos_of_pos (by linarith))
  have hbase : 0 < dozzBase γ μ := by
    rw [dozzBase]
    exact mul_pos (mul_pos Real.pi_pos hμ) hLpos
  let B : ℂ := (dozzBase γ μ : ℝ)
  let C : ℂ := (μ * Real.pi : ℝ)
  have hbaseEq : B = C * lFun q := by
    change ((Real.pi * μ * (lFun q).re : ℝ) : ℂ) = _
    rw [hLreal]
    simp only [Complex.ofReal_re]
    change ((Real.pi * μ *
      (Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4)) : ℝ) : ℂ) =
      ((μ * Real.pi : ℝ) : ℂ) *
        ((Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4) : ℝ) : ℂ)
    push_cast
    ring
  have hcoeff : B * q ^ 2 = -C / lFun (-q) := by
    apply (eq_div_iff hLneg).2
    rw [hbaseEq]
    calc
      C * lFun q * q ^ 2 * lFun (-q) = C * (lFun q * lFun (-q)) * q ^ 2 := by ring
      _ = C * (-1 / q ^ 2) * q ^ 2 := by rw [hLprod]
      _ = -C := by field_simp [hqne]
  have hb : b ≠ 0 := by
    dsimp [b]
    exact div_ne_zero hγc (by norm_num)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact div_ne_zero (by norm_num) hγc
  have hT := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := 0) hb
  have hNegT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 0)
    (neg_ne_zero.mpr hb)
  have hTq := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := q) hb
  have hNegTq := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := -q)
    (neg_ne_zero.mpr hb)
  have hP := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 0) hc
  have hP1 := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 1) hc
  have hNegP1 := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := -1)
    (neg_ne_zero.mpr hc)
  have hOneSubT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 1)
    (neg_ne_zero.mpr hb)
  have hOnePlusTq := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := 1 + q) hb
  filter_upwards [hT, hNegT, hTq, hNegTq, hP, hP1, hNegP1, hOneSubT, hOnePlusTq]
      with α hT hNegT hTq hNegTq hP hP1 hNegP1 hOneSubT hOnePlusTq
  let A : ℂ := Qc - α
  let t : ℂ := b * A
  let p : ℂ := c * A
  have hΓt : Complex.Gamma t ≠ 0 := by simpa [t, A] using hT
  have hΓnegT : Complex.Gamma (-t) ≠ 0 := by simpa [t, A] using hNegT
  have hΓtq : Complex.Gamma (t + q) ≠ 0 := by simpa [t, A] using hTq
  have hΓnegTq : Complex.Gamma (-t - q) ≠ 0 := by
    simpa [t, A, sub_eq_add_neg, add_comm] using hNegTq
  have hΓp : Complex.Gamma p ≠ 0 := by simpa [p, A] using hP
  have hΓp1 : Complex.Gamma (p + 1) ≠ 0 := by simpa [p, A] using hP1
  have hΓnegP1 : Complex.Gamma (-p - 1) ≠ 0 := by
    simpa [p, A, sub_eq_add_neg, add_comm] using hNegP1
  have hΓ1subT : Complex.Gamma (1 - t) ≠ 0 := by
    simpa [t, A, sub_eq_add_neg, add_comm] using hOneSubT
  have hΓ1plusTq : Complex.Gamma (1 + t + q) ≠ 0 := by
    simpa [t, A, add_assoc, add_comm, add_left_comm] using hOnePlusTq
  have htq : t = q * p := by
    dsimp [t, p, A, b, c, q]
    field_simp [hγc]
    ring
  have htne : t ≠ 0 := by
    intro h
    simp [h] at hΓt
  have htqne : t + q ≠ 0 := by
    intro h
    simp [h] at hΓtq
  have hL1 : lFun (1 - t) ≠ 0 := by
    unfold lFun
    have hden : 1 - (1 - t) = t := by ring
    rw [hden]
    exact div_ne_zero hΓ1subT hΓt
  have hL2 : lFun (1 + t + q) ≠ 0 := by
    unfold lFun
    have hden : 1 - (1 + t + q) = -t - q := by ring
    rw [hden]
    exact div_ne_zero hΓ1plusTq hΓnegTq
  have hAshift : Qc - (α - b) = A + b := by
    dsimp [A]
    ring
  have hExp : 2 * A / (γ : ℂ) = p := by
    dsimp [p, c]
    field_simp [hγc]
  have hTarg : (γ : ℂ) * A / 2 = t := by
    dsimp [t, b]
    ring
  have hExpShift : 2 * (Qc - (α - b)) / (γ : ℂ) = p + 1 := by
    rw [hAshift]
    dsimp [p, c, b]
    field_simp [hγc]
  have hTargShift : (γ : ℂ) * (Qc - (α - b)) / 2 = t + q := by
    rw [hAshift]
    dsimp [t, b, q]
    ring
  have htFormula : t = 1 + q - (γ : ℂ) * α / 2 := by
    dsimp [t, b, A, Qc, q]
    rw [show (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 by simp [Q]]
    field_simp [hγc]
    ring
  have hLarg1 : (γ : ℂ) * α / 2 - q = 1 - t := by rw [htFormula]; ring
  have hLarg2 : 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * α / 2 = 1 + t + q := by
    rw [htFormula]
    ring
  have hExp' : 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p := by
    simpa [A, Qc] using hExp
  have hTarg' : (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t := by
    simpa [A, Qc] using hTarg
  have hExpShift' :
      2 * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / (γ : ℂ) = p + 1 := by
    simpa [Qc, b] using hExpShift
  have hTargShift' :
      (γ : ℂ) * ((Q γ : ℂ) - (α - (γ : ℂ) / 2)) / 2 = t + q := by
    simpa [Qc, b] using hTargShift
  have hpow : B ^ (p + 1) = B * B ^ p := by
    have hBne : B ≠ 0 := by
      dsimp [B]
      exact_mod_cast hbase.ne'
    rw [Complex.cpow_add p 1 hBne]
    simp only [Complex.cpow_one]
    ring
  let Gshift : ℂ := Complex.Gamma (-t - q) / Complex.Gamma (t + q) *
    (Complex.Gamma (-p - 1) / Complex.Gamma (p + 1))
  let Gold : ℂ := Complex.Gamma (-t) / Complex.Gamma t *
    (Complex.Gamma (-p) / Complex.Gamma p)
  have hratio := gamma_ratio_shift_b htq hΓt hΓnegT hΓtq hΓnegTq hΓp hΓp1 hΓnegP1
  have hratio' : Gshift * (lFun (1 - t) * lFun (1 + t + q)) = q ^ 2 * Gold := by
    simpa [Gshift, Gold] using hratio
  have hscaled : (B * Gshift) * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) =
      -C * Gold := by
    calc
      _ = (B * lFun (-q)) * (Gshift * (lFun (1 - t) * lFun (1 + t + q))) := by ring
      _ = (B * lFun (-q)) * (q ^ 2 * Gold) := by
        rw [hratio']
      _ = (B * q ^ 2) * lFun (-q) * Gold := by ring
      _ = _ := by rw [hcoeff]; field_simp [hLneg]
  have hden : lFun (-q) * lFun (1 - t) * lFun (1 + t + q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hLneg hL1) hL2
  have hleft :
      reflectionDOZZ γ μ (α - γ / 2) = -B ^ (p + 1) * Gshift := by
    have hnegTq : -(t + q) = -t - q := by ring
    have hnegP1 : -(p + 1) = -p - 1 := by ring
    simp only [reflectionDOZZ, hExpShift', hTargShift', hnegTq, hnegP1, Gshift, B]
    ring
  have hright :
      reflectionDOZZ γ μ α = -B ^ p * Gold := by
    simp only [reflectionDOZZ, hExp', hTarg', Gold, B]
    ring
  have hfinal :
      reflectionDOZZ γ μ (α - γ / 2) =
        -C * reflectionDOZZ γ μ α /
          (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) := by
    apply (eq_div_iff hden).2
    rw [hleft, hright, hpow]
    calc
      -(B * B ^ p) * Gshift * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q)) =
        -B ^ p * ((B * Gshift) * (lFun (-q) * lFun (1 - t) * lFun (1 + t + q))) := by ring
      _ = -B ^ p * (-C * Gold) := by rw [hscaled]
      _ = -C * (-B ^ p * Gold) := by ring
  simpa [q, C, hLarg1, hLarg2, Complex.ofReal_mul] using hfinal

private lemma gamma_ratio_shift_binv {t p N : ℂ} (htN : t * N = p)
    (hΓt : Complex.Gamma t ≠ 0) (hΓnegT : Complex.Gamma (-t) ≠ 0)
    (hΓtm1 : Complex.Gamma (t - 1) ≠ 0)
    (hΓp : Complex.Gamma p ≠ 0) (hΓnegP : Complex.Gamma (-p) ≠ 0)
    (hΓpmN : Complex.Gamma (p - N) ≠ 0) (hΓNmp : Complex.Gamma (N - p) ≠ 0) :
    (Complex.Gamma (-t) / Complex.Gamma t *
      (Complex.Gamma (-p) / Complex.Gamma p)) *
        (lFun (1 + N - p) * lFun (1 + p)) =
      N ^ 2 * (Complex.Gamma (1 - t) / Complex.Gamma (t - 1) *
        (Complex.Gamma (N - p) / Complex.Gamma (p - N))) := by
  have ht : t ≠ 0 := by
    intro h
    simp [h] at hΓt
  have htm1 : t - 1 ≠ 0 := by
    intro h
    simp [h] at hΓtm1
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hΓp
  have hNmp : N - p ≠ 0 := by
    intro h
    simp [h] at hΓNmp
  have hrecTm : Complex.Gamma (1 - t) = -t * Complex.Gamma (-t) := by
    simpa [sub_eq_add_neg, add_comm] using
      Complex.Gamma_add_one (-t) (neg_ne_zero.mpr ht)
  have hrecT : Complex.Gamma t = (t - 1) * Complex.Gamma (t - 1) := by
    have harg : t - 1 + 1 = t := by ring
    calc
      Complex.Gamma t = Complex.Gamma (t - 1 + 1) := congrArg Complex.Gamma harg.symm
      _ = (t - 1) * Complex.Gamma (t - 1) := Complex.Gamma_add_one (t - 1) htm1
  have harg : 1 + N - p = 1 + (N - p) := by ring
  rw [harg, lFun_one_add hNmp, lFun_one_add hp, hrecTm, hrecT]
  have halg : p * (N - p) = N ^ 2 * (-t) * (t - 1) := by
    calc
      p * (N - p) = (t * N) * (N - t * N) := by rw [htN]
      _ = N ^ 2 * (-t) * (t - 1) := by ring
  field_simp [hΓt, hΓnegT, hΓtm1, hΓp, hΓnegP, hΓpmN, hΓNmp,
    ht, htm1, hp, hNmp]
  rw [halg]
  ring_nf

theorem reflectionDOZZ_shift_binv (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ) :
    ∀ᶠ α in codiscrete ℂ,
      reflectionDOZZ γ μ α =
        -(((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)) *
          reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * α / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * α / γ)) := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hqRpos : 0 < γ ^ 2 / 4 := by positivity
  have hqRlt : γ ^ 2 / 4 < 1 := by linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  have hLreal := lFun_gammaSq_real γ
  have hLpos : 0 < (lFun ((γ : ℂ) ^ 2 / 4)).re := by
    rw [hLreal, Complex.ofReal_re]
    exact div_pos (Real.Gamma_pos_of_pos hqRpos)
      (Real.Gamma_pos_of_pos (by linarith))
  have hbase : 0 < dozzBase γ μ := by
    rw [dozzBase]
    exact mul_pos (mul_pos Real.pi_pos hμ) hLpos
  let B : ℂ := (dozzBase γ μ : ℝ)
  let NR : ℝ := 4 / γ ^ 2
  let N : ℂ := (NR : ℂ)
  have hNRpos : 0 < NR := by dsimp [NR]; positivity
  have hNne : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast hNRpos.ne'
  have hNcast : ((4 / γ ^ 2 : ℝ) : ℂ) = N := rfl
  have hNcomplex : N = 4 / (γ : ℂ) ^ 2 := by
    dsimp [N, NR]
    push_cast
    field_simp [hγc]
  have hΓN : Complex.Gamma N ≠ 0 := by
    dsimp [N]
    rw [Complex.Gamma_ofReal]
    exact_mod_cast (Real.Gamma_pos_of_pos hNRpos).ne'
  have hΓnegN : Complex.Gamma (-N) ≠ 0 := by
    dsimp [N]
    apply Complex.Gamma_ne_zero
    intro k hk
    have hval : NR = (k : ℝ) := by
      have hreal : -NR = -(k : ℝ) := by exact_mod_cast hk
      linarith
    have hval' : 4 / γ ^ 2 = (k : ℝ) := by simpa [NR] using hval
    exact hγk k hval'
  have hΓ1subN : Complex.Gamma (1 - N) ≠ 0 := by
    dsimp [N]
    apply Complex.Gamma_ne_zero
    intro k hk
    have hval : NR = (k + 1 : ℝ) := by
      have hreal : 1 - NR = -(k : ℝ) := by exact_mod_cast hk
      linarith
    have hval' : 4 / γ ^ 2 = ((k + 1 : ℕ) : ℝ) := by
      simpa [NR] using hval
    exact hγk (k + 1) hval'
  have hΓ1plusN : Complex.Gamma (1 + N) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    rw [add_re, one_re]
    dsimp [N]
    linarith
  have hLN : lFun N ≠ 0 := by
    unfold lFun
    exact div_ne_zero hΓN hΓ1subN
  have hLnegN : lFun (-N) ≠ 0 := by
    unfold lFun
    apply div_ne_zero hΓnegN
    have hΓ1negN : Complex.Gamma (1 - -N) ≠ 0 := by
      rw [show 1 - -N = 1 + N by ring]
      exact hΓ1plusN
    exact hΓ1negN
  have hLprodN := lFun_mul_neg hNne hΓN hΓnegN
  have hb : (γ : ℂ) / 2 ≠ 0 := div_ne_zero hγc (by norm_num)
  have hc : (2 : ℂ) / (γ : ℂ) ≠ 0 := div_ne_zero (by norm_num) hγc
  let b : ℂ := (γ : ℂ) / 2
  let c : ℂ := (2 : ℂ) / (γ : ℂ)
  let Qc : ℂ := (Q γ : ℂ)
  have hT := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := 0) hb
  have hNegT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 0)
    (neg_ne_zero.mpr hb)
  have hTm1 := eventually_Gamma_Qsub_affine (Q := Qc) (c := b) (d := -1) hb
  have hOneSubT := eventually_Gamma_Qsub_affine (Q := Qc) (c := -b) (d := 1)
    (neg_ne_zero.mpr hb)
  have hP := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 0) hc
  have hNegP := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := 0)
    (neg_ne_zero.mpr hc)
  have hPmN := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := -N) hc
  have hNmp := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := N)
    (neg_ne_zero.mpr hc)
  have hOnePlusNmp := eventually_Gamma_Qsub_affine (Q := Qc) (c := -c) (d := 1 + N)
    (neg_ne_zero.mpr hc)
  have hOnePlusP := eventually_Gamma_Qsub_affine (Q := Qc) (c := c) (d := 1) hc
  filter_upwards [hT, hNegT, hTm1, hOneSubT, hP, hNegP, hPmN, hNmp,
      hOnePlusNmp, hOnePlusP]
      with α hT hNegT hTm1 hOneSubT hP hNegP hPmN hNmp hOnePlusNmp hOnePlusP
  let A : ℂ := Qc - α
  let t : ℂ := b * A
  let p : ℂ := c * A
  have hΓt : Complex.Gamma t ≠ 0 := by simpa [t, A] using hT
  have hΓnegT : Complex.Gamma (-t) ≠ 0 := by simpa [t, A] using hNegT
  have hΓtm1 : Complex.Gamma (t - 1) ≠ 0 := by
    simpa [t, A, sub_eq_add_neg, add_comm] using hTm1
  have hΓp : Complex.Gamma p ≠ 0 := by simpa [p, A] using hP
  have hΓnegP : Complex.Gamma (-p) ≠ 0 := by simpa [p, A] using hNegP
  have hΓpmN : Complex.Gamma (p - N) ≠ 0 := by
    simpa [p, A, sub_eq_add_neg, add_comm] using hPmN
  have hΓNmp : Complex.Gamma (N - p) ≠ 0 := by
    simpa [p, A, sub_eq_add_neg, add_comm] using hNmp
  have hΓ1subT : Complex.Gamma (1 - t) ≠ 0 := by
    simpa [t, A, sub_eq_add_neg, add_comm] using hOneSubT
  have hΓ1plusNmp : Complex.Gamma (1 + N - p) ≠ 0 := by
    simpa [p, A, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hOnePlusNmp
  have hΓ1plusP : Complex.Gamma (1 + p) ≠ 0 := by
    simpa [p, A, add_comm] using hOnePlusP
  have htN : t * N = p := by
    dsimp [t, p, A, b, c]
    rw [hNcomplex]
    field_simp [hγc]
    ring
  have hL1 : lFun (1 + N - p) ≠ 0 := by
    unfold lFun
    have hden : 1 - (1 + N - p) = p - N := by ring
    rw [hden]
    exact div_ne_zero hΓ1plusNmp hΓpmN
  have hL2 : lFun (1 + p) ≠ 0 := by
    unfold lFun
    have hden : 1 - (1 + p) = -p := by ring
    rw [hden]
    exact div_ne_zero hΓ1plusP hΓnegP
  have hAshift : Qc - (α + c) = A - c := by dsimp [A]; ring
  have hExp : 2 * A / (γ : ℂ) = p := by
    dsimp [p, c]
    field_simp [hγc]
  have hTarg : (γ : ℂ) * A / 2 = t := by dsimp [t, b]; ring
  have hExpShift : 2 * (Qc - (α + c)) / (γ : ℂ) = p - N := by
    rw [hAshift]
    calc
      2 * (A - c) / (γ : ℂ) = 2 * A / (γ : ℂ) - 2 * c / (γ : ℂ) := by ring
      _ = p - N := by
        rw [hExp]
        have hcN : 2 * c / (γ : ℂ) = N := by
          dsimp [c]
          rw [hNcomplex]
          field_simp [hγc]
          norm_num
        rw [hcN]
  have hTargShift : (γ : ℂ) * (Qc - (α + c)) / 2 = t - 1 := by
    rw [hAshift]
    calc
      (γ : ℂ) * (A - c) / 2 = (γ : ℂ) * A / 2 - (γ : ℂ) * c / 2 := by ring
      _ = t - 1 := by
        rw [hTarg]
        have hγc_half : (γ : ℂ) * c / 2 = 1 := by
          dsimp [c]
          field_simp [hγc]
        rw [hγc_half]
  have hQc : (Q γ : ℂ) = 2 / (γ : ℂ) + (γ : ℂ) / 2 := by simp [Q]
  have hpFormula : p = 1 + N - 2 * α / (γ : ℂ) := by
    dsimp [p, c, A, Qc]
    rw [hQc, hNcomplex]
    field_simp [hγc]
    ring
  have hLarg1 : 2 * α / (γ : ℂ) = 1 + N - p := by rw [hpFormula]; ring
  have hLarg2 : 2 + N - 2 * α / (γ : ℂ) = 1 + p := by rw [hpFormula]; ring
  have hExp' : 2 * ((Q γ : ℂ) - α) / (γ : ℂ) = p := by
    simpa [A, Qc] using hExp
  have hTarg' : (γ : ℂ) * ((Q γ : ℂ) - α) / 2 = t := by
    simpa [A, Qc] using hTarg
  have hcCast : ((2 / γ : ℝ) : ℂ) = c := by
    dsimp [c]
    push_cast
    field_simp [hγc]
  have hExpShift' :
      2 * ((Q γ : ℂ) - (α + (2 : ℂ) / (γ : ℂ))) / (γ : ℂ) = p - N := by
    simpa [Qc, c] using hExpShift
  have hTargShift' :
      (γ : ℂ) * ((Q γ : ℂ) - (α + (2 : ℂ) / (γ : ℂ))) / 2 = t - 1 := by
    simpa [Qc, c] using hTargShift
  have hBne : B ≠ 0 := by
    dsimp [B]
    exact_mod_cast hbase.ne'
  have hpow : B ^ p = B ^ N * B ^ (p - N) := by
    calc
      B ^ p = B ^ (N + (p - N)) := by congr 1; ring
      _ = B ^ N * B ^ (p - N) := Complex.cpow_add N (p - N) hBne
  let Gorig : ℂ := Complex.Gamma (-t) / Complex.Gamma t *
    (Complex.Gamma (-p) / Complex.Gamma p)
  let Gshift : ℂ := Complex.Gamma (1 - t) / Complex.Gamma (t - 1) *
    (Complex.Gamma (N - p) / Complex.Gamma (p - N))
  have hratio := gamma_ratio_shift_binv htN hΓt hΓnegT hΓtm1 hΓp hΓnegP hΓpmN hΓNmp
  have hratio' : Gorig * (lFun (1 + N - p) * lFun (1 + p)) = N ^ 2 * Gshift := by
    simpa [Gorig, Gshift] using hratio
  have hden : lFun (-N) * lFun (1 + N - p) * lFun (1 + p) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hLnegN hL1) hL2
  have hscaled : Gorig * (lFun N * lFun (-N) *
      lFun (1 + N - p) * lFun (1 + p)) = -Gshift := by
    calc
      _ = (Gorig * (lFun (1 + N - p) * lFun (1 + p))) *
          (lFun N * lFun (-N)) := by ring
      _ = (N ^ 2 * Gshift) * (lFun N * lFun (-N)) := by rw [hratio']
      _ = -Gshift := by rw [hLprodN]; field_simp [hNne]
  have hGammaCoeff :
      -Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) = Gshift / lFun N := by
    apply (eq_div_iff hLN).2
    calc
      (-Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) * lFun N =
          -(Gorig * (lFun N * lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) := by ring
      _ = Gshift := by rw [hscaled]; ring
  have hnegTm1 : -(t - 1) = 1 - t := by ring
  have hnegPmN : -(p - N) = N - p := by ring
  have hleft : reflectionDOZZ γ μ (α + 2 / γ) = -B ^ (p - N) * Gshift := by
    simp only [reflectionDOZZ, hExpShift', hTargShift', hnegTm1, hnegPmN, Gshift, B]
    ring
  have hright : reflectionDOZZ γ μ α = -B ^ p * Gorig := by
    simp only [reflectionDOZZ, hExp', hTarg', Gorig, B]
    ring
  have hfinal :
      reflectionDOZZ γ μ α =
        -(B ^ N / lFun N) * reflectionDOZZ γ μ (α + 2 / γ) /
          (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) := by
    apply (eq_div_iff hden).2
    rw [hright, hleft]
    calc
      (-B ^ p * Gorig) * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p)) =
          B ^ p * (-Gorig * (lFun (-N) * lFun (1 + N - p) * lFun (1 + p))) := by ring
      _ = B ^ p * (Gshift / lFun N) := by rw [hGammaCoeff]
      _ = -(B ^ N / lFun N) * (-B ^ (p - N) * Gshift) := by
        rw [hpow]
        field_simp [hLN]
  have hLarg2' : 2 + N - (1 + N - p) = 1 + p := by ring
  simpa [N, hNcast, hLarg1, hLarg2', B, Complex.ofReal_mul] using hfinal

end DOZZ.Proofs
