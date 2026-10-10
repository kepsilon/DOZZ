/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.SeriesRecurrence

/-! Parameter-dependent terms of the ordinary Gauss series. -/

@[expose] public section

open Nat Polynomial

namespace DOZZ.Proofs

/-- The `n`th ordinary Gauss series term, packaged as a function of the three parameters. -/
noncomputable def gaussParameterSeriesTerm
    (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n

theorem gaussParameterSeriesTerm_sum (a b c z : ℂ) :
    ordinaryHypergeometric a b c z =
      ∑' n : ℕ, gaussParameterSeriesTerm (a, b, c) z n := by
  rw [ordinaryHypergeometric_eq_tsum]
  simp [gaussParameterSeriesTerm, smul_eq_mul, mul_assoc]

/-- The parameter series term is holomorphic wherever its denominator Pochhammer factor is
nonzero. -/
theorem gaussParameterSeriesTerm_differentiableOn
    {U : Set (ℂ × ℂ × ℂ)} (hU : ∀ p ∈ U, ∀ k : ℕ, p.2.2 ≠ -(k : ℂ))
    (z : ℂ) (n : ℕ) :
    DifferentiableOn ℂ (fun p => gaussParameterSeriesTerm p z n) U := by
  have hA : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.1) U := by
    fun_prop
  have hB : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.1) U := by
    fun_prop
  have hC : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (ascPochhammer ℂ n).eval p.2.2) U := by
    fun_prop
  have hCne : ∀ p ∈ U, (ascPochhammer ℂ n).eval p.2.2 ≠ 0 := by
    intro p hp
    exact ordinaryHypergeometric_pochhammer_denominator_ne_zero n (hU p hp)
  have hCinv := hC.inv hCne
  have hcoeff : DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) U := by
    change DifferentiableOn ℂ
      (fun p : ℂ × ℂ × ℂ => (n !⁻¹ : ℂ) *
        (ascPochhammer ℂ n).eval p.1 * (ascPochhammer ℂ n).eval p.2.1 *
          ((ascPochhammer ℂ n).eval p.2.2)⁻¹) U
    exact (((differentiableOn_const _).mul hA).mul hB).mul hCinv
  change DifferentiableOn ℂ
    (fun p : ℂ × ℂ × ℂ =>
      ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n) U
  exact hcoeff.mul_const _

/-- Successive parameterized terms obey the pointwise Gauss coefficient recurrence. -/
theorem gaussParameterSeriesTerm_recurrence (p : ℂ × ℂ × ℂ) (z : ℂ) (n : ℕ)
    (hc : ∀ k : ℕ, p.2.2 ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) * gaussParameterSeriesTerm p z (n + 1) =
      ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
        gaussParameterSeriesTerm p z n := by
  rw [gaussParameterSeriesTerm, gaussParameterSeriesTerm, pow_succ]
  have hcoeff := ordinaryHypergeometricCoefficient_gauss_recurrence
    p.1 p.2.1 p.2.2 n hc
  calc
    ((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
        (ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 (n + 1) * (z ^ n * z))
        = (((n + 1 : ℂ) * ((n : ℂ) + p.2.2)) *
            ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 (n + 1)) * z ^ n * z := by ring
    _ = (((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) *
          ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n) * z ^ n * z := by
      rw [hcoeff]
    _ = ((n : ℂ) + p.1) * ((n : ℂ) + p.2.1) * z *
          (ordinaryHypergeometricCoefficient p.1 p.2.1 p.2.2 n * z ^ n) := by ring

end DOZZ.Proofs
