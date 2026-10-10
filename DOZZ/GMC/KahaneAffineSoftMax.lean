/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneWeightedVariance
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Smooth convex approximation of finite maxima of affine functions. -/

@[expose] public section

open scoped BigOperators

namespace DOZZ.Proofs

/-- The exponential sum of a finite family of affine functions. -/
noncomputable def affineSoftMaxSum {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) : ℝ := ∑ i, Real.exp (β * (a i * x + b i))

/-- The first weighted affine-slope sum. -/
noncomputable def affineSoftMaxSlopeSum {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) : ℝ := ∑ i, a i * Real.exp (β * (a i * x + b i))

/-- The second weighted affine-slope sum. -/
noncomputable def affineSoftMaxSlopeSquareSum {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) : ℝ := ∑ i, a i ^ 2 * Real.exp (β * (a i * x + b i))

/-- A smooth maximum of finitely many affine functions. -/
noncomputable def affineSoftMax {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) : ℝ := Real.log (affineSoftMaxSum a b β x) / β

/-- The derivative of the smooth affine maximum is the weighted mean slope. -/
noncomputable def affineSoftMaxDeriv {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) : ℝ := affineSoftMaxSlopeSum a b β x / affineSoftMaxSum a b β x

/-- The second derivative is the weighted variance of the affine slopes. -/
noncomputable def affineSoftMaxSecondDeriv {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) : ℝ := β *
      ((affineSoftMaxSlopeSquareSum a b β x) * affineSoftMaxSum a b β x -
        (affineSoftMaxSlopeSum a b β x) ^ 2) / (affineSoftMaxSum a b β x) ^ 2

theorem affineSoftMaxSum_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (β x : ℝ) : 0 < affineSoftMaxSum a b β x := by
  classical
  exact Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty

theorem affineSoftMaxSum_hasDerivAt {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) :
    HasDerivAt (affineSoftMaxSum a b β) (β * affineSoftMaxSlopeSum a b β x) x := by
  classical
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    ((((hasDerivAt_id x).const_mul (a i)).add_const (b i)).const_mul β).exp)
  convert h using 1
  · funext y
    rfl
  · dsimp [affineSoftMaxSlopeSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem affineSoftMaxSlopeSum_hasDerivAt {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (β x : ℝ) :
    HasDerivAt (affineSoftMaxSlopeSum a b β)
      (β * affineSoftMaxSlopeSquareSum a b β x) x := by
  classical
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (((((hasDerivAt_id x).const_mul (a i)).add_const (b i)).const_mul β).exp).const_mul (a i))
  convert h using 1
  · funext y
    rfl
  · dsimp [affineSoftMaxSlopeSquareSum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem affineSoftMax_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (β x : ℝ) (hβ : β ≠ 0) :
    HasDerivAt (affineSoftMax a b β) (affineSoftMaxDeriv a b β x) x := by
  have hS := affineSoftMaxSum_hasDerivAt a b β x
  have hpos := affineSoftMaxSum_pos a b β x
  convert (hS.log hpos.ne').div_const β using 1
  · funext y
    rfl
  · dsimp [affineSoftMaxDeriv]
    field_simp

theorem affineSoftMaxDeriv_hasDerivAt {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (β x : ℝ) :
    HasDerivAt (affineSoftMaxDeriv a b β) (affineSoftMaxSecondDeriv a b β x) x := by
  have hS := affineSoftMaxSum_hasDerivAt a b β x
  have hSlope := affineSoftMaxSlopeSum_hasDerivAt a b β x
  have hpos := affineSoftMaxSum_pos a b β x
  convert hSlope.div hS hpos.ne' using 1
  · funext y
    rfl
  · dsimp [affineSoftMaxSecondDeriv]
    ring

/-- Smooth affine maxima have globally bounded derivatives and nonnegative second derivative. -/
theorem affineSoftMax_derivative_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ B₁ B₂ : ℝ, (∀ x, ‖affineSoftMaxDeriv a b β x‖ ≤ B₁) ∧
      (∀ x, ‖affineSoftMaxSecondDeriv a b β x‖ ≤ B₂) ∧
        ∀ x, 0 ≤ affineSoftMaxSecondDeriv a b β x := by
  classical
  let B : ℝ := 1 + ∑ i, |a i|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have ha (i : ι) : |a i| ≤ B := by
    have h := Finset.single_le_sum (f := fun i => |a i|)
      (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
    dsimp [B]
    linarith
  have hb (x : ℝ) := weighted_variance_bounds a
    (fun i => Real.exp (β * (a i * x + b i)))
    (fun i => Real.exp_nonneg _) (affineSoftMaxSum_pos a b β x) B hB ha
  have hsecond (x : ℝ) : 0 ≤ affineSoftMaxSecondDeriv a b β x := by
    dsimp [affineSoftMaxSecondDeriv]
    rw [mul_div_assoc]
    exact mul_nonneg hβ (hb x).2.1
  refine ⟨B, β * B ^ 2, ?_, ?_, hsecond⟩
  · intro x
    exact (hb x).1
  · intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (hsecond x)]
    dsimp [affineSoftMaxSecondDeriv]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hb x).2.2 hβ

end DOZZ.Proofs
