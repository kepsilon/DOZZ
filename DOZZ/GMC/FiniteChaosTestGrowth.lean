/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTestIntegrationByParts

/-! Exponential growth envelopes for smooth finite-chaos scores. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- Every Wick weight in a finite family has a common absolute-exponential envelope. -/
theorem finiteChaosVectorWeight_absExp_bound
    {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (γ : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z i,
      ‖finiteChaosVectorWeight a v γ z i‖ ≤
        B * Real.exp (|γ| * ∑ j, |z j|) := by
  classical
  let b : ι → ℝ := fun i => |a i| * Real.exp (|γ ^ 2 / 2 * v i|)
  let B : ℝ := 1 + ∑ i, b i
  have hb (i : ι) : 0 ≤ b i := by
    dsimp [b]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hbi (i : ι) : b i ≤ B := by
    have hle : b i ≤ ∑ j, b j := by
      simpa using (Finset.single_le_sum (s := Finset.univ) (f := b)
        (fun j hj => hb j) (Finset.mem_univ i))
    dsimp [B]
    linarith
  refine ⟨B, hB, ?_⟩
  intro z i
  rw [finiteChaosVectorWeight, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  have harg : γ * z i - γ ^ 2 / 2 * v i ≤
      |γ| * ∑ j, |z j| + |γ ^ 2 / 2 * v i| := by
    have hlin : γ * z i ≤ |γ| * |z i| := by
      calc
        γ * z i ≤ |γ * z i| := le_abs_self _
        _ = |γ| * |z i| := abs_mul _ _
    have hcoord : |z i| ≤ ∑ j, |z j| := by
      simpa using (Finset.single_le_sum (s := Finset.univ)
        (f := fun j : ι => |z j|)
        (fun j hj => abs_nonneg (z j)) (Finset.mem_univ i))
    have hcoord' : |γ| * |z i| ≤ |γ| * ∑ j, |z j| :=
      mul_le_mul_of_nonneg_left hcoord (abs_nonneg γ)
    have hconst : -(γ ^ 2 / 2 * v i) ≤ |γ ^ 2 / 2 * v i| := neg_le_abs _
    linarith
  calc
    |a i| * Real.exp (γ * z i - γ ^ 2 / 2 * v i) ≤
        |a i| * Real.exp (|γ| * ∑ j, |z j| + |γ ^ 2 / 2 * v i|) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (abs_nonneg _)
    _ = b i * Real.exp (|γ| * ∑ j, |z j|) := by
      dsimp [b]
      rw [Real.exp_add]
      ring
    _ ≤ B * Real.exp (|γ| * ∑ j, |z j|) :=
      mul_le_mul_of_nonneg_right (hbi i) (Real.exp_nonneg _)

/-- Bounded first and second derivatives give an exponential-linear envelope for the score used
in the Gaussian integration-by-parts formula. -/
theorem finiteChaosVectorTestScore_exp_growth_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (F' F'' : ℝ → ℝ)
    (hF' : ∀ x, ‖F' x‖ ≤ B₁) (hF'' : ∀ x, ‖F'' x‖ ≤ B₂) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z i j,
      ‖finiteChaosVectorTestScore a v γ F' z i‖ ≤
          M * Real.exp (2 * (|γ| * ∑ k, |z k|)) ∧
      ‖finiteChaosVectorTestScoreDerivative a v γ F' F'' z i j‖ ≤
          M * Real.exp (2 * (|γ| * ∑ k, |z k|)) := by
  classical
  obtain ⟨B, hB, hWeight⟩ := finiteChaosVectorWeight_absExp_bound a v γ
  let u : (ι → ℝ) → ℝ := fun z => |γ| * ∑ k, |z k|
  let E : (ι → ℝ) → ℝ := fun z => Real.exp (2 * u z)
  let M : ℝ := B * B₁ + |γ| * (B * B₁ + B ^ 2 * B₂)
  have hu (z : ι → ℝ) : 0 ≤ u z :=
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k hk => abs_nonneg _)
  have hExp (z : ι → ℝ) : Real.exp (u z) ≤ E z := by
    apply Real.exp_le_exp.mpr
    linarith [hu z]
  have hExpSq (z : ι → ℝ) :
      Real.exp (u z) * Real.exp (u z) = E z := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨M, ?_, ?_⟩
  · dsimp [M]
    positivity
  · intro z i j
    constructor
    · rw [finiteChaosVectorTestScore]
      have hw := hWeight z i
      calc
        ‖finiteChaosVectorWeight a v γ z i * F'
            (finiteChaosVectorMass a v γ z)‖ ≤
            ‖finiteChaosVectorWeight a v γ z i‖ * B₁ := by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (hF' _) (norm_nonneg _)
        _ ≤ B * Real.exp (u z) * B₁ := by
              exact mul_le_mul_of_nonneg_right hw hB₁
        _ ≤ B * B₁ * E z := by
              calc
                _ = (B * B₁) * Real.exp (u z) := by ring
                _ ≤ (B * B₁) * E z :=
                  mul_le_mul_of_nonneg_left (hExp z) (mul_nonneg hB hB₁)
        _ ≤ M * E z := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
              dsimp [M]
              exact le_add_of_nonneg_right
                (mul_nonneg (abs_nonneg γ) (by positivity))
    · rw [finiteChaosVectorTestScoreDerivative]
      have hw₁ := hWeight z i
      have hw₂ := hWeight z j
      have hdiag : ‖if i = j then
          finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
          else 0‖ ≤ B * B₁ * E z := by
        have hdiag' : ‖finiteChaosVectorWeight a v γ z i *
            F' (finiteChaosVectorMass a v γ z)‖ ≤ B * B₁ * E z := by
          calc
            _ = ‖finiteChaosVectorWeight a v γ z i‖ *
                ‖F' (finiteChaosVectorMass a v γ z)‖ := norm_mul _ _
            _ ≤ ‖finiteChaosVectorWeight a v γ z i‖ * B₁ :=
              mul_le_mul_of_nonneg_left (hF' _) (norm_nonneg _)
            _ ≤ B * Real.exp (u z) * B₁ :=
              mul_le_mul_of_nonneg_right hw₁ hB₁
            _ ≤ B * B₁ * E z := by
              calc
                _ = (B * B₁) * Real.exp (u z) := by ring
                _ ≤ (B * B₁) * E z :=
                  mul_le_mul_of_nonneg_left (hExp z) (mul_nonneg hB hB₁)
        by_cases hij : i = j
        · rw [ite_eq_left hij]
          exact hdiag'
        · rw [ite_eq_right hij]
          simp only [norm_zero]
          exact mul_nonneg (mul_nonneg hB hB₁) (Real.exp_nonneg _)
      have hprod :
          ‖finiteChaosVectorWeight a v γ z i *
            finiteChaosVectorWeight a v γ z j *
            F'' (finiteChaosVectorMass a v γ z)‖ ≤ B ^ 2 * B₂ * E z := by
        calc
          _ = ‖finiteChaosVectorWeight a v γ z i‖ *
                ‖finiteChaosVectorWeight a v γ z j‖ *
                ‖F'' (finiteChaosVectorMass a v γ z)‖ := by
              rw [norm_mul, norm_mul]
          _ ≤ (B * Real.exp (u z)) * (B * Real.exp (u z)) * B₂ := by
            apply mul_le_mul
              (mul_le_mul hw₁ hw₂ (norm_nonneg _) (by positivity))
              (hF'' _)
              (norm_nonneg _)
              (by positivity)
          _ = B ^ 2 * B₂ * E z := by
            calc
              _ = B ^ 2 * B₂ * (Real.exp (u z) * Real.exp (u z)) := by ring
              _ = B ^ 2 * B₂ * E z := by rw [hExpSq]
      have hsum :
          ‖γ * (if i = j then
              finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
              else 0) +
            γ * finiteChaosVectorWeight a v γ z i *
              finiteChaosVectorWeight a v γ z j *
                F'' (finiteChaosVectorMass a v γ z)‖ ≤
          |γ| * (B * B₁ + B ^ 2 * B₂) * E z := by
        have hnormDiag :
            ‖γ * (if i = j then
              finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
              else 0)‖ = |γ| * ‖if i = j then
              finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
              else 0‖ := by
          rw [norm_mul, Real.norm_eq_abs]
        have hnormProd :
            ‖γ * finiteChaosVectorWeight a v γ z i *
              finiteChaosVectorWeight a v γ z j *
              F'' (finiteChaosVectorMass a v γ z)‖ =
            |γ| * ‖finiteChaosVectorWeight a v γ z i *
              finiteChaosVectorWeight a v γ z j *
              F'' (finiteChaosVectorMass a v γ z)‖ := by
          calc
            _ = ‖γ * (finiteChaosVectorWeight a v γ z i *
                finiteChaosVectorWeight a v γ z j *
                F'' (finiteChaosVectorMass a v γ z))‖ := by congr 1; ring
            _ = _ := by rw [norm_mul, Real.norm_eq_abs]
        calc
          _ ≤ ‖γ * (if i = j then
                finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
                else 0)‖ +
              ‖γ * finiteChaosVectorWeight a v γ z i *
                finiteChaosVectorWeight a v γ z j *
                  F'' (finiteChaosVectorMass a v γ z)‖ := norm_add_le _ _
          _ = |γ| * ‖if i = j then
                finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
                else 0‖ +
              |γ| * ‖finiteChaosVectorWeight a v γ z i *
                finiteChaosVectorWeight a v γ z j *
                  F'' (finiteChaosVectorMass a v γ z)‖ := by
                rw [hnormDiag, hnormProd]
          _ ≤ |γ| * (B * B₁ * E z) + |γ| * (B ^ 2 * B₂ * E z) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hdiag (abs_nonneg γ))
              (mul_le_mul_of_nonneg_left hprod (abs_nonneg γ))
          _ = _ := by ring
      calc
        _ = ‖γ * (if i = j then
              finiteChaosVectorWeight a v γ z i * F' (finiteChaosVectorMass a v γ z)
              else 0) +
            γ * finiteChaosVectorWeight a v γ z i *
              finiteChaosVectorWeight a v γ z j *
                F'' (finiteChaosVectorMass a v γ z)‖ := rfl
        _ ≤ |γ| * (B * B₁ + B ^ 2 * B₂) * E z := hsum
        _ ≤ M * E z := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          dsimp [M]
          calc
            |γ| * (B * B₁ + B ^ 2 * B₂) ≤
                |γ| * (B * B₁ + B ^ 2 * B₂) + B * B₁ :=
              le_add_of_nonneg_right (mul_nonneg hB hB₁)
            _ = B * B₁ + |γ| * (B * B₁ + B ^ 2 * B₂) := by ring


end DOZZ.Proofs
