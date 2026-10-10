/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Algebraic cancellation in the finite Gaussian interpolation derivative. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Once the two coordinatewise Gaussian integration-by-parts identities are applied to the
interpolation derivative, the diagonal Hessian term cancels the derivative of the Wick variance.
`hXibp` and `hYibp` are the multivariate IBP outputs; `hHessian` is the chain-rule Hessian of a
scalar test of the Wick chaos mass. -/
theorem kahaneInterpolation_diagonal_cancellation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ t : ℝ) (covX covY : ι → ι → ℝ)
    (A B : ι → ℝ) (H K : ι → ι → ℝ) (D : ι → ℝ)
    (ht : 0 < t) (ht1 : t < 1)
    (hXibp : ∀ i, A i = Real.sqrt t * ∑ j, covX i j * H i j)
    (hYibp : ∀ i, B i = Real.sqrt (1 - t) * ∑ j, covY i j * H i j)
    (hHessian : ∀ i j, H i j = γ ^ 2 * K i j +
      if i = j then γ ^ 2 * D i else 0) :
    (∑ i, A i) / (2 * Real.sqrt t) -
        (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
        γ ^ 2 / 2 * ∑ i, (covX i i - covY i i) * D i =
      γ ^ 2 / 2 * ∑ i, ∑ j, (covX i j - covY i j) * K i j := by
  classical
  have hsqrtT : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hsqrtOne : Real.sqrt (1 - t) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hX : (∑ i, A i) / (2 * Real.sqrt t) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, covX i j * H i j := by
    rw [show (∑ i, A i) = ∑ i, Real.sqrt t * ∑ j, covX i j * H i j by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hXibp i]]
    rw [show (∑ i, Real.sqrt t * ∑ j, covX i j * H i j) =
      Real.sqrt t * ∑ i, ∑ j, covX i j * H i j by rw [Finset.mul_sum]]
    field_simp
  have hY : (∑ i, B i) / (2 * Real.sqrt (1 - t)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, covY i j * H i j := by
    rw [show (∑ i, B i) = ∑ i, Real.sqrt (1 - t) * ∑ j, covY i j * H i j by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hYibp i]]
    rw [show (∑ i, Real.sqrt (1 - t) * ∑ j, covY i j * H i j) =
      Real.sqrt (1 - t) * ∑ i, ∑ j, covY i j * H i j by rw [Finset.mul_sum]]
    field_simp
  have hdiag : ∑ i, ∑ j, (covX i j - covY i j) *
      (if i = j then D i else 0) =
      ∑ i, (covX i i - covY i i) * D i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  calc
    (∑ i, A i) / (2 * Real.sqrt t) -
        (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
        γ ^ 2 / 2 * ∑ i, (covX i i - covY i i) * D i
      = γ ^ 2 / 2 * ∑ i, ∑ j,
          (covX i j - covY i j) * K i j := by
            rw [hX, hY]
            have hsplit : (∑ i, ∑ j, covX i j * H i j) -
                (∑ i, ∑ j, covY i j * H i j) =
                ∑ i, ∑ j, (covX i j - covY i j) * H i j := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i hi
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j hj
              ring
            have hHsum : ∑ i, ∑ j, (covX i j - covY i j) * H i j =
                γ ^ 2 * ∑ i, ∑ j, (covX i j - covY i j) * K i j +
                  γ ^ 2 * ∑ i, ∑ j, (covX i j - covY i j) *
                    (if i = j then D i else 0) := by
              calc
                _ = ∑ i, ∑ j, (γ ^ 2 * ((covX i j - covY i j) * K i j) +
                    γ ^ 2 * ((covX i j - covY i j) *
                      (if i = j then D i else 0))) := by
                      apply Finset.sum_congr rfl
                      intro i hi
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [hHessian i j]
                      by_cases hij : i = j
                      · subst j
                        simp
                        ring
                      · simp [hij]
                        ring
                _ = _ := by
                      simp only [Finset.sum_add_distrib]
                      simp_rw [← Finset.mul_sum]
            rw [show (1 / 2 : ℝ) * (∑ i, ∑ j, covX i j * H i j) -
                (1 / 2 : ℝ) * (∑ i, ∑ j, covY i j * H i j) =
                (1 / 2 : ℝ) * ((∑ i, ∑ j, covX i j * H i j) -
                  (∑ i, ∑ j, covY i j * H i j)) by ring,
              hsplit, hHsum, hdiag]
            ring

/-- Entrywise covariance order and nonnegative chaos Hessian make the interpolation derivative
nonpositive when the path runs from `Y` at zero to `X` at one. -/
theorem kahaneInterpolation_derivative_nonpos_of_covariance_order
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ t : ℝ) (covX covY : ι → ι → ℝ)
    (A B : ι → ℝ) (H K : ι → ι → ℝ) (D : ι → ℝ)
    (ht : 0 < t) (ht1 : t < 1)
    (hcov : ∀ i j, covX i j ≤ covY i j)
    (hK : ∀ i j, 0 ≤ K i j)
    (hXibp : ∀ i, A i = Real.sqrt t * ∑ j, covX i j * H i j)
    (hYibp : ∀ i, B i = Real.sqrt (1 - t) * ∑ j, covY i j * H i j)
    (hHessian : ∀ i j, H i j = γ ^ 2 * K i j +
      if i = j then γ ^ 2 * D i else 0) :
    (∑ i, A i) / (2 * Real.sqrt t) -
        (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
        γ ^ 2 / 2 * ∑ i, (covX i i - covY i i) * D i ≤ 0 := by
  rw [kahaneInterpolation_diagonal_cancellation γ t covX covY A B H K D ht ht1
    hXibp hYibp hHessian]
  have hsum : ∑ i, ∑ j, (covX i j - covY i j) * K i j ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hcov i j)) (hK i j)
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ γ ^ 2 / 2) hsum

/-- A differentiable interpolation with nonpositive derivative on the interior has the Kahane
endpoint order. This isolates the one-dimensional real-analysis step from the Gaussian IBP proof. -/
theorem kahaneInterpolation_endpoint_le_of_derivative
    (φ d : ℝ → ℝ)
    (hcont : ContinuousOn φ (Set.Icc 0 1))
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt φ (d t) t)
    (hsign : ∀ t ∈ Set.Ioo (0 : ℝ) 1, d t ≤ 0) :
    φ 1 ≤ φ 0 := by
  have hanti : AntitoneOn φ (Set.Icc 0 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1) hcont
      (fun t ht => (hderiv t (by simpa using ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(hderiv t (by simpa using ht)).deriv]
        exact hsign t (by simpa using ht))
  exact hanti (by simp) (by simp) (by norm_num)

end DOZZ.Proofs
