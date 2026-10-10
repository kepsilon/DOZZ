/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosLaplaceLinearChain

/-! Scaled covariance integration by parts for one block of a finite interpolation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

/-- The shifted Laplace-score IBP after scaling one standard-Gaussian block by a positive
interpolation coefficient. The covariance on the right is that of the unscaled field, with the
single expected factor of `scale` left outside. -/
theorem finiteChaos_laplace_score_scaled_shifted_standardGaussian_ibp
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a v c : Fin (n + 1) → ℝ) (γ s scale : ℝ)
    (ha : ∀ j, 0 ≤ a j) (hs : 0 ≤ s) (hscale : 0 < scale)
    (i : Fin (n + 1)) :
    let V : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x j =>
      scale * (∑ k, A j k * x k) + c j
    let W : (Fin (n + 1) → ℝ) → ℝ := fun x =>
      finiteChaosVectorWeight a v γ (V x) i *
        (-s * Real.exp (-s * finiteChaosVectorMass a v γ (V x)))
    let D : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ := fun x p q =>
      γ * (if p = q then
          finiteChaosVectorWeight a v γ (V x) p *
            (-s * Real.exp (-s * finiteChaosVectorMass a v γ (V x))) else 0) +
        γ * finiteChaosVectorWeight a v γ (V x) p *
          finiteChaosVectorWeight a v γ (V x) q *
            (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ (V x)))
    ∫ x, (∑ k, A i k * x k) * W x
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) =
      scale * ∑ j, (∑ k, A i k * A j k) *
        ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  let V : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x j =>
    scale * (∑ k, A j k * x k) + c j
  let W : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    finiteChaosVectorWeight a v γ (V x) i *
      (-s * Real.exp (-s * finiteChaosVectorMass a v γ (V x)))
  let D : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ := fun x p q =>
    γ * (if p = q then
        finiteChaosVectorWeight a v γ (V x) p *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ (V x))) else 0) +
        γ * finiteChaosVectorWeight a v γ (V x) p *
          finiteChaosVectorWeight a v γ (V x) q *
            (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ (V x)))
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := fun p q => scale * A p q
  let Wraw : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    finiteChaosVectorWeight a v γ (fun j => (∑ k, B j k * x k) + c j) i *
      (-s * Real.exp (-s * finiteChaosVectorMass a v γ
        (fun j => (∑ k, B j k * x k) + c j)))
  let Draw : (Fin (n + 1) → ℝ) → Fin (n + 1) → Fin (n + 1) → ℝ := fun x p q =>
    γ * (if p = q then
        finiteChaosVectorWeight a v γ
          (fun j => (∑ k, B j k * x k) + c j) p *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ
            (fun j => (∑ k, B j k * x k) + c j))) else 0) +
      γ * finiteChaosVectorWeight a v γ
          (fun j => (∑ k, B j k * x k) + c j) p *
        finiteChaosVectorWeight a v γ
          (fun j => (∑ k, B j k * x k) + c j) q *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ
          (fun j => (∑ k, B j k * x k) + c j)))
  have hbase := finiteChaos_laplace_score_shifted_standardGaussian_ibp
    B c a v γ s ha hs i
  have hfield (x : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
      (∑ k, B j k * x k) + c j = V x j := by
    change (∑ k, (scale * A j k) * x k) + c j =
      scale * (∑ k, A j k * x k) + c j
    congr 1
    calc
      (∑ k, (scale * A j k) * x k) =
          ∑ k, scale * (A j k * x k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = scale * (∑ k, A j k * x k) := by
            exact (Finset.mul_sum Finset.univ (fun k => A j k * x k) scale).symm
  have hscore (x : Fin (n + 1) → ℝ) : Wraw x = W x := by
    simp [Wraw, W, hfield]
  have hderiv (x : Fin (n + 1) → ℝ) (p q : Fin (n + 1)) :
      Draw x p q = D x p q := by
    simp [Draw, D, hfield]
  have hcov (j : Fin (n + 1)) :
      (∑ k, B i k * B j k) = scale ^ 2 * ∑ k, A i k * A j k := by
    calc
      ∑ k, B i k * B j k =
          ∑ k, scale ^ 2 * (A i k * A j k) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [B]
            ring
      _ = scale ^ 2 * ∑ k, A i k * A j k := by rw [Finset.mul_sum]
  have hbase0 :
      (∫ x, (∑ k, B i k * x k) * Wraw x
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        ∑ j, (∑ k, B i k * B j k) *
          ∫ x, Draw x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
    simpa [Wraw, Draw] using hbase
  have hbase' :
      (∫ x, (∑ k, B i k * x k) * W x
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        ∑ j, (∑ k, B i k * B j k) *
          ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
    calc
      (∫ x, (∑ k, B i k * x k) * W x
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        ∫ x, (∑ k, B i k * x k) * Wraw x
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [hscore x]
      _ = ∑ j, (∑ k, B i k * B j k) *
          ∫ x, Draw x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := hbase0
      _ = _ := by
            apply Finset.sum_congr rfl
            intro j hj
            congr 1
            exact integral_congr_ae (ae_of_all _ fun x => hderiv x i j)
  have hleft :
      (∫ x, (∑ k, B i k * x k) * W x
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        scale * (∫ x, (∑ k, A i k * x k) * W x
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    have hlinear (x : Fin (n + 1) → ℝ) :
        (∑ k, B i k * x k) = scale * (∑ k, A i k * x k) := by
      change (∑ k, (scale * A i k) * x k) =
        scale * (∑ k, A i k * x k)
      calc
        (∑ k, (scale * A i k) * x k) =
            ∑ k, scale * (A i k * x k) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = scale * (∑ k, A i k * x k) := by
              exact (Finset.mul_sum Finset.univ (fun k => A i k * x k) scale).symm
    calc
      _ = ∫ x, scale * ((∑ k, A i k * x k) * W x)
          ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [hlinear x]
            ring
      _ = _ := integral_const_mul _ _
  have hright :
      (∑ j, (∑ k, B i k * B j k) *
          ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        scale ^ 2 * (∑ j, (∑ k, A i k * A j k) *
          ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    calc
      (∑ j, (∑ k, B i k * B j k) *
          ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
        ∑ j, scale ^ 2 * ((∑ k, A i k * A j k) *
          ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hcov j]
            ring
      _ = scale ^ 2 * (∑ j, (∑ k, A i k * A j k) *
          ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
            rw [Finset.mul_sum]
  have hscaled := hleft.symm.trans (hbase'.trans hright)
  change (∫ x, (∑ k, A i k * x k) * W x
      ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    scale * ∑ j, (∑ k, A i k * A j k) *
      ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
  apply (mul_left_cancel₀ (ne_of_gt hscale))
  calc
    scale * (∫ x, (∑ k, A i k * x k) * W x
        ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      scale ^ 2 * (∑ j, (∑ k, A i k * A j k) *
        ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) := hscaled
    _ = scale * (scale * ∑ j, (∑ k, A i k * A j k) *
        ∫ x, D x i j ∂(Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)) := by ring

end DOZZ.Proofs
