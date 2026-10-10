/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosGaussianLaplaceFintype

/-! Laplace comparison for several disjoint finite-chaos blocks. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- A nonnegative linear combination of the masses of disjoint coordinate blocks is a single
finite-chaos mass with the block parameter absorbed into each coordinate weight. -/
theorem finiteChaos_blockMass_weighted_sum
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (block : ι → κ)
    (a : ι → ℝ) (t : κ → ℝ) (γ : ℝ) (ω : Ω) :
    (∑ k, t k * DOZZ.finiteChaosMass P Z
      (fun i => if block i = k then a i else 0) γ ω) =
      DOZZ.finiteChaosMass P Z (fun i => a i * t (block i)) γ ω := by
  classical
  let W : ι → ℝ := fun i => Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i))
  change (∑ k, t k * ∑ i, (if block i = k then a i else 0) * W i) =
    ∑ i, (a i * t (block i)) * W i
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have hinner :
      (∑ k, t k * (if block i = k then a i else 0)) = t (block i) * a i := by
    simp [mul_ite, mul_comm]
  calc
    (∑ k, t k * ((if block i = k then a i else 0) * W i)) =
        ∑ k, (t k * (if block i = k then a i else 0)) * W i := by
          congr 1
          funext k
          ring
    _ = (∑ k, t k * (if block i = k then a i else 0)) * W i := by
      rw [Finset.sum_mul]
    _ = (a i * t (block i)) * W i := by rw [hinner]; ring

/-- Entrywise covariance order compares the Laplace transform of every nonnegative weighted sum
of finitely many block chaoses. This reduces several blocks to one finite-chaos mass. -/
theorem kahane_finite_multi_block_laplace_lintegral
    {ΩX ΩY ι κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (block : ι → κ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (t : κ → ℝ) (ht : ∀ k, 0 ≤ t k) (γ : ℝ)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
      (-∑ k, t k * DOZZ.finiteChaosMass PX X
        (fun i => if block i = k then a i else 0) γ ω)) ∂PX ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp
        (-∑ k, t k * DOZZ.finiteChaosMass PY Y
          (fun i => if block i = k then a i else 0) γ ω)) ∂PY := by
  let a' : ι → ℝ := fun i => a i * t (block i)
  have ha' : ∀ i, 0 ≤ a' i := fun i => mul_nonneg (ha i) (ht (block i))
  have hsingle := kahane_finite_laplace_lintegral_fintype PX PY X Y hX hY a' ha' γ 1
    (by norm_num) hcov
  have hmassX (ω : ΩX) :
      (∑ k, t k * DOZZ.finiteChaosMass PX X
        (fun i => if block i = k then a i else 0) γ ω) =
        DOZZ.finiteChaosMass PX X a' γ ω :=
    finiteChaos_blockMass_weighted_sum PX X block a t γ ω
  have hmassY (ω : ΩY) :
      (∑ k, t k * DOZZ.finiteChaosMass PY Y
        (fun i => if block i = k then a i else 0) γ ω) =
        DOZZ.finiteChaosMass PY Y a' γ ω :=
    finiteChaos_blockMass_weighted_sum PY Y block a t γ ω
  simpa [hmassX, hmassY, a'] using hsingle


end DOZZ.Proofs
