/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneConvexOrderClosure

/-! Finite Kahane comparison for arbitrary measurable convex tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Kahane comparison for convex functions of finite-dimensional chaos masses under entrywise
covariance order. See [KRV, §9.2] and [KRV, §12.2]. -/
theorem kahane_finite_convex
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (hcov : ∀ i j,
      gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    (F : ℝ → ℝ) (hF : Measurable F)
    (hconvex : ConvexOn ℝ (Set.Ici 0) F)
    (hIY : Integrable (fun ω => F (finiteChaosMass PY Y a γ ω)) PY) :
    Integrable (fun ω => F (finiteChaosMass PX X a γ ω)) PX ∧
      ∫ ω, F (finiteChaosMass PX X a γ ω) ∂PX ≤
        ∫ ω, F (finiteChaosMass PY Y a γ ω) ∂PY := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  by_cases hapos : ∃ i, 0 < a i
  · have hmassPos (P : Measure ΩX) (Z : ΩX → ι → ℝ) (ω : ΩX) :
        0 < finiteChaosMass P Z a γ ω := by
      obtain ⟨i, hai⟩ := hapos
      have hterm : 0 < a i * Real.exp (γ * Z ω i - γ ^ 2 / 2 *
          gaussianVariance P (fun ω => Z ω i)) := mul_pos hai (Real.exp_pos _)
      unfold finiteChaosMass
      exact hterm.trans_le (Finset.single_le_sum
        (f := fun j => a j * Real.exp (γ * Z ω j - γ ^ 2 / 2 *
          gaussianVariance P (fun ω => Z ω j)))
        (fun j _ => mul_nonneg (ha j) (Real.exp_nonneg _)) (Finset.mem_univ i))
    have hmassPosY (ω : ΩY) : 0 < finiteChaosMass PY Y a γ ω := by
      obtain ⟨i, hai⟩ := hapos
      have hterm : 0 < a i * Real.exp (γ * Y ω i - γ ^ 2 / 2 *
          gaussianVariance PY (fun ω => Y ω i)) := mul_pos hai (Real.exp_pos _)
      unfold finiteChaosMass
      exact hterm.trans_le (Finset.single_le_sum
        (f := fun j => a j * Real.exp (γ * Y ω j - γ ^ 2 / 2 *
          gaussianVariance PY (fun ω => Y ω j)))
        (fun j _ => mul_nonneg (ha j) (Real.exp_nonneg _)) (Finset.mem_univ i))
    have hmX := finiteChaosMass_integral PX X hX a γ
    have hmY := finiteChaosMass_integral PY Y hY a γ
    exact convex_comparison_of_affine_max_order PX PY
      (finiteChaosMass PX X a γ) (finiteChaosMass PY Y a γ) hmX.1 hmY.1
      (ae_of_all _ (hmassPos PX X)) (ae_of_all _ hmassPosY) (hmX.2.trans hmY.2.symm)
      (fun n c d => kahane_finite_affine_max PX PY X Y hX hY a ha γ c d hcov)
      F hF hconvex hIY
  · have hazero (i : ι) : a i = 0 := le_antisymm (le_of_not_gt
      (fun hi => hapos ⟨i, hi⟩)) (ha i)
    constructor
    · simp [finiteChaosMass, hazero]
    · simp [finiteChaosMass, hazero]


end DOZZ.Proofs
