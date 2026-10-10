/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.LogRegularizationReference

/-! The definition `DOZZ.IsAdmissibleLogRegularization`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Admissible logarithmic regularization on the open chart `U`: a centered Gaussian family in
`(ε, x)`, jointly measurable at each scale, with the mixed logarithmic covariance bound, the
coarse variance and same-center bounds, the separated off-diagonal limit `log (1/|x-y|) + H x y`
with a continuous regular part, and fixed-coarse-scale limits. -/
structure IsAdmissibleLogRegularization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) : Prop where
  measurableAtScale : ∀ ε, Measurable (fun q : Ω × ℂ => Y q.1 ε q.2)
  openChart : IsOpen U
  densityContinuous : ContinuousOn dens U
  densityPositive : ∀ x ∈ U, 0 < dens x
  cutoffPositive : 0 < ε₀
  gaussian : ∀ (n : ℕ) (q : Fin n → ℝ × ℂ), (∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀) →
    IsCenteredJointlyGaussian P (fun ω i => Y ω (q i).1 (q i).2)
  covarianceBound : ∀ K, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε δ, 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ ε₀ →
      ∀ x ∈ K, ∀ y ∈ K,
        |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y) -
          Real.log (1 / max ‖x - y‖ (max ε δ))| ≤ C
  coarseVarianceBound : ∀ K, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ ε₀ →
      ∀ x ∈ K,
        |gaussianVariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x) - (k : ℝ)| ≤ C
  coarseMixedBound : ∀ K, IsCompact K → K ⊆ U →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ ε₀ →
      ∀ ε, 0 < ε → ε ≤ Real.exp (-(k : ℝ)) →
        ∀ x ∈ K,
          |gaussianCovariance P (fun ω => Y ω (Real.exp (-(k : ℝ))) x)
              (fun ω => Y ω ε x) - (k : ℝ)| ≤ C
  offDiagonalLimit : ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
    ∀ K, IsCompact K → K ⊆ U → ∀ s : ℝ, 0 < s → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε', 0 < ε → ε ≤ min δ ε₀ → 0 < ε' → ε' ≤ min δ ε₀ →
        ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
          |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y) -
            (Real.log (1 / ‖x - y‖) + H x y)| < η
  fixedCoarseLimit : ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ,
    ∀ K, IsCompact K → K ⊆ U → ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ ε₀ → ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ min δ ε₀ →
        ∀ x ∈ K, ∀ y ∈ K,
          |gaussianCovariance P (fun ω => Y ω ε x)
              (fun ω => Y ω (Real.exp (-(k : ℝ))) y) - coarseKernel k x y| < η

end DOZZ
