/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosInterpolationCalculus
public import DOZZ.GMC.FiniteGaussianIntegrationByPartsGrowth

/-! Gaussian integration by parts for a Wick weight times the derivative of a scalar chaos test. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- The field derivative of one Wick weight times a scalar test derivative. -/
noncomputable def finiteChaosVectorTestScore
    {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (γ : ℝ) (F' : ℝ → ℝ)
    (x : ι → ℝ) (i : ι) : ℝ :=
  finiteChaosVectorWeight a v γ x i * F' (finiteChaosVectorMass a v γ x)

/-- The coordinate derivative of `finiteChaosVectorTestScore`. -/
noncomputable def finiteChaosVectorTestScoreDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ : ℝ) (F' F'' : ℝ → ℝ)
    (x : ι → ℝ) (i j : ι) : ℝ :=
  γ * (if i = j then
      finiteChaosVectorWeight a v γ x i * F' (finiteChaosVectorMass a v γ x) else 0) +
    γ * finiteChaosVectorWeight a v γ x i * finiteChaosVectorWeight a v γ x j *
      F'' (finiteChaosVectorMass a v γ x)

/-- Gaussian integration by parts for a Wick weight times `F'` of the full chaos mass. The
exponential envelopes make every integral finite, including when the Gaussian covariance is
singular. The directional derivative is the diagonal-plus-mixed Hessian term used in Kahane's
interpolation formula. -/
theorem finiteChaosVectorTestScore_gaussian_integration_by_parts
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (i : ι)
    (a v c : ι → ℝ) (hc : ∀ j, 0 ≤ c j)
    (γ M : ℝ) (hM : 0 ≤ M)
    (F' F'' : ℝ → ℝ)
    (hFMeas : Measurable F') (hFDerivMeas : Measurable F'')
    (hF' : ∀ z, HasDerivAt F' (F'' z) z)
    (hGbound : ∀ z, ‖finiteChaosVectorTestScore a v γ F' z i‖ ≤
      M * Real.exp (∑ j, c j * |z j|))
    (hDbound : ∀ z j, ‖finiteChaosVectorTestScoreDerivative a v γ F' F'' z i j‖ ≤
      M * Real.exp (∑ j, c j * |z j|)) :
    ∫ ω, Z ω i * finiteChaosVectorTestScore a v γ F' (Z ω) i ∂P =
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) *
        ∫ ω, finiteChaosVectorTestScoreDerivative a v γ F' F'' (Z ω) i j ∂P := by
  classical
  let G : (ι → ℝ) → ℝ := fun x => finiteChaosVectorTestScore a v γ F' x i
  let D : (ι → ℝ) → ι → ℝ := fun x j =>
    finiteChaosVectorTestScoreDerivative a v γ F' F'' x i j
  have hGmeas : Measurable G := by
    dsimp [G, finiteChaosVectorTestScore]
    fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight]
  have hDmeas : ∀ j, Measurable (fun x => D x j) := by
    intro j
    by_cases hij : i = j
    · simp [D, finiteChaosVectorTestScoreDerivative, hij]
      fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight]
    · simp [D, finiteChaosVectorTestScoreDerivative, hij]
      fun_prop [finiteChaosVectorMass, finiteChaosVectorWeight]
  have hGdir : ∀ (x d : ι → ℝ) t,
      HasDerivAt (fun s => G (fun j => x j + s * d j))
        (∑ j, d j * D (fun j => x j + t * d j) j) t := by
    intro x d t
    simpa [G, D, finiteChaosVectorTestScore, finiteChaosVectorTestScoreDerivative] using
      finiteChaosVectorTestWeight_directional_hasDerivAt
        a v γ F' F'' hF' x d i t
  have hGbound' : ∀ z, ‖G z‖ ≤ M * Real.exp (∑ j, c j * |z j|) := by
    simpa [G] using hGbound
  have hDbound' : ∀ z j, ‖D z j‖ ≤ M * Real.exp (∑ j, c j * |z j|) := by
    simpa [D] using hDbound
  simpa [G, D] using
    finite_gaussian_integration_by_parts_of_absExp_bound P Z hZ i G D hGmeas hDmeas
      c hc M hM hGbound' hDbound' hGdir


end DOZZ.Proofs
