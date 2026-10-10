/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTestIntegrationByParts
public import DOZZ.GMC.FiniteGaussianProduct
public import DOZZ.GMC.FiniteGaussianInterpolationIdentity

/-! Smooth-test scores on the independent Gaussian Kahane interpolation path. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- The interpolated field as a linear function of the two concatenated Gaussian blocks. -/
noncomputable def kahaneSumVectorField {ι : Type*}
    (t : ℝ) (z : Sum ι ι → ℝ) : ι → ℝ := fun i =>
  Real.sqrt t * z (Sum.inl i) + Real.sqrt (1 - t) * z (Sum.inr i)

/-- The score of one Wick weight times `F'` of the interpolated chaos mass. -/
noncomputable def kahaneSumVectorScore {ι : Type*} [Fintype ι]
    (a v : ι → ℝ) (γ t : ℝ) (F' : ℝ → ℝ)
    (z : Sum ι ι → ℝ) (i : ι) : ℝ :=
  finiteChaosVectorTestScore a v γ F' (kahaneSumVectorField t z) i

/-- The field-coordinate derivative of the score in the interpolated vector. -/
noncomputable def kahaneSumVectorFieldScoreDerivative {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ t : ℝ) (F' F'' : ℝ → ℝ)
    (z : Sum ι ι → ℝ) (i j : ι) : ℝ :=
  finiteChaosVectorTestScoreDerivative a v γ F' F''
    (kahaneSumVectorField t z) i j

/-- The score derivative with respect to one coordinate of the concatenated Gaussian vector. -/
noncomputable def kahaneSumVectorScoreDerivative {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ t : ℝ) (F' F'' : ℝ → ℝ)
    (z : Sum ι ι → ℝ) (i : ι) (k : Sum ι ι) : ℝ :=
  match k with
  | Sum.inl j => Real.sqrt t * kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j
  | Sum.inr j => Real.sqrt (1 - t) * kahaneSumVectorFieldScoreDerivative a v γ t F' F'' z i j

/-- Directional differentiation of a smooth Wick score along the concatenated Gaussian blocks. -/
theorem kahaneSumVectorScore_directional_hasDerivAt
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a v : ι → ℝ) (γ t : ℝ) (F' F'' : ℝ → ℝ)
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (z d : Sum ι ι → ℝ) (i : ι) (s : ℝ) :
    HasDerivAt (fun r => kahaneSumVectorScore a v γ t F'
      (fun k => z k + r * d k) i)
      (∑ k, d k * kahaneSumVectorScoreDerivative a v γ t F' F''
        (fun k => z k + s * d k) i k) s := by
  classical
  let x : ι → ℝ := kahaneSumVectorField t z
  let d' : ι → ℝ := fun j =>
    Real.sqrt t * d (Sum.inl j) + Real.sqrt (1 - t) * d (Sum.inr j)
  have hpath : (fun r => kahaneSumVectorField t (fun k => z k + r * d k)) =
      fun r j => x j + r * d' j := by
    funext r j
    simp [x, d', kahaneSumVectorField]
    ring
  have hpath_at (r : ℝ) : kahaneSumVectorField t (fun k => z k + r * d k) =
      fun j => x j + r * d' j := by
    exact congrFun hpath r
  have hbase := finiteChaosVectorTestWeight_directional_hasDerivAt
    a v γ F' F'' hF' x d' i s
  have hsum : (∑ k, d k * kahaneSumVectorScoreDerivative a v γ t F' F''
      (fun k => z k + s * d k) i k) =
      ∑ j, d' j * finiteChaosVectorTestScoreDerivative a v γ F' F''
        (kahaneSumVectorField t (fun k => z k + s * d k)) i j := by
    rw [Fintype.sum_sum_type]
    simp only [kahaneSumVectorScoreDerivative, kahaneSumVectorFieldScoreDerivative]
    simp_rw [d']
    calc
      _ = (∑ j, d (Sum.inl j) * (Real.sqrt t *
            finiteChaosVectorTestScoreDerivative a v γ F' F''
              (kahaneSumVectorField t (fun k => z k + s * d k)) i j)) +
          ∑ j, d (Sum.inr j) * (Real.sqrt (1 - t) *
            finiteChaosVectorTestScoreDerivative a v γ F' F''
              (kahaneSumVectorField t (fun k => z k + s * d k)) i j) := rfl
      _ = ∑ j, (Real.sqrt t * d (Sum.inl j) +
          Real.sqrt (1 - t) * d (Sum.inr j)) *
            finiteChaosVectorTestScoreDerivative a v γ F' F''
              (kahaneSumVectorField t (fun k => z k + s * d k)) i j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = _ := rfl
  have hbase' : HasDerivAt
      (fun r => finiteChaosVectorTestScore a v γ F'
        (fun j => x j + r * d' j) i)
      (∑ j, d' j * finiteChaosVectorTestScoreDerivative a v γ F' F''
        (fun j => x j + s * d' j) i j) s := by
    simpa [finiteChaosVectorTestScore, finiteChaosVectorTestScoreDerivative] using hbase
  convert hbase' using 1
  · funext r
    change finiteChaosVectorTestScore a v γ F'
      (kahaneSumVectorField t (fun k => z k + r * d k)) i =
      finiteChaosVectorTestScore a v γ F' (fun j => x j + r * d' j) i
    exact congrArg (fun y => finiteChaosVectorTestScore a v γ F' y i) (hpath_at r)
  · calc
      _ = ∑ j, d' j * finiteChaosVectorTestScoreDerivative a v γ F' F''
          (kahaneSumVectorField t (fun k => z k + s * d k)) i j := hsum
      _ = _ := by
          apply Finset.sum_congr rfl
          intro j hj
          congr 2
          exact hpath_at s

end DOZZ.Proofs
