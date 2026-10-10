/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyKernel
public import DOZZ.GMC.FiniteChaosGaussianLaplaceFintype

/-! A two-root finite-barrier tilt for every compatible pair of regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Finite Gaussian coordinates for coarse scales at two roots and the two fine fields. -/
abbrev CompatibleBarrierPairIndex (m : ℕ) :=
  (Fin (m + 1) × Bool) ⊕ Bool

/-- Only active scales are included in the rectangle; lower scales impose no constraint. -/
abbrev CompatibleBarrierPairActiveIndex (k₀ m : ℕ) :=
  {j : Fin (m + 1) × Bool // k₀ ≤ j.1.val}

/-- The family and spatial point represented by each coordinate. -/
noncomputable def compatibleBarrierPairTuple
    (k₀ m : ℕ) (ε δ : ℝ) (x y : ℂ) (b₁ b₂ : Bool)
    (i : CompatibleBarrierPairIndex m) : Bool × ℝ × ℂ :=
  match i with
  | .inl (k, root) =>
      (true, Real.exp (-((if k₀ ≤ k.val then k.val else k₀ : ℕ) : ℝ)),
        if root then x else y)
  | .inr false => (b₁, ε, x)
  | .inr true => (b₂, δ, y)

/-- The finite centered Gaussian vector selected by the tuple. -/
noncomputable def compatibleBarrierPairCoordinates
    {Ω : Type*} (Y Z : Ω → ℝ → ℂ → ℝ)
    (k₀ m : ℕ) (ε δ : ℝ) (x y : ℂ) (b₁ b₂ : Bool) :
    Ω → CompatibleBarrierPairIndex m → ℝ := fun ω i =>
  let q := compatibleBarrierPairTuple k₀ m ε δ x y b₁ b₂ i
  if q.1 then Y ω q.2.1 q.2.2 else Z ω q.2.1 q.2.2

/-- The event that the finite vector satisfies both roots' coarse barrier constraints. -/
def compatibleBarrierPairRectangle
    (a : ℝ) (k₀ m : ℕ)
    (z : CompatibleBarrierPairIndex m → ℝ) : Prop :=
  ∀ j : CompatibleBarrierPairActiveIndex k₀ m,
    z (.inl j.val) ≤ a * (j.val.1.val : ℝ)

/-- Indicator of the finite two-root barrier rectangle. -/
noncomputable def compatibleBarrierPairRectangleIndicator
    (a : ℝ) (k₀ m : ℕ) :
    (CompatibleBarrierPairIndex m → ℝ) → ℝ≥0∞ := fun z =>
  Set.indicator {z | compatibleBarrierPairRectangle a k₀ m z}
    (fun _ => (1 : ℝ≥0∞)) z

/-- The two fine-field coordinate slots. -/
def compatibleBarrierPairRoot₁ {m : ℕ} : CompatibleBarrierPairIndex m := .inr false
def compatibleBarrierPairRoot₂ {m : ℕ} : CompatibleBarrierPairIndex m := .inr true

/-- The finite two-root Gaussian tilt of the common coarse barrier rectangle. -/
noncomputable def compatibleAdmissibleSelectedFiniteBarrierPairTiltedKernel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y Z : Ω → ℝ → ℂ → ℝ) (γ a : ℝ) (k₀ m : ℕ)
    (ε δ : ℝ) (x y : ℂ) (b₁ b₂ : Bool) : ℝ≥0∞ := by
  classical
  let V := compatibleBarrierPairCoordinates Y Z k₀ m ε δ x y b₁ b₂
  exact ENNReal.ofReal (Real.exp (γ ^ 2 / 2 *
      (gaussianCovariance P (fun ω => V ω compatibleBarrierPairRoot₁)
          (fun ω => V ω compatibleBarrierPairRoot₂) +
        gaussianCovariance P (fun ω => V ω compatibleBarrierPairRoot₂)
          (fun ω => V ω compatibleBarrierPairRoot₁)))) *
    (∫⁻ ω, compatibleBarrierPairRectangleIndicator a k₀ m
      (fun i => V ω i + γ * gaussianCovariance P (fun ω => V ω i)
          (fun ω => V ω compatibleBarrierPairRoot₁) +
        γ * gaussianCovariance P (fun ω => V ω i)
          (fun ω => V ω compatibleBarrierPairRoot₂)) ∂P)


end DOZZ.Proofs
