/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianCoefficients
import Mathlib.Analysis.Complex.RealDeriv

/-! Pointwise Cramer reconstruction and holomorphy of the conjugate coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The two Cramer coefficients reconstruct both the value and its first `∂z`
derivative from a nonvanishing analytic Wronskian pair. -/
theorem realGaussCramer_reconstruct
    (T : ℂ → ℝ) {f g : ℂ → ℂ} {z : ℂ}
    (hW : gaussCramerWronskian f g z ≠ 0) :
    (T z : ℂ) = gaussCramerCoefficient₁ T f g z * f z +
        gaussCramerCoefficient₂ T f g z * g z ∧
      wirtingerZ (fun w => (T w : ℂ)) z =
        gaussCramerCoefficient₁ T f g z * deriv f z +
          gaussCramerCoefficient₂ T f g z * deriv g z := by
  let A := gaussCramerNumerator₁ T g z
  let B := gaussCramerNumerator₂ T f z
  let W := gaussCramerWronskian f g z
  have hA : A * f z + B * g z = (T z : ℂ) * W := by
    dsimp [A, B, W, gaussCramerNumerator₁, gaussCramerNumerator₂,
      gaussCramerWronskian]
    ring
  have hB : A * deriv f z + B * deriv g z =
      wirtingerZ (fun w => (T w : ℂ)) z * W := by
    dsimp [A, B, W, gaussCramerNumerator₁, gaussCramerNumerator₂,
      gaussCramerWronskian]
    ring
  have hW' : W ≠ 0 := hW
  constructor
  · change (T z : ℂ) = (A * W⁻¹) * f z + (B * W⁻¹) * g z
    calc
      (T z : ℂ) = ((T z : ℂ) * W) * W⁻¹ := by
        calc
          (T z : ℂ) = (T z : ℂ) * (W * W⁻¹) := by
            rw [mul_inv_cancel₀ hW']
            simp
          _ = ((T z : ℂ) * W) * W⁻¹ := by ring
      _ = (A * f z + B * g z) * W⁻¹ := by rw [hA]
      _ = (A * W⁻¹) * f z + (B * W⁻¹) * g z := by ring
  · change wirtingerZ (fun w => (T w : ℂ)) z =
      (A * W⁻¹) * deriv f z + (B * W⁻¹) * deriv g z
    calc
      wirtingerZ (fun w => (T w : ℂ)) z =
          (wirtingerZ (fun w => (T w : ℂ)) z * W) * W⁻¹ := by
        calc
          wirtingerZ (fun w => (T w : ℂ)) z =
              wirtingerZ (fun w => (T w : ℂ)) z * (W * W⁻¹) := by
            rw [mul_inv_cancel₀ hW']
            simp
          _ = (wirtingerZ (fun w => (T w : ℂ)) z * W) * W⁻¹ := by ring
      _ = (A * deriv f z + B * deriv g z) * W⁻¹ := by rw [hB]
      _ = (A * W⁻¹) * deriv f z + (B * W⁻¹) * deriv g z := by ring

/-- The conjugates of the Cramer coefficients are holomorphic on the slit plane. -/
theorem realGaussCramer_conjugates_analytic
    (a b c : ℝ) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T)
    {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hODEf : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) f z = 0)
    (hODEg : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ) g z = 0)
    (hW : ∀ z ∈ gaussCutPlane, gaussCramerWronskian f g z ≠ 0) :
    AnalyticOnNhd ℂ (fun z => star (gaussCramerCoefficient₁ T f g z)) gaussCutPlane ∧
      AnalyticOnNhd ℂ (fun z => star (gaussCramerCoefficient₂ T f g z)) gaussCutPlane := by
  have hcoeff := realGaussCramerCoefficients_wirtingerZ_eq_zero
    a b c T hT hf hg hODEf hODEg hW
  have hαdiff : DifferentiableOn ℂ
      (fun z => star (gaussCramerCoefficient₁ T f g z)) gaussCutPlane := by
    intro z hz
    obtain ⟨hαAt, hαz, _, _⟩ := hcoeff z hz
    exact (differentiableAt_star_of_wirtingerZ_eq_zero hαAt hαz).differentiableWithinAt
  have hβdiff : DifferentiableOn ℂ
      (fun z => star (gaussCramerCoefficient₂ T f g z)) gaussCutPlane := by
    intro z hz
    obtain ⟨_, _, hβAt, hβz⟩ := hcoeff z hz
    exact (differentiableAt_star_of_wirtingerZ_eq_zero hβAt hβz).differentiableWithinAt
  exact ⟨hαdiff.analyticOnNhd gaussCutPlane_isOpen,
    hβdiff.analyticOnNhd gaussCutPlane_isOpen⟩

end DOZZ.Proofs
