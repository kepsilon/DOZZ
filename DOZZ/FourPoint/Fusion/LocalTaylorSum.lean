/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalR2Coefficient
public import DOZZ.FourPoint.Fusion.NormalizedLittleO

/-! # Summing the three local Taylor contributions -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The pure contribution, its conjugate, and the mixed contribution sum to `-p A`. -/
theorem fusionLocalOneRooted_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ =>
      (fusionLocalR1 P M γ α₁ α₂ α₃ p z + fusionLocalR2 P M γ α₁ α₂ α₃ p z +
        star (fusionLocalR1 P M γ α₁ α₂ α₃ p z)) / (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ))
      (nhdsWithin 0 {0}ᶜ) (nhds ((-p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p : ℝ) : ℂ)) := by
  have h1 := fusionLocalR1_coefficient_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp
  have h2 := fusionLocalR2_coefficient_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hsq hα₁ hα₂ hα₃ p hp
  have h := (h1.add h2).add h1.star
  have hreal (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp
  simp only [star_div₀, hreal, ← add_div] at h
  have he : -1 < γ ^ 2 / 2 - γ * α₁ := by
    have hd := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
    linarith only [hd.2.2.2.1]
  have halg (p e A : ℝ) (he : -1 < e) :
      (-p / 4 * e / (e + 1) * A) + (-p / 2 * (e + 2) / (e + 1) * A) +
        (-p / 4 * e / (e + 1) * A) = -p * A := by
    field_simp [show e + 1 ≠ 0 by linarith]
    ring
  have hc := congrArg Complex.ofReal (halg p (γ ^ 2 / 2 - γ * α₁)
    (gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p) he)
  simp only [Complex.ofReal_add] at hc
  rw [hc] at h
  exact h


end DOZZ.Proofs
