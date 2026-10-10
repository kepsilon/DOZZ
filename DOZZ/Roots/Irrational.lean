/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.CubeContinuation
public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
/-! # Irrational-gamma root assembly from the calibrated residual identity -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- The source's sufficiently small cube can always be chosen in the first-case regime. -/
theorem roots_small_cube (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ η : ℝ, 0 < η ∧ η ≤ γ / 4 ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ := by
  have hQ : γ < Q γ := by
    have hq : γ / 2 < 2 / γ := by
      apply (lt_div_iff₀ hγ).mpr
      nlinarith only [hγ, hγ2]
    unfold Q
    linarith only [hq]
  let η := min ((Q γ - γ) / 8) (γ / 4)
  have hη : 0 < η := lt_min (by linarith only [hQ]) (by positivity)
  have hη1 : η ≤ (Q γ - γ) / 8 := min_le_left _ _
  exact ⟨η, hη, min_le_right _ _, by linarith only [hQ, hη1], by linarith only [hQ, hγ, hη1]⟩
/-- The exact residual-factor conclusion, followed by charge continuation, proves the irrational root. -/
theorem roots_main_of_calibrated_residual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (U : ℂ → ℂ) (hU : IsUpsilon γ U) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hresidual : ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        (∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
        ∃ cγ : ℂ, cγ = 1 ∧ ∀ α₁ α₂ α₃ : ℝ,
          Q γ - η < α₁ → α₁ < Q γ → Q γ - η < α₂ → α₂ < Q γ →
          Q γ - η < α₃ → α₃ < Q γ →
          (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
            cγ * ((μ : ℂ) ^ (sExp γ α₁ α₂ α₃ : ℂ) / Complex.Gamma (sExp γ α₁ α₂ α₃) *
              dozzFormula γ μ U α₁ α₂ α₃))
    (a b c : ℝ) (hα : ExtendedSeiberg3 γ a b c) (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    (structureConstant P M γ μ a b c : ℂ) = dozzFormula γ μ U a b c := by
  obtain ⟨η, hη, _hsmall, hηshift, hηQ⟩ := roots_small_cube γ hγ hγ2
  obtain ⟨B, Z, _hZ, _hB, cγ, hcγ, hcube⟩ := hresidual η ⟨hη, hηshift, hηQ⟩
  have hcube' : ∀ a b c : ℝ, Q γ - η < a → a < Q γ → Q γ - η < b → b < Q γ →
      Q γ - η < c → c < Q γ → (unitVolumeStructureConstant P M γ a b c : ℂ) =
        ((μ : ℂ) ^ (sExp γ a b c : ℂ) / Complex.Gamma (sExp γ a b c)) * dozzFormula γ μ U a b c := by
    intro a b c ha haQ hb hbQ hc hcQ
    simpa only [hcγ, one_mul] using hcube a b c ha haQ hb hbQ hc hcQ
  exact roots_structureConstant_of_unitVolume_value P M γ μ a b c hμ hs _
    (roots_unitVolume_of_cube P X M γ μ η hγ hγ2 hμ hη hηQ U hU hX hM hcube' a b c hα hs)
end DOZZ.Proofs
