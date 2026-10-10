/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.UnreflectedD
public import DOZZ.FourPoint.Diagonal.Assembly

/-! # The unreflected `γ/2` formula

Proof of `DOZZ.gammaHalf_full_unreflected_formula`: the conditional theorem
`bpz_gammaHalf_full_unreflected_formula_of_diag` applied to the diagonal classification at
`χ = γ/2`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- **The unreflected `γ/2` formula** ([KRV, Theorem 9.1]). -/
theorem gammaHalf_full_unreflected_formula {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
    let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
    let c := gaussParameterC γ (γ / 2) α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            ‖gaussFMinus H a b c z‖ ^ 2 +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              ‖gaussFPlus H a b c z‖ ^ 2 := by
  exact bpz_gammaHalf_full_unreflected_formula_of_diag hH P X M γ μ α₁ α₂ α₃ hγ hγ₂ hμ hαlo
    hαhi hα₂ hα₃ hs hX hM fun M' γ' t h0 h2 hM' hlo hhi h₂ h₃ hs' =>
      degenerateFourPoint_diagonal_classification hH P X M' γ' μ (γ' / 2) t α₂ α₃ h0 h2 hμ
        (Or.inl rfl)
        (by
          have hQ : Q γ' = 2 / γ' + γ' / 2 := rfl
          have : (0 : ℝ) < γ' / 2 := by positivity
          rw [hQ]; linarith)
        h₂ h₃ hs' hX hM'

end DOZZ.Proofs
