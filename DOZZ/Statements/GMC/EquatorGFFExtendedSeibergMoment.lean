/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.CoulombMass
import DOZZ.GMC.SharpMoments.SeibergMoment

/-! The statement `DOZZ.equatorGFF_extendedSeiberg_moment`,
proved by `DOZZ.Proofs.equatorGFF_extendedSeiberg_moment`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The global extended moment on `U_N`, with arbitrary distinct finite roots and an optional
root at infinity. See [KRV, (ThextendedSeibergbounds0) and (ThextendedSeibergbounds)]. -/
theorem equatorGFF_extendedSeiberg_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z)
    (α : Fin N → ℝ) (αinf : ℝ) (hαQ : ∀ k, α k < Q γ) (hαinf : αinf < Q γ)
    (hbulk : (2 * Q γ - (∑ k, α k + αinf)) / γ < 4 / γ ^ 2)
    (hins : ∀ k, (2 * Q γ - (∑ k, α k + αinf)) / γ < 2 / γ * (Q γ - α k))
    (hinsinf : (2 * Q γ - (∑ k, α k + αinf)) / γ < 2 / γ * (Q γ - αinf)) :
    0 < ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf)
        ((2 * Q γ - (∑ k, α k + αinf)) / γ) ∂P ∧
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf)
        ((2 * Q γ - (∑ k, α k + αinf)) / γ) ∂P < ⊤ := by exact DOZZ.Proofs.equatorGFF_extendedSeiberg_moment P X hX γ hγ hγ2 M hM z hz α αinf hαQ hαinf hbulk hins hinsinf

end DOZZ
