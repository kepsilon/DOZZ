/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.RegularizedCoulombMass
import DOZZ.GMC.Moments.RhoMoment

/-! The statement `DOZZ.equatorGFF_extendedSeiberg_rho_moment`,
proved by `DOZZ.Proofs.equatorGFF_extendedSeiberg_rho_moment`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The extended-domain moment `E[ρ^{-s}]` of [DKRV, Lemma 3.10] is strictly positive and finite
on `ExtendedSeiberg3`, i.e. well defined there. See
[KRV, (ThextendedSeibergbounds0) and (ThextendedSeibergbounds)]. -/
theorem equatorGFF_extendedSeiberg_rho_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ : ℝ)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    0 < (∫⁻ ω,
      ENNReal.rpow (rho γ (M ω) α₁ α₂ α₃)
        (-sExp γ α₁ α₂ α₃) ∂P) ∧
      (∫⁻ ω,
        ENNReal.rpow (rho γ (M ω) α₁ α₂ α₃)
          (-sExp γ α₁ α₂ α₃) ∂P) < ⊤ := by exact DOZZ.Proofs.equatorGFF_extendedSeiberg_rho_moment P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα

end DOZZ
