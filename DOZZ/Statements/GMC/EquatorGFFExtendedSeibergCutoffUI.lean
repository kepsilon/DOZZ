/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.RegularizedCoulombMass
import DOZZ.GMC.SharpMoments.ExtendedSeibergCutoffUI

/-! The statement `DOZZ.equatorGFF_extendedSeiberg_cutoff_UI`,
proved by `DOZZ.Proofs.equatorGFF_extendedSeiberg_cutoff_UI`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The regularized global `U_N` masses converge in probability and have a uniformly integrable
higher moment on compact charge, power, and noncolliding-center sets. The higher power handles
positive and negative Seiberg exponents. -/
theorem equatorGFF_extendedSeiberg_cutoff_UI
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition)
    (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ)) {N : ℕ}
    (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S)
    (hadm : ∀ c ∈ S,
      0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 < 4 / c.1 ^ 2 ∧
      (∀ k, (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 <
        2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 <
        2 / c.1 * (Q c.1 - c.2.2.2)) :
    (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun r : ℝ => ⨆ c ∈ S, P {ω | ε ≤ edist
        (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω).toReal
        (coulombMass c.1 (Mfam c.1 ω) c.2.2.1 c.2.1 c.2.2.2).toReal})
      atTop (𝓝 0)) ∧
    (∃ η : ℝ, 0 < η ∧ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ S, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, ENNReal.rpow
        (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω)
        ((1 + η) * ((2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1)) ∂P ≤ B) := by exact DOZZ.Proofs.equatorGFF_extendedSeiberg_cutoff_UI P X hX Xc hXc partition Mfam hMfam S hS hadm

end DOZZ
