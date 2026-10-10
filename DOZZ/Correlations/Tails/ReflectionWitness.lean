/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.ShiftEquations.Reflection.Witness

/-! One source lateral measure and one reflection family for all charges below the Seiberg bound. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The source witness required by the uniform one-insertion theorem can be chosen before
the compact charge set and the admissible error exponent. -/
theorem exists_source_reflection_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        ∀ α : ℝ, α < Q γ → IsReflectionData P γ α (B α) Z := by
  obtain ⟨A, hc, hA, hA0, hBp, hBn, hhalves, hZmeas, hAZ, hZ⟩ :=
    equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ2 hX hM
  let Z := fun ω => lateralProjectedGMC γ (A ω) (M ω)
  have hsource : IsSourceLateralProjection P X γ M Z :=
    ⟨hX, hM, A, hc, hA, hA0, hBp, hBn, hhalves, hZmeas, hAZ,
      ae_of_all P (fun _ => rfl)⟩
  obtain ⟨B, hB⟩ := exists_reflectionData_family P X γ M Z hsource hZ
  exact ⟨B, Z, hsource, hB⟩


end DOZZ.Proofs
