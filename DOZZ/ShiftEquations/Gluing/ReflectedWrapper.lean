/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.ReflectedAssembly
public import DOZZ.FourPoint.Diagonal.Assembly
public import DOZZ.FourPoint.ReflectedEnd.Formula

/-!
# The reflected shift and gluing from the two first shifts

Applying the classification `DOZZ.degenerateFourPoint_diagonal_classification` (at `χ = γ/2`) and
the reflected diagonal formula `DOZZ.gammaHalf_reflected_formula` in
`structureConstant_reflected_shift_and_gluing_of_deps` leaves
`DOZZ.reflectionR_first_shift_meromorphic` and `DOZZ.structureConstant_first_shift_strip` as the
remaining inputs.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The reflected shift and gluing from the two first shifts.** `hFirstShift`, `hFirstStrip` are the conclusions
of `reflectionR_first_shift_meromorphic` and `structureConstant_first_shift_strip` at the given
field, chaos, coupling and charges. -/
theorem structureConstant_reflected_shift_and_gluing_of_shifts
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hFirstShift : ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
          ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
            MeromorphicOn R {z | |z.im| < h} ∧
            (∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
            ∀ᶠ z in codiscrete ℂ,
              R (z - γ / 2) =
                -(μ * Real.pi : ℂ) * R z /
                  (lFun (-((γ : ℂ) ^ 2) / 4) *
                    lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                    lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    (hFirstStrip : ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
      MeromorphicOn C {z | |z.im| < h} ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ,
        C (z + γ / 2) =
          -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) =
                  (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)) :=
  structureConstant_reflected_shift_and_gluing_of_deps P X M γ μ η hγ hγ2 hμ hη α₂ α₃ hα₂ hα₃
    hFirstShift hFirstStrip
    (fun hH α₁ hα₁ hs => degenerateFourPoint_diagonal_classification hH P X M γ μ (γ / 2) α₁ α₂ α₃
      hγ hγ2 hμ (Or.inl rfl) hα₁ hα₂.2 hα₃.2 hs hX hM)
    (fun hH α₁ hα₁ hs hreflect hnear => gammaHalf_reflected_formula hH P M X γ μ α₁ α₂ α₃ hγ hγ2
      hμ hα₁ hα₂.2 hα₃.2 hs hreflect hnear hX hM)

end DOZZ.Proofs

end
