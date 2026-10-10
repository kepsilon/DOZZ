/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Residual.Calibration
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.BrownianPath
import DOZZ.Roots.CubeContinuation
import DOZZ.ShiftEquations.Reflection.Witness
import DOZZ.Brownian.Lateral.ReflectionJointLaw

/-!
# The residual factor from the first and the first-case dual structure shifts

Put `η₀ = min η (γ/4)`. For `α₂, α₃` in `(Q - η₀, Q)` the first structure shift
(`structureConstant_first_shift_strip`) and the first-case dual structure shift
(`structureConstant_dual_shift_strip_first_case`, `η₀ ≤ γ/4`) give a joint representative
(`exists_joint_representative`); the removable-periodic quotient
(`structureConstant_DOZZ_quotient_removable_periodic`) and the dense periods `γ, 4/γ` make `C = c D`
on the slice, and the zero mode `α₁ = 2Q - α₂ - α₃` (where `C̄ = 2/γ` and the normalized DOZZ
companion tends to `2/γ`) fixes `c = 1`. This is the calibrated identity on the small cube; the
continuation `roots_unitVolume_of_cube` (with
`unitVolumeStructureConstant_holomorphic_near_extended_domain` along affine charge lines) carries it
to every pole-free extended triple, in particular to the cube of size `η` (where `s > 0` since
`3η < Q`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- **The residual factor from the first structure shift and the first-case dual structure shift.**
`hFirstStrip` is the conclusion of `DOZZ.structureConstant_first_shift_strip` at the given field, chaos and
coupling; `hDualStripFirstCase` is the first case `η ≤ γ/4` of the dual structure shift
(`structureConstant_dual_shift_strip_first_case`), restricted to its structure-constant clauses. -/
theorem unitVolume_residual_factor_eq_one_of_shifts
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ) (U : ℂ → ℂ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hU : IsUpsilon γ U)
    (hFirstStrip : ∀ η' : ℝ, (0 < η' ∧ Q γ - 2 * η' > γ) → ∀ α₂ α₃ : ℝ,
      (Q γ - η' < α₂ ∧ α₂ < Q γ) → (Q γ - η' < α₃ ∧ α₃ < Q γ) →
      ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
        MeromorphicOn C {z | |z.im| < h} ∧
        (∀ α : ℝ, 2 * η' < α → α < Q γ →
          C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
        ∀ᶠ z in codiscrete ℂ,
          C (z + γ / 2) =
            -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
              C (z - γ / 2))
    (hDualStripFirstCase : ∀ η' : ℝ, (0 < η' ∧ Q γ - 2 * η' > γ) → η' ≤ γ / 4 → ∀ α₂ α₃ : ℝ,
      (Q γ - η' < α₂ ∧ α₂ < Q γ) → (Q γ - η' < α₃ ∧ α₃ < Q γ) →
      ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
        MeromorphicOn C {z | |z.im| < h} ∧
        (∀ α : ℝ, 2 * η' < α → α < Q γ →
          C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
        ∀ᶠ z in codiscrete ℂ,
          C (z + 2 / γ) =
            -(1 / (Real.pi * dualMu γ μ)) *
              shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) * C (z - 2 / γ)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ cγ : ℂ, cγ = 1 ∧
              ∀ α₁ α₂ α₃ : ℝ,
                Q γ - η < α₁ → α₁ < Q γ →
                Q γ - η < α₂ → α₂ < Q γ →
                Q γ - η < α₃ → α₃ < Q γ →
                  (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
                    cγ * ((μ : ℂ) ^ ((sExp γ α₁ α₂ α₃ : ℂ)) /
                      Complex.Gamma (sExp γ α₁ α₂ α₃ : ℂ) *
                        dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ)) := by
  obtain ⟨hη0, hηγ, hη3⟩ := hη
  -- the small cube
  set η₀ : ℝ := min η (γ / 4) with hη₀
  have hη₀le : η₀ ≤ η := min_le_left _ _
  have hη₀4 : η₀ ≤ γ / 4 := min_le_right _ _
  have hη₀0 : 0 < η₀ := lt_min hη0 (by positivity)
  have hη₀γ : Q γ - 2 * η₀ > γ := by linarith
  have hη₀3 : 3 * η₀ < Q γ := by linarith
  have hsmall : ∀ a b c : ℝ, Q γ - η₀ < a → a < Q γ → Q γ - η₀ < b → b < Q γ →
      Q γ - η₀ < c → c < Q γ → (unitVolumeStructureConstant P M γ a b c : ℂ) =
        ((μ : ℂ) ^ (sExp γ a b c : ℂ) / Complex.Gamma (sExp γ a b c)) *
          dozzFormula γ μ U a b c := by
    intro a b c ha1 ha2 hb1 hb2 hc1 hc2
    have hjoint := exists_joint_representative P M (η := η₀) (α₂ := b) (α₃ := c)
      (by linarith) (hFirstStrip η₀ ⟨hη₀0, hη₀γ⟩ b c ⟨hb1, hb2⟩ ⟨hc1, hc2⟩)
      (hDualStripFirstCase η₀ ⟨hη₀0, hη₀γ⟩ hη₀4 b c ⟨hb1, hb2⟩ ⟨hc1, hc2⟩)
    obtain ⟨c₀, hc₀⟩ := slice_constant_of_joint P M hγ hγ2 hγirr hμ ⟨hη₀0, hη₀γ⟩
      ⟨hb1, hb2⟩ ⟨hc1, hc2⟩ hU hjoint
    exact slice_identity_calibrated P X M hγ hγ2 hμ hX hM hU ⟨hη₀0, hη₀γ⟩ ⟨hb1, hb2⟩
      ⟨hc1, hc2⟩ hc₀ a (by linarith) ha2
  -- the witnesses
  obtain ⟨A, hXcA, hAm, hA0, hBf, hBb, hInd, hLm, hIndL, hLat⟩ :=
    equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ2 hX hM
  have hSLP : IsSourceLateralProjection P X γ M
      (fun ω => lateralProjectedGMC γ (A ω) (M ω)) :=
    ⟨hX, hM, A, hXcA, hAm, hA0, hBf, hBb, hInd, hLm, hIndL, Eventually.of_forall fun _ => rfl⟩
  obtain ⟨B, hB⟩ := exists_reflectionData_family P X γ M _ hSLP hLat
  refine ⟨B, fun ω => lateralProjectedGMC γ (A ω) (M ω), hSLP, fun α _ hα => hB α hα, 1, rfl,
    fun α₁ α₂ α₃ h1 h2 h3 h4 h5 h6 => ?_⟩
  have hs : 0 < sExp γ α₁ α₂ α₃ := by
    unfold sExp
    exact div_pos (by linarith) hγ
  rw [one_mul]
  exact roots_unitVolume_of_cube P X M γ μ η₀ hγ hγ2 hμ hη₀0 hη₀3 U hU hX hM hsmall α₁ α₂ α₃
    (roots_extended_cube hγ hη3 h1 h2 h3 h4 h5 h6)
    (fun n hn => by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)

end DOZZ.Proofs

end
