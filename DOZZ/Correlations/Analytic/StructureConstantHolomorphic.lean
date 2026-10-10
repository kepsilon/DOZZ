/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
public import DOZZ.Correlations.Analytic.MixedCoulombHolomorphic
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import DOZZ.GMC.Moments.RhoCoulomb

/-! Proof of `DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain` in the
canonical three-point frame. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The canonical extended three-point domain supplies the mixed-frame charge inequalities. -/
theorem structure_extended_moment_domain (γ : ℝ) (α : Fin 3 → ℝ)
    (hα : ExtendedSeiberg3 γ (α 0) (α 1) (α 2)) :
    (∀ i, α i < Q γ) ∧ (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2 ∧
      ∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i) := by
  obtain ⟨h0, h1, h2, hp⟩ := hα
  have he : (2 * Q γ - ∑ i, α i) / γ = -sExp γ (α 0) (α 1) (α 2) := by
    simp only [Fin.sum_univ_three, sExp]
    ring
  have hp' := lt_min_iff.mp hp
  refine ⟨?_, by rw [he]; exact hp'.1, ?_⟩
  · intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro i
    rw [he]
    fin_cases i
    · exact (lt_min_iff.mp hp'.2).1
    · exact (lt_min_iff.mp (lt_min_iff.mp hp'.2).2).1
    · exact (lt_min_iff.mp (lt_min_iff.mp hp'.2).2).2

/-- Proof of the canonical-frame statement
`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`. -/
theorem unitVolumeStructureConstant_holomorphic_near_extended_domain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ V : Set (Fin 3 → ℂ), IsOpen V ∧
      (∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin 3 → ℂ) → ℂ, DifferentiableOn ℂ f V ∧
        ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
          f (complexifyNCharges α) =
            (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ) := by
  obtain ⟨Xc, hc⟩ := exists_equatorGFF_circle_average_witness X hX
  have hz : Function.Injective (![0, 1] : Fin 2 → ℂ) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨V, hV, hmem, f, hf, hreal⟩ := mixed_coulomb_holomorphic
    P X hX γ hγ hγ2 M hM Xc hc (![0, 1] : Fin 2 → ℂ) hz
  refine ⟨V, hV, ?_, (fun β => (2 / γ : ℂ) * f β), ?_, ?_⟩
  · intro α hα
    obtain ⟨ha, hp, hpi⟩ := structure_extended_moment_domain γ α hα
    exact hmem α ha hp hpi
  · exact hf.const_mul _
  · intro α hα
    obtain ⟨ha, hp, hpi⟩ := structure_extended_moment_domain γ α hα
    have he := hreal α ha hp hpi
    have hcharges : (fun i : Fin 2 => α i.castSucc) = ![α 0, α 1] := by
      ext i
      fin_cases i <;> rfl
    have hsum : (∑ i : Fin 3, α i) = (∑ i : Fin 2, (![α 0, α 1] : Fin 2 → ℝ) i) + α 2 := by
      simp only [Fin.sum_univ_three, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hm := rho_moment_eq_coulomb_moment P X hX γ hγ hγ2 M hM (α 0) (α 1) (α 2)
    change (2 / γ : ℂ) * f (fun i => (α i : ℂ)) = _
    rw [he]
    simp only [hcharges, hsum, show Fin.last 2 = (2 : Fin 3) from rfl]
    unfold unitVolumeStructureConstant
    push_cast
    congr 1
    congr 1
    simpa only [ENNReal.rpow_eq_pow] using congrArg ENNReal.toReal hm.symm

end DOZZ.Proofs
