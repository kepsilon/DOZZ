/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.ComplexifyNCharges
public import DOZZ.Correlations.Analytic.MixedCoulombHolomorphic
public import DOZZ.Correlations.Analytic.AllFiniteFrame
public import DOZZ.Correlations.Analytic.ComplexCoulombPrefactor
public import DOZZ.GMC.Construction.CircleAverageJointVersion

/-! Proof of `DOZZ.unitVolumeNPoint_holomorphic_near_extended_domain` ([KRV, Theorem 6.1]) in
the all-finite N-point frame. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- Proof of `DOZZ.unitVolumeNPoint_holomorphic_near_extended_domain`, obtained from the
holomorphic zero infinity-charge slice and the entire finite-position Coulomb prefactor. -/
theorem unitVolumeNPoint_holomorphic_near_extended_domain
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 3 ≤ N)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (hM : IsGMCOf P X γ M) (z : Fin N → ℂ)
    (hz : ∀ i j, i ≠ j → z i ≠ z j) :
    ∃ V : Set (Fin N → ℂ), IsOpen V ∧
      (∀ α : Fin N → ℝ, ExtendedSeibergN γ α → complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin N → ℂ) → ℂ,
        DifferentiableOn ℂ f V ∧
          ∀ α : Fin N → ℝ, ExtendedSeibergN γ α →
            f (complexifyNCharges α) =
              (unitVolumeNPointCorrelation P M γ α z : ℂ) := by
  by_cases hZero : N = 0
  · subst N
    omega
  ·
    have hzinj : Function.Injective z := fun i j he => by
      by_contra hne
      exact hz i j hne he
    obtain ⟨Xc, hc⟩ := exists_equatorGFF_circle_average_witness X hX
    obtain ⟨V, hV, hmem, f, hf, hreal⟩ := mixed_coulomb_holomorphic
      P X hX γ hγ hγ2 M hM Xc hc z hzinj
    let W := appendZeroCharges ⁻¹' V
    have hAppend := append_zero_differentiable (N := N)
    have hW : IsOpen W := hV.preimage hAppend.continuous
    have hcast (α : Fin N → ℝ) : appendZeroCharges (complexifyNCharges α) =
        (fun i => ((Fin.snoc α (0 : ℝ) : Fin (N + 1) → ℝ) i : ℂ)) := by
      ext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [appendZeroCharges, Fin.snoc_last, Complex.ofReal_zero]
      · simp only [appendZeroCharges, Fin.snoc_castSucc, complexifyNCharges]
    let g := fun β => (2 / γ : ℂ) * complexCoulombPrefactor β z *
      f (appendZeroCharges β)
    refine ⟨W, hW, ?_, g, ?_, ?_⟩
    · intro α hα
      obtain ⟨ha, hp, hpi⟩ := append_zero_extended_domain γ hγ α hα
      change appendZeroCharges (complexifyNCharges α) ∈ V
      rw [hcast]
      exact hmem (Fin.snoc α 0) ha hp hpi
    · have hcomp : DifferentiableOn ℂ (fun β => f (appendZeroCharges β)) W :=
        hf.comp hAppend.differentiableOn (fun _ h => h)
      have hpref : DifferentiableOn ℂ (fun β => (2 / γ : ℂ) * complexCoulombPrefactor β z) W :=
        (complex_coulomb_prefactor_differentiable z).differentiableOn.const_mul _
      exact hpref.mul hcomp
    · intro α hα
      obtain ⟨ha, hp, hpi⟩ := append_zero_extended_domain γ hγ α hα
      have he := hreal (Fin.snoc α 0) ha hp hpi
      change (2 / γ : ℂ) * complexCoulombPrefactor (complexifyNCharges α) z *
        f (appendZeroCharges (complexifyNCharges α)) = _
      rw [hcast, he]
      change (2 / γ : ℂ) * complexCoulombPrefactor (fun i => (α i : ℂ)) z * _ = _
      rw [complex_coulomb_prefactor_ofReal α z hzinj]
      simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, add_zero]
      have hpower : (2 * Q γ - ∑ i, α i) / γ = -nPointSExp γ α := by
        unfold nPointSExp
        ring
      rw [hpower]
      unfold unitVolumeNPointCorrelation
      push_cast
      rfl

end DOZZ.Proofs
