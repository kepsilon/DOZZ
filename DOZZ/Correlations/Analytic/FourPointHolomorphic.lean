/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
public import DOZZ.Correlations.Analytic.MixedCoulombHolomorphic
public import DOZZ.GMC.Construction.CircleAverageJointVersion

/-! Proof of `DOZZ.fourPointMoment_holomorphic_mixed_frame` on ordinary four-point vectors. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The ordinary mixed-frame domain is contained in the strict mixed moment domain. -/
theorem four_ordinary_moment_domain (γ : ℝ) (hγ : 0 < γ) (α : Fin 4 → ℝ)
    (ha : ∀ i, α i < Q γ) (hs : 0 < nPointSExp γ α) :
    (2 * Q γ - ∑ i, α i) / γ < 4 / γ ^ 2 ∧
      ∀ i, (2 * Q γ - ∑ j, α j) / γ < 2 / γ * (Q γ - α i) := by
  have he : (2 * Q γ - ∑ i, α i) / γ = -nPointSExp γ α := by
    unfold nPointSExp
    ring
  have hp : (2 * Q γ - ∑ i, α i) / γ < 0 := by rw [he]; linarith
  exact ⟨hp.trans (by positivity), fun i => hp.trans
    (mul_pos (by positivity) (sub_pos.mpr (ha i)))⟩

/-- Proof of the ordinary-vector statement `DOZZ.fourPointMoment_holomorphic_mixed_frame`. -/
theorem fourPointMoment_holomorphic_mixed_frame
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (z : ℂ) (hz : z ≠ 0 ∧ z ≠ 1) :
    ∃ V : Set (Fin 4 → ℂ), IsOpen V ∧
      (∀ α : Fin 4 → ℝ, (∀ i, α i < Q γ) → 0 < nPointSExp γ α →
        complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin 4 → ℂ) → ℂ, DifferentiableOn ℂ f V ∧
        ∀ α : Fin 4 → ℝ, (∀ i, α i < Q γ) → 0 < nPointSExp γ α →
          f (complexifyNCharges α) =
            ((∫⁻ ω, ENNReal.rpow
              (coulombMass γ (M ω) ![α 0, α 1, α 2] ![z, 0, 1] (α 3))
              (-nPointSExp γ α) ∂P).toReal : ℂ) := by
  obtain ⟨Xc, hc⟩ := exists_equatorGFF_circle_average_witness X hX
  have hzinj : Function.Injective (![z, 0, 1] : Fin 3 → ℂ) := by
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨V, hV, hmem, f, hf, hreal⟩ := mixed_coulomb_holomorphic
    P X hX γ hγ hγ2 M hM Xc hc (![z, 0, 1] : Fin 3 → ℂ) hzinj
  refine ⟨V, hV, ?_, f, hf, ?_⟩
  · intro α ha hs
    obtain ⟨hp, hpi⟩ := four_ordinary_moment_domain γ hγ α ha hs
    exact hmem α ha hp hpi
  · intro α ha hs
    obtain ⟨hp, hpi⟩ := four_ordinary_moment_domain γ hγ α ha hs
    have he := hreal α ha hp hpi
    have hcharges : (fun i : Fin 3 => α i.castSucc) = ![α 0, α 1, α 2] := by
      ext i
      fin_cases i <;> rfl
    have hpower : (2 * Q γ - ∑ i, α i) / γ = -nPointSExp γ α := by
      unfold nPointSExp
      ring
    change f (fun i => (α i : ℂ)) = _
    simpa only [hcharges, hpower, ENNReal.rpow_eq_pow,
      show Fin.last 3 = (3 : Fin 4) from rfl] using he

end DOZZ.Proofs
