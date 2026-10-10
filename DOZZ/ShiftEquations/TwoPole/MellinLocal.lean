/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.LocalTail
public import DOZZ.ShiftEquations.PoleSubtracted.CutoffGood
public import DOZZ.Statements.Correlations.OneInsertionTailCoefficient
public import DOZZ.Statements.Correlations.TwoInsertionTailCeiling
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Complex.TwoTailRational
import DOZZ.Complex.TwoTail
import DOZZ.Brownian.Reflection.PositiveFinite

/-!
# The Mellin transform of the local mass

Given the two-insertion tail expansion of the local mass `R₁ = R_{z₂} + R_{z₃}` at the poles `2, -2`
(the estimate `twoInsertion_tail_sum_uniform`, here as a hypothesis), the complex moments `E[R₁^s]`
continue meromorphically to `Re s < β₃` (any `β₃` below the double-tail ceiling) with simple poles
at the two reflection exponents and residues `-β c` (the theorem
`complexMoment_two_tail_residues_of_inverse_moments`). The local mass is positive and has negative
moments of all orders.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The local mass is almost surely positive and finite. -/
theorem ae_localMassReal_pos {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {η δ : ℝ} (hW : TwoPoleWindow γ η δ) :
    ∀ᵐ ω ∂P, 0 < localMassReal M γ η ω ∧
      poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) < ⊤ := by
  filter_upwards [ae_cutoffGood P X hX γ hγ hγ2 M hM hW] with ω hω
  exact ⟨hω.localMassReal_pos, hω.localMass_lt_top⟩

/-- The local mass has negative real moments of all orders. -/
theorem integrable_localMassReal_rpow_neg {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    {q : ℝ} (hq : 0 < q) : Integrable (fun ω => localMassReal M γ η ω ^ (-q)) P := by
  have hη := (window_eta_pos hW).le
  have hηγ := window_eta_le_two_div hγ hγ2 hW
  have hfin := lintegral_localMass_rpow_neg_lt_top P X hX γ hγ hγ2 M hM hη hηγ hq
  have hmeas : AEMeasurable (fun ω => localMassReal M γ η ω ^ (-q)) P :=
    (aemeasurable_localMassReal P X hX γ hγ hγ2 M hM η).pow_const _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hnn : 0 ≤ᵐ[P] fun ω => localMassReal M γ η ω ^ (-q) :=
    Eventually.of_forall fun ω => Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [hasFiniteIntegral_iff_ofReal hnn]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr_ae ?_)) hfin
  filter_upwards [ae_localMassReal_pos P X hX γ hγ hγ2 M hM hW] with ω hω
  rw [← ENNReal.ofReal_rpow_of_pos hω.1, localMassReal, ENNReal.ofReal_toReal hω.2.ne]

/-- The tail coefficient of a pole is positive. -/
theorem oneInsertionTailCoefficient_pos {γ α R F : ℝ} {z : ℂ} (hz : z ≠ 0) (hF : 0 < F)
    (hR : 0 < R) : 0 < oneInsertionTailCoefficient γ α z F R := by
  unfold oneInsertionTailCoefficient
  have h1 : 0 < Real.rpow ‖z‖ (-4 * α * (Q γ - α)) :=
    Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _
  have h2 : 0 < Real.rpow F (reflectionExponent γ α) := Real.rpow_pos_of_pos hF _
  positivity

/-- **The Mellin transform of the local mass**, from its two-insertion tail expansion. -/
theorem exists_localMass_mellin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    {R₂ R₃ θ C : ℝ} (hR₂ : 0 < R₂) (hR₃ : 0 < R₃)
    (htail : ∀ x : ℝ, 1 ≤ x →
      |(P {ω | ENNReal.ofReal x <
          localSingularMass M (poleFactorTwo γ η) 2 γ (2 / γ + η) ω +
            localSingularMass M (poleFactorNegTwo γ η) (-2) γ (2 / γ - η) ω}).toReal -
        (oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R₂ *
            Real.rpow x (-reflectionExponent γ (2 / γ + η)) +
          oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2)) R₃ *
            Real.rpow x (-reflectionExponent γ (2 / γ - η)))| ≤
        C * Real.rpow x (-(twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ)))
    (hβ : reflectionExponent γ (2 / γ - η) <
      twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ) :
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r
        {s | s.re < twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ} ∧
      ∀ s : ℂ, s.re < reflectionExponent γ (2 / γ + η) →
        Integrable (fun ω => ((localMassReal M γ η ω : ℝ) : ℂ) ^ s) P ∧
        ∫ ω, ((localMassReal M γ η ω : ℝ) : ℂ) ^ s ∂P =
          twoTailRational
            (oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R₂)
            (oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2)) R₃)
            (reflectionExponent γ (2 / γ + η)) (reflectionExponent γ (2 / γ - η)) s + r s := by
  have := hX.1
  have hη := (window_eta_pos hW)
  have hηγ := window_eta_le_two_div hγ hγ2 hW
  have hp := window_threshold_pos hγ hW
  set Lr : Ω → ℝ := localMassReal M γ η with hLr
  have hY : AEMeasurable Lr P := aemeasurable_localMassReal P X hX γ hγ hγ2 M hM η
  have hgood := ae_localMassReal_pos P X hX γ hγ hγ2 M hM hW
  have hpos : ∀ᵐ ω ∂P, 0 < Lr ω := by
    filter_upwards [hgood] with ω hω
    exact hω.1
  have hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Lr ω ^ (-q)) P := fun q hq =>
    integrable_localMassReal_rpow_neg P X hX γ hγ hγ2 M hM hW hq
  have hβ₁ : 0 < reflectionExponent γ (2 / γ + η) := by
    rw [reflectionExponent_pole hγ η]
    exact hp
  have hβ₁₂ : reflectionExponent γ (2 / γ + η) < reflectionExponent γ (2 / γ - η) := by
    rw [reflectionExponent_pole hγ η]
    have : reflectionExponent γ (2 / γ - η) = 1 + 2 * η / γ := by
      rw [reflectionExponent, Q]
      field_simp
      ring
    rw [this]
    have : 0 < 2 * η / γ := by positivity
    linarith
  have hF₂ : 0 < poleFactorTwo γ η 2 := by
    rw [poleFactorTwo_two hγ]
    positivity
  have hF₃ : 0 < poleFactorNegTwo γ η (-2) := by
    rw [poleFactorNegTwo_negTwo hγ]
    positivity
  have hc₁ := oneInsertionTailCoefficient_pos (γ := γ) (α := 2 / γ + η) (z := (2 : ℂ))
    two_ne_zero hF₂ hR₂
  have hc₂ := oneInsertionTailCoefficient_pos (γ := γ) (α := 2 / γ - η) (z := (-2 : ℂ))
    (by norm_num) hF₃ hR₃
  have hc₃ : 0 < max C 1 := lt_max_of_lt_right one_pos
  have htail' : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Lr hY t -
          oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R₂ *
            t ^ (-reflectionExponent γ (2 / γ + η)) -
          oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2)) R₃ *
            t ^ (-reflectionExponent γ (2 / γ - η))| ≤
        max C 1 * t ^ (-(twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ)) := by
    intro t ht
    have hevent : (P {ω | t < Lr ω}) = P {ω | ENNReal.ofReal t <
        localSingularMass M (poleFactorTwo γ η) 2 γ (2 / γ + η) ω +
          localSingularMass M (poleFactorNegTwo γ η) (-2) γ (2 / γ - η) ω} := by
      refine measure_congr ?_
      rw [eventuallyEqSet_iff]
      filter_upwards [hgood] with ω hω
      rw [← poleLocalMass_eq_localSingularMass M hγ hη.le hηγ ω, hLr, localMassReal,
        ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hω.2.ne]
    have h := htail t ht
    rw [← hevent] at h
    simp only [Real.rpow_eq_pow] at h
    calc _ = |(P {ω | t < Lr ω}).toReal -
          (oneInsertionTailCoefficient γ (2 / γ + η) 2 (poleFactorTwo γ η 2) R₂ *
              t ^ (-reflectionExponent γ (2 / γ + η)) +
            oneInsertionTailCoefficient γ (2 / γ - η) (-2) (poleFactorNegTwo γ η (-2)) R₃ *
              t ^ (-reflectionExponent γ (2 / γ - η)))| := by
          rw [realUpperTail, sub_sub]
      _ ≤ C * t ^ (-(twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ)) := h
      _ ≤ max C 1 * t ^ (-(twoInsertionTailCeiling γ (2 / γ + η) (2 / γ - η) - θ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  obtain ⟨hint, -, r, hr, -, hform, -⟩ := complexMoment_two_tail_residues_of_inverse_moments
    P Lr hY hpos hinv _ _ (max C 1) _ _ _ hc₁ hc₂ hc₃ hβ₁ hβ₁₂ hβ htail'
  exact ⟨r, hr, fun s hs => ⟨hint s hs, hform s hs⟩⟩

end DOZZ.Proofs

end
