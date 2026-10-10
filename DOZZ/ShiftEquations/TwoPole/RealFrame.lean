/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.Frame
public import DOZZ.ShiftEquations.PoleSubtracted.CutoffGood
public import DOZZ.Statements.ShiftEquations.PoleSubtractedObservable
import DOZZ.ShiftEquations.PoleSubtracted.RealLimit
import DOZZ.GMC.Moments.RhoMoment

/-!
# The real identity of the two-pole expansion

For `2η < x < 1/γ` the three charges `(x, 2/γ + η, 2/γ - η)` lie in the extended Seiberg domain,
so the structure-constant moment is finite, and by the frame identity so is the total moment
`E[Z_ℂ(x)^{1-x/γ}]`. The pole-subtracted observable plus the local moment is then the total
moment, which is `(γ/2) 2^{-4(1-x/γ)} C̄(x, α₂, α₃)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The charges of the two-pole expansion lie in the extended Seiberg domain. -/
theorem extendedSeiberg3_pole {γ η δ x : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hW : TwoPoleWindow γ η δ) (hx₁ : 2 * η < x) (hx₂ : x < 1 / γ) :
    ExtendedSeiberg3 γ x (2 / γ + η) (2 / γ - η) := by
  have hη := window_eta_pos hW
  have hη4 := window_eta_lt_quarter hW
  have hs : -sExp γ x (2 / γ + η) (2 / γ - η) = 1 - x / γ := by
    unfold sExp Q
    field_simp
    ring
  have hxγ : x / γ < 1 / γ ^ 2 := by
    rw [div_lt_iff₀ hγ]
    calc x < 1 / γ := hx₂
      _ = 1 / γ ^ 2 * γ := by field_simp
  have h4 : 1 < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hQ]
    have : x < 2 / γ := by
      have : 1 / γ < 2 / γ := by
        rw [div_lt_div_iff_of_pos_right hγ]
        norm_num
      linarith
    linarith
  · rw [hQ]
    linarith
  · rw [hQ]
    linarith
  · rw [hs]
    have hxpos : 0 < x / γ := div_pos (by linarith) hγ
    refine lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))
    · linarith
    · have : 2 / γ * (Q γ - x) = 1 + 4 / γ ^ 2 - 2 * (x / γ) := by
        rw [hQ]
        field_simp
        ring
      rw [this]
      have : x / γ < 4 / γ ^ 2 := by
        have : 1 / γ ^ 2 < 4 / γ ^ 2 := by
          rw [div_lt_div_iff_of_pos_right (by positivity)]
          norm_num
        linarith
      linarith
    · have : 2 / γ * (Q γ - (2 / γ + η)) = 1 - 2 * η / γ := by
        rw [hQ]
        field_simp
        ring
      rw [this]
      have : 2 * η / γ < x / γ := by
        rw [div_lt_div_iff_of_pos_right hγ]
        exact hx₁
      linarith
    · have : 2 / γ * (Q γ - (2 / γ - η)) = 1 + 2 * η / γ := by
        rw [hQ]
        field_simp
        ring
      rw [this]
      have : 0 < 2 * η / γ := by positivity
      linarith

/-- The total moment at a real charge of the expansion is finite. -/
theorem lintegral_totalMass_rpow_lt_top_pole {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ x : ℝ} (hW : TwoPoleWindow γ η δ)
    (hx₁ : 2 * η < x) (hx₂ : x < 1 / γ) :
    ∫⁻ ω, poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) ^ (1 - x / γ) ∂P < ⊤ := by
  have hES := extendedSeiberg3_pole hγ hγ2 hW hx₁ hx₂
  have hrho := (equatorGFF_extendedSeiberg_rho_moment P X hX γ hγ hγ2 M hM x (2 / γ + η)
    (2 / γ - η) hES).2
  have hs : -sExp γ x (2 / γ + η) (2 / γ - η) = 1 - x / γ := by
    unfold sExp Q
    field_simp
    ring
  simp only [hs, ENNReal.rpow_eq_pow] at hrho
  rw [lintegral_totalMass_rpow_eq_rho P X hX γ hγ hγ2 M hM η x]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hrho

/-- **The real identity**: the pole-subtracted observable plus the local moment is the total
moment. -/
theorem observable_add_localMoment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ x : ℝ} (hW : TwoPoleWindow γ η δ)
    (hx₁ : 2 * η < x) (hx₂ : x < 1 / γ)
    (hLint : Integrable (fun ω => localMassReal M γ η ω ^ (1 - x / γ)) P) :
    poleSubtractedObservable P M γ η x + ∫ ω, localMassReal M γ η ω ^ (1 - x / γ) ∂P =
      (∫⁻ ω, poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) ^ (1 - x / γ) ∂P).toReal := by
  have hxQ : x < Q γ := by
    have : 1 / γ < Q γ := by
      rw [Q]
      have : 1 / γ < 2 / γ := by
        rw [div_lt_div_iff_of_pos_right hγ]
        norm_num
      linarith [half_pos hγ]
    linarith
  have hgood := ae_cutoffGood P X hX γ hγ hγ2 M hM hW
  have hfin := ae_totalMass_lt_top_of_lt P X hX γ hγ hγ2 M hM hW hxQ
  have hTpos : ∀ᵐ ω ∂P, 0 < poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) := by
    filter_upwards [hgood] with ω hω
    exact hω.1.trans_le ((localMass_le_cutoffTiltedMass γ η x 0 (M ω)).trans
      (cutoffTiltedMass_le_totalMass γ η x 0 (M ω)))
  set T : Ω → ℝ := fun ω =>
    (poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω)).toReal ^ (1 - x / γ) with hT
  have hTmeas : AEMeasurable T P :=
    ((aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
      (measurable_poleTotalMass γ η x)).ennreal_toReal).pow_const _
  have hTofReal : ∀ᵐ ω ∂P, ENNReal.ofReal (T ω) =
      poleTotalMass γ x (2 / γ + η) (2 / γ - η) (M ω) ^ (1 - x / γ) := by
    filter_upwards [hTpos, hfin] with ω h1 h2
    rw [hT, ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos h1.ne' h2.ne),
      ENNReal.ofReal_toReal h2.ne]
  have hTnn : 0 ≤ᵐ[P] T := Eventually.of_forall fun ω => Real.rpow_nonneg ENNReal.toReal_nonneg _
  have hTint : Integrable T P := by
    refine ⟨hTmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hTnn).2 ?_⟩
    rw [lintegral_congr_ae hTofReal]
    exact lintegral_totalMass_rpow_lt_top_pole P X hX γ hγ hγ2 M hM hW hx₁ hx₂
  have hobs : poleSubtractedObservable P M γ η x =
      ∫ ω, (T ω - localMassReal M γ η ω ^ (1 - x / γ)) ∂P := rfl
  rw [hobs, integral_sub hTint hLint, sub_add_cancel,
    integral_eq_lintegral_of_nonneg_ae hTnn hTmeas.aestronglyMeasurable,
    lintegral_congr_ae hTofReal]

end DOZZ.Proofs

end
