/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.RepinField
public import DOZZ.Correlations.Tails.UnpinnedMeasureIdentification
public import DOZZ.GMC.Moments.InversionAdmissibleVersion
public import DOZZ.Statements.GMC.EquatorGFFCircleAverageGMCExists

/-! Realizing the translated unpinned field as an equator GFF, and identifying its GMC
on the unit disk with the transported source measure. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Translation followed by subtraction of the circle pin at the translated center. -/
noncomputable def translatedField {Ω : Type*} (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) : Ω → Distr :=
  repinField X (fun ω => Xc ω z 0) 1 z

theorem translated_field_isEquatorGFF
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) : IsEquatorGFF P (translatedField X Xc z) := by
  simpa only [translatedField, norm_one, Real.log_one, neg_zero] using
    isEquatorGFF_repinField P X Xc 1 z hX hc one_ne_zero

theorem translated_field_circleAverage
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) : IsCircleAverage P (translatedField X Xc z)
      (fun ω x r => Xc ω (z+x) r - Xc ω z 0) := by
  have he : repinCircle Xc (fun ω => Xc ω z (-Real.log ‖(1 : ℂ)‖)) 1 z =
      (fun ω x r => Xc ω (z+x) r - Xc ω z 0) := by
    funext ω x r
    simp only [repinCircle, norm_one, Real.log_one, neg_zero, one_mul, sub_zero, add_comm]
  have hh := isCircleAverage_repinField P X Xc 1 z hX hc one_ne_zero
  rw [he] at hh
  simpa only [translatedField, norm_one, Real.log_one, neg_zero] using hh

/-- Any GMC of the realized translated field has the literal transported source restriction.
This equality is on one event for all measurable integrands, including singular masses. -/
theorem translated_source_gmc_restriction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N) :
    ∀ᵐ ω ∂P, (N ω).restrict (Metric.ball 0 1) =
      transferredMeasure (M ω) z γ (Xc ω z 0) := by
  obtain ⟨K, hK, -, hNK⟩ := isGMCOf_restrict_admissible_version P
    (translatedField X Xc z) (translated_field_isEquatorGFF P X Xc hX hc z)
    γ hγ hγ2 N hN (fun ω x r => Xc ω (z+x) r - Xc ω z 0)
    (translated_field_circleAverage P X Xc hX hc z)
    (Metric.ball 0 1) Metric.isOpen_ball
  filter_upwards [hNK, unpinned_source_measure_identity P X Xc hX hc z hz γ M hM K hK]
    with ω hω hKω
  exact hω.trans hKω

/-- A genuine translated equator GMC exists on the original probability space and agrees
with the transported source chaos throughout the unit disk. -/
theorem translated_source_gmc_exists
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ, IsGMCOf P (translatedField X Xc z) γ N ∧
      ∀ᵐ ω ∂P, (N ω).restrict (Metric.ball 0 1) =
        transferredMeasure (M ω) z γ (Xc ω z 0) := by
  obtain ⟨-, N, -, hN⟩ := equatorGFF_circle_average_GMC_exists P
    (translatedField X Xc z) (translated_field_isEquatorGFF P X Xc hX hc z)
    γ hγ hγ2
  exact ⟨N, hN, translated_source_gmc_restriction P X Xc hX hc z hz γ hγ hγ2 M hM N hN⟩


end DOZZ.Proofs
