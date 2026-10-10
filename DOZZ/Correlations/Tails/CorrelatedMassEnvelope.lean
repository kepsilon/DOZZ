/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CutoffCompactMoment
public import DOZZ.GMC.SharpMoments.ArbitraryCenter
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Integrable products of correlated pin envelopes and compact cutoff masses. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- Hölder combines an envelope moment with the uniform cutoff and limiting GMC
moments. The same finite bound controls every integer cutoff and the actual limit; no
independence between the envelope and the field is assumed. -/
theorem regularized_mass_envelope_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ R : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 ≤ R)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (E : Ω → ℝ≥0∞) (hE : AEMeasurable E P)
    (p q : ℝ) (hpq : p.HolderConjugate q) (hqc : q < 4 / γ^2)
    (hEp : (∫⁻ ω, E ω ^ p ∂P) < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧
      (∀ n : ℕ, ∫⁻ ω, E ω * regularizedGMC P Xc γ n ω (Metric.closedBall 0 R) ∂P ≤ C) ∧
      (∫⁻ ω, E ω * M ω (Metric.closedBall 0 R) ∂P ≤ C) := by
  have hp : 0 < p := hpq.pos
  have hq : 0 < q := hpq.symm.pos
  obtain ⟨B, hB, hb⟩ := regularized_compact_mass_moment_uniform
    P X hX Xc hc γ q R hγ hγ2 hpq.symm.pos hqc hR
  have hLm := gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM
    (Metric.closedBall 0 R) (Metric.isBounded_closedBall) q hpq.symm.nonneg hqc
  let A : ℝ≥0∞ := (∫⁻ ω, E ω ^ p ∂P) ^ (1/p)
  let D : ℝ≥0∞ := gmcMassMoment P M (Metric.closedBall 0 R) q
  let C : ℝ≥0∞ := A * B ^ (1/q) + A * D ^ (1/q)
  have hA : A < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hEp.ne
  have hDB : B ^ (1/q) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hB.ne
  have hDD : D ^ (1/q) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by positivity) hLm.ne
  refine ⟨C, ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hA hDB,
    ENNReal.mul_lt_top hA hDD⟩, ?_, ?_⟩
  · intro n
    have hmass : AEMeasurable
        (fun ω => regularizedGMC P Xc γ n ω (Metric.closedBall 0 R)) P :=
      ((Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp
        (regularizedGMC_measurable P X hX Xc hc γ n)).aemeasurable
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hE hmass
    change (∫⁻ ω, E ω * regularizedGMC P Xc γ n ω (Metric.closedBall 0 R) ∂P) ≤ _ at h
    exact (h.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (hb n)
      (by positivity)))).trans (le_add_right le_rfl)
  · have hmass := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
      (Metric.closedBall 0 R) Metric.isClosed_closedBall.measurableSet
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq hE hmass
    change (∫⁻ ω, E ω * M ω (Metric.closedBall 0 R) ∂P) ≤ A * D ^ (1/q) at h
    exact h.trans (le_add_left le_rfl)


end DOZZ.Proofs
