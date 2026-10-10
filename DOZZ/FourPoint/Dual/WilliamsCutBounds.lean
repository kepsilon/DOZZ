/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.ReflectionCutMoments
public import DOZZ.Correlations.Tails.CanonicalSourceWilliamsLaw
public import DOZZ.Correlations.Tails.SourceCutOrdering
/-! Ordering and measurability of the actual dual Williams last-cut mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The random last-cut reflection mass is a measurable real observable. -/
theorem dual_williams_cut_real_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α : ℝ) (hα : α < Q γ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (hData : IsReflectionData P γ α B Z) :
    AEMeasurable (fun q : ℝ × Ω =>
      (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal)
      ((brownianMaximumReferenceLaw (Q γ-α)).prod P) := by
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα)
  exact (actual_cut_mass_joint_aemeasurable P _ γ B Z
    (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1.2.2.2.1
      hData.2.1.2.2.2.2.1).ennreal_toReal

/-- Above a fixed maximum cutoff the random cut lies between the fixed cut and the full
reflection mass, on the original reflection witness. All real conversions are justified
by the finite first moment of the full mass. -/
theorem dual_williams_cut_real_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α c : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    ∀ᵐ q : ℝ × Ω ∂(brownianMaximumReferenceLaw (Q γ-α)).prod P,
      0 ≤ (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal ∧
      (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal ≤
        (twoSidedReflectionMass γ B Z q.2).toReal ∧
      (c ≤ q.1 → (twoSidedReflectionCutMass γ c B Z q.2).toReal ≤
        (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal) := by
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα)
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ, hγ₂]
  have hJm := twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z
    (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1
  have hmoment := reflected_reflection_mass_moment_lt_top P γ α 1 B Z hα hData h4
  simp only [ENNReal.rpow_one] at hmoment
  have hJfin := ae_lt_top' hJm hmoment.ne
  have horder := source_last_exit_mono_prod_ae P (Q γ-α) c
    (sub_pos.mpr hα) (fun ω => (B ω).2) hData.1.2.1
  filter_upwards [horder, measurePreserving_snd.quasiMeasurePreserving.ae hJfin] with q hq hf
  have hcut := twoSidedReflectionCutMass_le_mass γ q.1 B Z q.2
  have hcutfin : twoSidedReflectionCutMass γ q.1 B Z q.2 ≠ ⊤ :=
    (hcut.trans_lt hf).ne
  refine ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hf.ne hcut, ?_⟩
  intro hc
  exact ENNReal.toReal_mono hcutfin
    (reflection_cut_mass_le_of_last_exit_le γ c q.1 B Z q.2 (hq hc))

end DOZZ.Proofs
