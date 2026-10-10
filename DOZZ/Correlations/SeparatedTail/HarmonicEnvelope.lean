/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.HarmonicMoments
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Measurability of the compact harmonic envelope of the separated joint-tail estimate and its
correlated product bound. -/

@[expose] public section
open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- Almost-sure spatial continuity makes the compact supremum a measurable random variable.
The proof modifies the field on a measurable null set before taking the uncountable supremum. -/
theorem separatedTail_harmonic_envelope_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℂ) (H : Ω → ℂ → ℝ) (hH : Measurable (fun q : Ω × ℂ => H q.1 q.2))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (H ω) (closedBall c 1)) (l : ℝ) :
    AEMeasurable (fun ω => ⨆ z ∈ closedBall c 1,
      ENNReal.ofReal (Real.exp (l*|H ω z|))) P := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (mem_ae_iff.mp hcont)
  let S := Nᶜ
  have hSm : MeasurableSet S := hNm.compl
  have hS : ∀ᵐ ω ∂P, ω ∈ S := compl_mem_ae_iff.mpr hN0
  have hgood : ∀ ω ∈ S, ContinuousOn (H ω) (closedBall c 1) := by
    intro ω hω
    by_contra hbad
    exact hω (hNsub hbad)
  let f : closedBall c 1 → Ω → ℝ≥0∞ := fun z ω =>
    if ω ∈ S then ENNReal.ofReal (Real.exp (l*|H ω z|)) else 0
  have hf (z : closedBall c 1) : Measurable (f z) := by
    apply Measurable.ite hSm
    · exact measurable_ofReal_exp_mul_abs (fun ω => H ω z)
        (hH.comp (measurable_id.prodMk measurable_const)) l
    · exact measurable_const
  have hc (ω : Ω) : Continuous (fun z : closedBall c 1 => f z ω) := by
    by_cases hω : ω ∈ S
    · have ht : Continuous (fun z : closedBall c 1 => H ω z) :=
        continuousOn_iff_continuous_domRestrict.mp (hgood ω hω)
      simpa only [f, ite_eq_left hω, Function.comp_def] using
        ENNReal.continuous_ofReal.comp ((ht.abs.const_mul l).rexp)
    · simpa only [f, ite_eq_right hω] using
        (continuous_const : Continuous (fun _ : closedBall c 1 => (0 : ℝ≥0∞)))
  have hmeas := measurable_iSup_of_lowerSemicontinuous hf (fun ω => (hc ω).lowerSemicontinuous)
  refine hmeas.aemeasurable.congr ?_
  filter_upwards [hS] with ω hω
  simp only [iSup_apply, f, ite_eq_left hω, iSup_subtype]

/-- Correlated positive envelopes with two doubled-order bounds have a uniform product bound.
This elementary sum bound avoids introducing any independence hypothesis. -/
theorem separatedTail_correlated_envelope_product_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E2 E3 : Ω → ℝ≥0∞) (hE2 : AEMeasurable E2 P)
    (B2 B3 : ℝ≥0∞)
    (h2 : (∫⁻ ω, E2 ω ^ (2 : ℝ) ∂P) ≤ B2)
    (h3 : (∫⁻ ω, E3 ω ^ (2 : ℝ) ∂P) ≤ B3) :
    (∫⁻ ω, E2 ω * E3 ω ∂P) ≤ B2+B3 := by
  calc
    _ ≤ ∫⁻ ω, E2 ω ^ (2 : ℝ) + E3 ω ^ (2 : ℝ) ∂P := lintegral_mono fun ω => by
      simp only [ENNReal.rpow_two, pow_two]
      rcases le_total (E2 ω) (E3 ω) with h | h
      · exact (mul_le_mul_left h (E3 ω)).trans le_add_self
      · exact (mul_le_mul_right h (E2 ω)).trans le_self_add
    _ = (∫⁻ ω, E2 ω ^ (2 : ℝ) ∂P)+(∫⁻ ω, E3 ω ^ (2 : ℝ) ∂P) :=
      lintegral_add_left' (hE2.pow_const _) _
    _ ≤ _ := add_le_add h2 h3

end DOZZ.Proofs
