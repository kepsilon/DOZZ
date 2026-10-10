/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ReflectionRealMoments
public import DOZZ.Statements.Brownian.ReflectionMassLastCutBound
public import DOZZ.Brownian.Reflection.LastCut
import Mathlib.Tactic
/-! Finite signed cut moments and the last-cut gap for the same reflection witness. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Each positive subcritical cut moment has its genuine integrable real representative.
The full reflection mass supplies finiteness; the cut is not replaced by an independent mass. -/
theorem dual_reflection_cut_real_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α q c : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z)
    (hq0 : 0 ≤ q) (hq : q < 4/γ^2) :
    Integrable (fun ω => (twoSidedReflectionCutMass γ c B Z ω).toReal^q) P ∧
    (∫ ω, (twoSidedReflectionCutMass γ c B Z ω).toReal^q ∂P) =
      (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^q ∂P).toReal := by
  have hZ := hData.2.1
  have hm := twoSidedReflectionCutMass_aemeasurable P γ c B Z
    (conditionedPair_aemeasurable P B (Q γ-α) hData.1) hZ.2.2.2.1 hZ.2.2.2.2.1
  have hf : (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^q ∂P) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (twoSidedReflectionCutMass_le_mass γ c B Z ω) hq0)
      (reflected_reflection_mass_moment_lt_top P γ α q B Z hα hData hq)
  constructor
  · simpa only [ENNReal.toReal_rpow] using
      integrable_toReal_of_lintegral_ne_top (hm.pow_const q) hf.ne
  · simpa only [ENNReal.toReal_rpow] using
      integral_toReal (hm.pow_const q) (ae_lt_top' (hm.pow_const q) hf.ne)

/-- The same supplied reflection witness gives the exponentially small moment gap between
the full mass and every nonnegative last-cut level. -/
theorem dual_reflection_cut_moment_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α q : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z)
    (hq0 : 0 < q) (hq : q < 4/γ^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 0 ≤ c →
      0 ≤ (∫⁻ ω, twoSidedReflectionMass γ B Z ω^q ∂P).toReal-
        (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^q ∂P).toReal ∧
      (∫⁻ ω, twoSidedReflectionMass γ B Z ω^q ∂P).toReal-
        (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^q ∂P).toReal ≤ C*Real.exp (-γ*c) := by
  obtain ⟨C, hC, hb⟩ := DOZZ.reflectionMass_lastCut_bound P γ hγ hγ₂
    {Q γ-α} {q} isCompact_singleton isCompact_singleton (fun _ => B)
    (by
      intro ν hν
      rw [mem_singleton_iff.mp hν]
      exact ⟨sub_pos.mpr hα,hData.1⟩)
    Z hData.2.1 (fun _ _ => hData.2.2)
    (by intro p hp; rw [mem_singleton_iff.mp hp]; exact ⟨hq0,hq⟩)
  exact ⟨C,hC,fun c hc => hb (Q γ-α) (mem_singleton _) q (mem_singleton _) c hc⟩

/-- Sending the last-cut level to infinity recovers the finite full reflection moment of the
same witness, with the exponential gap supplied by the Brownian estimate
`DOZZ.reflectionMass_lastCut_bound`. -/
theorem dual_reflection_cut_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α q : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hα : α < Q γ) (hData : IsReflectionData P γ α B Z)
    (hq0 : 0 < q) (hq : q < 4/γ^2) :
    Tendsto (fun c : ℝ => (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^q ∂P).toReal)
      atTop (𝓝 (∫⁻ ω, twoSidedReflectionMass γ B Z ω^q ∂P).toReal) := by
  obtain ⟨C, _, hb⟩ := dual_reflection_cut_moment_gap P γ α q hγ hγ₂ B Z hα hData hq0 hq
  have hscale : Tendsto (fun c : ℝ => γ*c) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hγ).mpr tendsto_id
  have he : Tendsto (fun c : ℝ => C*Real.exp (-γ*c)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale).const_mul C
  have hgap : Tendsto (fun c : ℝ =>
      (∫⁻ ω, twoSidedReflectionMass γ B Z ω^q ∂P).toReal-
        (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^q ∂P).toReal) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ he
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
      exact (hb c hc).1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
      exact (hb c hc).2
  have ht := (tendsto_const_nhds (x :=
    (∫⁻ ω, twoSidedReflectionMass γ B Z ω^q ∂P).toReal)).sub hgap
  simpa only [sub_sub_cancel, sub_zero] using ht

end DOZZ.Proofs
