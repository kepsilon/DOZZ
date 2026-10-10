/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionMassLastCutBound
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.FourPoint.Reflected.RadialTilt
import Mathlib.Tactic

/-! # Ordered removal of the reflected maximum cutoff

The actual supplied reflection data satisfy the last-cut bound `DOZZ.reflectionMass_lastCut_bound`.
This proves the `H → ∞` moment limit, which is used after the spatial limit.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The last-cut moment converges to the literal source reflection moment. -/
theorem reflected_cut_moment_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ α : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα : α < Q γ) (hreflect : Q γ - α < γ / 2)
    (hData : IsReflectionData P γ α B Z) :
    Tendsto (fun H : ℝ =>
      (∫⁻ ω, (twoSidedReflectionCutMass γ H B Z ω) ^ (reflectionExponent γ α) ∂P).toReal)
      atTop (nhds (reflectionBarR P γ α B Z)) := by
  have hν : 0 < Q γ - α := sub_pos.mpr hα
  have ha := reflected_exponent_mem_Ioo γ α hγ hα hreflect
  have hbulk : 1 < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ, hγ₂]
  obtain ⟨C, -, hb⟩ := DOZZ.reflectionMass_lastCut_bound P γ hγ hγ₂
    {Q γ - α} {reflectionExponent γ α} isCompact_singleton isCompact_singleton
    (fun _ => B) (by
      intro ν hνmem
      have he : ν = Q γ - α := mem_singleton_iff.mp hνmem
      subst ν
      exact ⟨hν, hData.1⟩) Z hData.2.1 (fun _ _ => hData.2.2) (by
      intro p hpmem
      have he : p = reflectionExponent γ α := mem_singleton_iff.mp hpmem
      subst p
      exact ⟨ha.1, ha.2.trans hbulk⟩)
  have ht : Tendsto (fun H : ℝ => C * Real.exp (-γ * H)) atTop (nhds 0) := by
    have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hγ)
    simpa only [Function.comp_def, id_eq, neg_mul, mul_zero] using hexp.const_mul C
  have hdiff : Tendsto (fun H : ℝ => reflectionBarR P γ α B Z -
      (∫⁻ ω, (twoSidedReflectionCutMass γ H B Z ω) ^ (reflectionExponent γ α) ∂P).toReal)
      atTop (nhds 0) := by
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
      exact (hb _ (mem_singleton _) _ (mem_singleton _) H hH).1
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
      exact (hb _ (mem_singleton _) _ (mem_singleton _) H hH).2
    · exact ht
  have hlimit := (tendsto_const_nhds (x := reflectionBarR P γ α B Z)).sub hdiff
  simpa only [sub_sub_cancel, sub_zero] using hlimit

end DOZZ.Proofs
