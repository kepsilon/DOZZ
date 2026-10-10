/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-! Pole-free multiplication turning the unit-volume residue into the full three-to-two
residue. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The full moment formula is exactly Gamma times the unit-volume moment, including the
normalization. This algebra does not divide by Gamma at a totalized pole. -/
theorem residue_structureConstant_eq_unitVolume
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ μ a b c : ℝ) :
    structureConstant P M γ μ a b c =
      μ ^ (-sExp γ a b c) * Real.Gamma (sExp γ a b c) *
        unitVolumeStructureConstant P M γ a b c := by
  unfold structureConstant unitVolumeStructureConstant
  ring

/-- The full three-to-two residue follows from the literal unit-volume residue on its pole-free
domain. -/
theorem residue_full_limit_of_unit_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ μ α2 α3 : ℝ) (hγ : 0 < γ) (hμ : 0 < μ) (hα3 : α3 < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hPole : ReflectionPoleFree γ α3)
    (hunit : Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
      (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 * reflectionBarR P γ α3 B Z))) :
    Tendsto (fun ε : ℝ => ε * structureConstant P M γ μ
      (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionR P γ μ α3 B Z)) := by
  let p : ℝ := reflectionExponent γ α3
  have hp : 0 < p := div_pos (mul_pos (by norm_num) (sub_pos.mpr hα3)) hγ
  have hnoPole : ∀ n : ℕ, -p ≠ -(n : ℝ) := by
    intro n hn
    have hh : p = (n : ℝ) := by linarith only [hn]
    cases n with
    | zero => simp only [Nat.cast_zero] at hh; linarith only [hp, hh]
    | succ n => exact hPole n (by simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hh)
  have hs (ε : ℝ) : sExp γ (α3 - α2 + ε) α2 α3 = -p + ε / γ := by
    dsimp only [p]
    unfold sExp reflectionExponent
    ring
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hslim : Tendsto (fun ε : ℝ => sExp γ (α3 - α2 + ε) α2 α3) (𝓝[>] 0) (𝓝 (-p)) := by
    simpa only [hs, zero_div, add_zero] using tendsto_const_nhds.add (he.div_const γ)
  have hGamma := (Real.differentiableAt_Gamma hnoPole).continuousAt.tendsto.comp hslim
  have hmu := (Real.continuous_const_rpow hμ.ne').continuousAt.tendsto.comp hslim.neg
  have hprod := (hmu.mul hGamma).mul hunit
  convert hprod using 1
  · ext ε
    rw [residue_structureConstant_eq_unitVolume]
    dsimp only [Function.comp_def]
    ring_nf
  · dsimp only [p]
    unfold reflectionR
    simp only [neg_neg]
    ring_nf

end DOZZ.Proofs
