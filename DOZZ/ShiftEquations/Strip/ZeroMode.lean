/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.StructureConstant
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The Gamma-pole normalization in the lastone structure-constant limit. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The zero-mode exponent on the lastone charge line. -/
theorem lastone_sExp (γ ε δ : ℝ) :
    sExp γ ε (Q γ - δ) (Q γ - ε) = -δ / γ := by
  unfold sExp
  congr 1
  ring

/-- The zero-mode factor contributes `-2`; the critical Coulomb moment must contribute `2`. -/
theorem lastone_zeroMode_limit (γ μ : ℝ) (hγ : 0 < γ) (hμ : 0 < μ) :
    Tendsto (fun δ : ℝ => δ * (2 * μ ^ (δ / γ) / γ * Real.Gamma (-δ / γ)))
      (𝓝[>] 0) (𝓝 (-2)) := by
  have hd : Tendsto (fun δ : ℝ => δ / γ) (𝓝[>] 0) (𝓝 0) := by
    have h0 := ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 0) (𝓝 0)).div_const γ).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using h0
  have hμpow : Tendsto (fun δ : ℝ => μ ^ (δ / γ)) (𝓝[>] 0) (𝓝 1) := by
    simp_rw [Real.rpow_def_of_pos hμ]
    simpa [Function.comp_def] using
      Real.continuous_exp.continuousAt.tendsto.comp (hd.const_mul (Real.log μ))
  have hΓcont : ContinuousAt Real.Gamma (1 : ℝ) := by
    apply (Real.differentiableAt_Gamma _).continuousAt
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hΓ : Tendsto (fun δ : ℝ => Real.Gamma (-δ / γ + 1)) (𝓝[>] 0) (𝓝 1) := by
    have ha : Tendsto (fun δ : ℝ => -δ / γ + 1) (𝓝[>] 0) (𝓝 1) := by
      simpa only [neg_zero, zero_add, neg_div] using hd.neg.add_const 1
    simpa only [Function.comp_def, Real.Gamma_one] using hΓcont.tendsto.comp ha
  have hlim : Tendsto (fun δ : ℝ => -2 * μ ^ (δ / γ) * Real.Gamma (-δ / γ + 1))
      (𝓝[>] 0) (𝓝 (-2)) := by
    simpa using (hμpow.const_mul (-2)).mul hΓ
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδpos : 0 < δ := hδ
  have hrec := Real.Gamma_add_one (neg_ne_zero.mpr (div_pos hδpos hγ).ne')
  rw [← neg_div] at hrec
  rw [hrec]
  field_simp

/-- Exact reduction of the lastone structure-constant limit to its critical small-power
Coulomb moment. The arbitrary supplied probability space is preserved. -/
theorem lastone_structureConstant_limit_of_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (γ μ ε : ℝ) (hγ : 0 < γ) (hμ : 0 < μ)
    (hmoment : Tendsto (fun δ : ℝ =>
      (∫⁻ ω, rho γ (M ω) ε (Q γ - δ) (Q γ - ε) ^ (δ / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 2)) :
    Tendsto (fun δ : ℝ => δ * structureConstant P M γ μ ε (Q γ - δ) (Q γ - ε))
      (𝓝[>] 0) (𝓝 (-4)) := by
  have h := (lastone_zeroMode_limit γ μ hγ hμ).mul hmoment
  convert h using 1
  · ext δ
    simp only [structureConstant, lastone_sExp, neg_div, neg_neg]
    ring
  · norm_num

end DOZZ.Proofs
