/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! L¹ convergence passes finite-cutoff comparisons through Lipschitz tests. -/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal

namespace DOZZ.Proofs

/-- Passage of a finite-cutoff Kahane comparison through `L¹` convergence for Lipschitz tests.
Applying this to the convex truncations `F_R` and then increasing `R` gives the positive power
part of the limit comparison. -/
theorem kahane_limit_lipschitz
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Xr : ℕ → ΩX → ℝ) (Yr : ℕ → ΩY → ℝ) (X : ΩX → ℝ) (Y : ΩY → ℝ)
    (hX : Tendsto (fun n => eLpNorm (fun ω => Xr n ω - X ω) 1 PX) atTop (𝓝 0))
    (hY : Tendsto (fun n => eLpNorm (fun ω => Yr n ω - Y ω) 1 PY) atTop (𝓝 0))
    (F : ℝ → ℝ) (_hF : Measurable F)
    (hLip : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, |F x - F y| ≤ C * |x - y|)
    (hIX : ∀ n, Integrable (fun ω => F (Xr n ω)) PX)
    (hIY : ∀ n, Integrable (fun ω => F (Yr n ω)) PY)
    (hI : Integrable (fun ω => F (X ω)) PX ∧ Integrable (fun ω => F (Y ω)) PY)
    (hcmp : ∀ n, ∫ ω, F (Xr n ω) ∂PX ≤ ∫ ω, F (Yr n ω) ∂PY) :
    ∫ ω, F (X ω) ∂PX ≤ ∫ ω, F (Y ω) ∂PY := by
  obtain ⟨C, hC, hLip⟩ := hLip
  have hXbound (n : ℕ) : ∀ᵐ ω ∂PX,
      ‖F (Xr n ω) - F (X ω)‖ ≤ C * ‖Xr n ω - X ω‖ := by
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using hLip (Xr n ω) (X ω)
  have hYbound (n : ℕ) : ∀ᵐ ω ∂PY,
      ‖F (Yr n ω) - F (Y ω)‖ ≤ C * ‖Yr n ω - Y ω‖ := by
    filter_upwards [] with ω
    simpa [Real.norm_eq_abs] using hLip (Yr n ω) (Y ω)
  have hXle (n : ℕ) :
      eLpNorm (fun ω => F (Xr n ω) - F (X ω)) 1 PX ≤
        ENNReal.ofReal C * eLpNorm (fun ω => Xr n ω - X ω) 1 PX := by
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((hIX n).aestronglyMeasurable.sub hI.1.aestronglyMeasurable) (hXbound n) 1
  have hYle (n : ℕ) :
      eLpNorm (fun ω => F (Yr n ω) - F (Y ω)) 1 PY ≤
        ENNReal.ofReal C * eLpNorm (fun ω => Yr n ω - Y ω) 1 PY := by
    exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((hIY n).aestronglyMeasurable.sub hI.2.aestronglyMeasurable) (hYbound n) 1
  have hCfinite : ENNReal.ofReal C ≠ ∞ := ENNReal.ofReal_ne_top
  have hXmul : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun ω => Xr n ω - X ω) 1 PX)
      atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul hX (Or.inr hCfinite))
  have hYmul : Tendsto
      (fun n => ENNReal.ofReal C * eLpNorm (fun ω => Yr n ω - Y ω) 1 PY)
      atTop (𝓝 0) := by
    simpa using (ENNReal.Tendsto.const_mul hY (Or.inr hCfinite))
  have hXdiff : Tendsto
      (fun n => eLpNorm (fun ω => F (Xr n ω) - F (X ω)) 1 PX)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hXmul
    · intro n
      exact bot_le
    · exact hXle
  have hYdiff : Tendsto
      (fun n => eLpNorm (fun ω => F (Yr n ω) - F (Y ω)) 1 PY)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hYmul
    · intro n
      exact bot_le
    · exact hYle
  have hXint : Tendsto (fun n => ∫ ω, F (Xr n ω) ∂PX) atTop
      (𝓝 (∫ ω, F (X ω) ∂PX)) := by
    exact tendsto_integral_of_L1'
      (f := fun ω => F (X ω)) (F := fun n ω => F (Xr n ω)) (l := atTop)
      (Filter.Eventually.of_forall hIX) hXdiff
  have hYint : Tendsto (fun n => ∫ ω, F (Yr n ω) ∂PY) atTop
      (𝓝 (∫ ω, F (Y ω) ∂PY)) := by
    exact tendsto_integral_of_L1'
      (f := fun ω => F (Y ω)) (F := fun n ω => F (Yr n ω)) (l := atTop)
      (Filter.Eventually.of_forall hIY) hYdiff
  exact le_of_tendsto_of_tendsto' hXint hYint hcmp

end DOZZ.Proofs
