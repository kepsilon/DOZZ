/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.RandomTestApproximation
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! Passing correlated random tests to the chaos limit by uniform mean approximation. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- Uniform mean approximation by tests whose limits are already known suffices for a
random test. The test choice may depend on the same outcome as the random measure. -/
theorem tendstoInMeasure_L1_approximation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (a : ℕ → ℕ → Ω → ℝ) (b : ℕ → Ω → ℝ)
    (hconv : ∀ k, TendstoInMeasure P (a k) atTop (b k))
    (c : ℕ → ℝ≥0∞) (hc : Tendsto c atTop (𝓝 0))
    (hleftmeas : ∀ k n, AEMeasurable (fun ω => ENNReal.ofReal ‖f n ω - a k n ω‖) P)
    (hrightmeas : ∀ k, AEMeasurable (fun ω => ENNReal.ofReal ‖b k ω - g ω‖) P)
    (hleft : ∀ k n, ∫⁻ ω, ENNReal.ofReal ‖f n ω - a k n ω‖ ∂P ≤ c k)
    (hright : ∀ k, ∫⁻ ω, ENNReal.ofReal ‖b k ω - g ω‖ ∂P ≤ c k) :
    TendstoInMeasure P f atTop g := by
  apply tendstoInMeasure_uniform_approximation P f g a b hconv
  intro ε hε
  have hε0 : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨fun k => c k / ENNReal.ofReal ε, ?_, ?_, ?_⟩
  · simpa only [ENNReal.zero_div] using ENNReal.Tendsto.div_const hc (Or.inr hε0)
  · intro k n
    have heq : {ω | ε ≤ ‖f n ω - a k n ω‖} =
        {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal ‖f n ω - a k n ω‖} := by
      ext ω
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
    rw [heq]
    exact (meas_ge_le_lintegral_div (hleftmeas k n) hε0 ENNReal.ofReal_ne_top).trans
      (ENNReal.div_le_div_right (hleft k n) _)
  · intro k
    have heq : {ω | ε ≤ ‖b k ω - g ω‖} =
        {ω | ENNReal.ofReal ε ≤ ENNReal.ofReal ‖b k ω - g ω‖} := by
      ext ω
      exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).symm
    rw [heq]
    exact (meas_ge_le_lintegral_div (hrightmeas k) hε0 ENNReal.ofReal_ne_top).trans
      (ENNReal.div_le_div_right (hright k) _)


end DOZZ.Proofs
