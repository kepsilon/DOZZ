/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ChaosLawFDDLimit

/-! Correlated finite test selection in the pin-copy limit passage. -/

@[expose] public section

open MeasureTheory Filter Topology

namespace DOZZ.Proofs

/-- Choosing a test from a finite family, even using the source outcome, preserves its limit.
No independence between the choice and the cutoff chaos is required. -/
theorem tendstoInMeasure_finite_selection
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (f : ℕ → Ω → ι → ℝ) (g : Ω → ι → ℝ) (choice : Ω → ι)
    (hcoord : ∀ i, TendstoInMeasure P (fun n ω => f n ω i) atTop (fun ω => g ω i)) :
    TendstoInMeasure P (fun n ω => f n ω (choice ω)) atTop (fun ω => g ω (choice ω)) := by
  have hv := tendstoInMeasure_pi_finite P f g hcoord
  rw [tendstoInMeasure_iff_norm] at hv ⊢
  intro ε hε
  have hsubset n : {ω | ε ≤ ‖f n ω (choice ω) - g ω (choice ω)‖} ⊆
      {ω | ε ≤ ‖f n ω - g ω‖} := by
    intro ω hω
    exact hω.trans (norm_le_pi_norm (f n ω - g ω) (choice ω))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hv ε hε)
    (fun _ => zero_le) (fun n => measure_mono (hsubset n))


end DOZZ.Proofs
