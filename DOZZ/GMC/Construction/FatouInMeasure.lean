/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Fatou's lemma transfers uniform nonnegative expectation bounds through convergence in measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- If real random variables converge in measure and their positive-part expectations are uniformly
bounded, the limiting positive-part expectation has the same bound. -/
theorem lintegral_ofReal_limit_le_of_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℝ → Ω → ℝ) (G : Ω → ℝ) (C : ℝ≥0∞)
    (hFmeas : ∀ r, Measurable (F r))
    (hT : TendstoInMeasure P F atTop G)
    (hbound : ∀ r, ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤ C := by
  obtain ⟨ns, hns, hae⟩ := hT.exists_seq_tendsto_ae'
  let Q : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (F (ns n) ω)
  have hQmeas : ∀ n, Measurable (Q n) := fun n =>
    ENNReal.measurable_ofReal.comp (hFmeas (ns n))
  have hQlim : ∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (𝓝 (ENNReal.ofReal (G ω))) := by
    filter_upwards [hae] with ω hω
    exact ENNReal.tendsto_ofReal hω
  have hliminf : (fun ω => liminf (fun n => Q n ω) atTop) =ᵐ[P]
      fun ω => ENNReal.ofReal (G ω) := by
    filter_upwards [hQlim] with ω hω
    exact hω.liminf_eq
  calc
    ∫⁻ ω, ENNReal.ofReal (G ω) ∂P =
        ∫⁻ ω, liminf (fun n => Q n ω) atTop ∂P := by
          exact lintegral_congr_ae hliminf.symm
    _ ≤ liminf (fun n => ∫⁻ ω, Q n ω ∂P) atTop := lintegral_liminf_le hQmeas
    _ ≤ C := liminf_le_of_frequently_le' <| Frequently.of_forall fun n => by
      simpa [Q] using hbound (ns n)

end DOZZ.Proofs
