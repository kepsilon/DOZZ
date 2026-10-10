/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelCDFOrder
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of common-uniform quantiles

For a probability law, its generalized CDF inverse is monotone on uniform levels in `(0,1)`. This
makes the one-dimensional sampling map measurable with respect to the restricted uniform law.
Joint measurability in a transition kernel's starting state is a separate requirement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open Topology
open scoped Topology

namespace DOZZ.Proofs

private theorem cdf_superlevel_nonempty {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {u : ℝ} (hu : u < 1) :
    {x : ℝ | u ≤ ProbabilityTheory.cdf μ x}.Nonempty := by
  have hev : ∀ᶠ x : ℝ in atTop, u < ProbabilityTheory.cdf μ x :=
    (ProbabilityTheory.tendsto_cdf_atTop μ).eventually
      (isOpen_Ioi.mem_nhds hu)
  obtain ⟨x, hx⟩ := Filter.eventually_atTop.1 hev
  exact ⟨x, (hx x le_rfl).le⟩

private theorem cdf_superlevel_bddBelow {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {u : ℝ} (hu : 0 < u) :
    BddBelow {x : ℝ | u ≤ ProbabilityTheory.cdf μ x} := by
  have hev : ∀ᶠ x : ℝ in atBot, ProbabilityTheory.cdf μ x < u :=
    (ProbabilityTheory.tendsto_cdf_atBot μ).eventually
      (isOpen_Iio.mem_nhds hu)
  obtain ⟨a, ha⟩ := Filter.eventually_atBot.1 hev
  refine ⟨a, ?_⟩
  intro x hx
  by_contra hnot
  have hxa : x ≤ a := (lt_of_not_ge hnot).le
  exact (not_lt_of_ge hx) (ha x hxa)

/-- The generalized quantile is monotone as a function of the uniform level on `(0,1)`. -/
theorem cdfGeneralizedQuantile_monoOn_Ioo
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MonotoneOn (fun u => cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u)
      (Set.Ioo 0 1) := by
  intro u hu v hv huv
  apply csInf_le_csInf
    (cdf_superlevel_bddBelow hu.1)
    (cdf_superlevel_nonempty hv.2)
  intro x hx
  exact huv.trans hx

/-- The generalized CDF inverse is almost everywhere measurable under Lebesgue measure restricted
to `(0,1)`, hence under the standard uniform distribution. -/
theorem aemeasurable_cdfGeneralizedQuantile_Ioo
    (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    AEMeasurable (fun u => cdfGeneralizedQuantile (ProbabilityTheory.cdf μ) u)
      ((volume : Measure ℝ).restrict (Set.Ioo 0 1)) := by
  exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo
    (cdfGeneralizedQuantile_monoOn_Ioo μ)

end DOZZ.Proofs

end
