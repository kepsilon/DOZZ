/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Tails.WilliamsInputCode
/-! Joint measurability of the maximum-dependent reflection cut mass. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_williams_variable_cut_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) :
    AEMeasurable (fun v : ℝ × Ω => twoSidedReflectionCutMass γ v.1 B Z v.2) (μ.prod P) := by
  have hpair := (hB.prodMk hZ).comp_quasiMeasurePreserving
    (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving
  have hcode := (measurable_williamsCutMassCode γ).comp_aemeasurable
    (measurable_fst.aemeasurable.prodMk hpair)
  apply hcode.congr
  filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hfin] with v hv
  exact williamsCutMassCode_eq γ v.1 (B v.2) (Z v.2) hv

end DOZZ.Proofs
