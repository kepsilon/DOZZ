/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.LastCutSqueeze
/-! The maximum-dependent cut bounds on the actual supplied conditioned carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual reflection pair supplies the cut sandwich for an independently sampled real
maximum, with the measurable-version transport handling the variable-level null event. -/
theorem reflected_random_reflection_cut_squeeze_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [SFinite μ] (γ ν : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν)
    (B₀ : Measure BrownianPath) [SFinite B₀]
    (hB₀ : IsBrownianReal (fun t p => p t) B₀) (hν : 0 < ν)
    (H : ℝ≥0) (hH : 0 < (H : ℝ)) :
    ∀ᵐ v : ℝ × Ω ∂μ.prod P, (H : ℝ) ≤ v.1 →
      twoSidedReflectionCutMass γ H B Z v.2 ≤
        twoSidedReflectionCutMass γ v.1 B Z v.2 ∧
      twoSidedReflectionCutMass γ v.1 B Z v.2 ≤ twoSidedReflectionMass γ B Z v.2 := by
  let f : Ω → BrownianPath := fun ω => (B ω).2
  have hf : AEMeasurable f P := hB.2.1.1
  let f' := hf.mk f
  have hfm : Measurable f' := hf.measurable_mk
  have hmap : P.map f' = P.map f := (Measure.map_congr hf.ae_eq_mk).symm
  have hpf : MeasurePreserving f' P (P.map f) := ⟨hfm,hmap⟩
  have hpm : MeasurePreserving Real.toNNReal μ (μ.map Real.toNNReal) :=
    ⟨continuous_real_toNNReal.measurable,rfl⟩
  have hprod := hpm.prod hpf
  have htime := reflected_conditioned_random_lastExit_squeeze (μ.map Real.toNNReal)
    hB.2.1.2 hB₀ hν H hH
  have hpull := hprod.quasiMeasurePreserving.ae htime
  have heq := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := P)).ae hf.ae_eq_mk
  filter_upwards [hpull,heq] with v hv he hvH
  have hm : H ≤ Real.toNNReal v.1 := by
    exact_mod_cast (show (H : ℝ) ≤ max v.1 0 from hvH.trans (le_max_left _ _))
  have hm0 : 0 ≤ v.1 := hH.le.trans hvH
  have hl := hv hm
  change negativeLastExitTime (f' v.2) H ≤
    negativeLastExitTime (f' v.2) (Real.toNNReal v.1) at hl
  change f v.2 = f' v.2 at he
  rw [← he,Real.coe_toNNReal v.1 hm0] at hl
  exact ⟨reflected_cutMass_mono_of_lastExit γ H v.1 B Z v.2 hl,
    twoSidedReflectionCutMass_le_mass γ v.1 B Z v.2⟩

end DOZZ.Proofs
