/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GMCRandomExponentialTest

/-! Retaining actual GFF and GMC witnesses on the independent pin-copy space. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

theorem tendstoInMeasure_measurePreserving
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (T : Ω' → Ω) (hT : MeasurePreserving T P' P)
    (f : ι → Ω → ℝ) (g : Ω → ℝ) (l : Filter ι) (h : TendstoInMeasure P f l g) :
    TendstoInMeasure P' (fun i ω => f i (T ω)) l (fun ω => g (T ω)) := by
  intro ε hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ => zero_le) (fun i => hT.measure_preimage_le {ω | ε ≤ edist (f i ω) (g ω)})

theorem isEquatorGFF_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P']
    (T : Ω' → Ω) (hT : MeasurePreserving T P' P) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) : IsEquatorGFF P' (X ∘ T) := by
  refine ⟨inferInstance, fun f => ?_⟩
  obtain ⟨hm, v, hv, hl⟩ := hX.2 f
  refine ⟨hm.comp hT.measurable, v, hv, ?_⟩
  change P'.map ((fun ω => X ω f) ∘ T) = _
  rw [← Measure.map_map hm hT.measurable, hT.map_eq, hl]

theorem isCircleAverage_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (T : Ω' → Ω) (hT : MeasurePreserving T P' P)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsCircleAverage P' (X ∘ T) (Xc ∘ T) := by
  refine ⟨fun r => (hc.1 r).comp ((hT.measurable.comp measurable_fst).prodMk measurable_snd),
    fun x r => (hc.2.1 x r).comp_measurePreserving hT, ?_⟩
  intro x r f hf
  have heq (n : ℕ) : eLpNorm (fun ω => X (T ω) (f n) - Xc (T ω) x r) 2 P' =
      eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P :=
    eLpNorm_comp_measurePreserving (((hX.2 (f n)).1.sub
      ((hc.1 r).comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable) hT
  simpa only [Function.comp_def, heq] using hc.2.2 x r f hf

theorem regularizedGMC_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (T : Ω' → Ω) (hT : MeasurePreserving T P' P)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ r : ℝ) (ω : Ω') :
    regularizedGMC P' (Xc ∘ T) γ r ω = regularizedGMC P Xc γ r (T ω) := by
  have hv (x : ℂ) : (∫ ω', Xc (T ω') x r ^ 2 ∂P') = ∫ ω', Xc ω' x r ^ 2 ∂P :=
    by
      rw [← hT.map_eq]
      exact (integral_map hT.aemeasurable
        (((hc.1 r).comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable).symm
  unfold regularizedGMC
  simp only [Function.comp_def, hv]

theorem isGMCOf_measurePreserving
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (T : Ω' → Ω) (hT : MeasurePreserving T P' P)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    IsGMCOf P' (X ∘ T) γ (M ∘ T) := by
  obtain ⟨hf, Xc, hc, hconv⟩ := hM
  refine ⟨fun ω => hf (T ω), Xc ∘ T,
    isCircleAverage_measurePreserving P P' T hT X Xc hX hc, fun f => ?_⟩
  have h := tendstoInMeasure_measurePreserving P P' T hT _ _ atTop (hconv f)
  change TendstoInMeasure P' (fun r ω => ∫ x, f x ∂regularizedGMC P' (Xc ∘ T) γ r ω)
    atTop (fun ω => ∫ x, f x ∂M (T ω))
  simpa only [regularizedGMC_measurePreserving P P' T hT X Xc hc] using h


end DOZZ.Proofs
