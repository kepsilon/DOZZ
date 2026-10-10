/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TranslatedField
public import DOZZ.Brownian.Lateral.GlobalIndependence

/-! The translated source projection uses the literal off-center radial Brownian motion. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem translated_circle_jointMeasurable
    {Ω : Type*} [MeasurableSpace Ω] (Xc : Ω → ℂ → ℝ → ℝ)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) (z : ℂ) :
    Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 (z+p.2.1) p.2.2 - Xc p.1 z 0) :=
  (hm.comp (measurable_fst.prodMk
    ((measurable_const.add measurable_snd.fst).prodMk measurable_snd.snd))).sub
      (hm.comp (measurable_fst.prodMk (measurable_const (a := (z,(0 : ℝ))))))

theorem translated_circle_continuous
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) (z : ℂ) :
    ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω (z+p.1) p.2 - Xc ω z 0) := by
  filter_upwards [hcont] with ω hω
  exact (hω.comp ((continuous_const.add continuous_fst).prodMk continuous_snd)).sub
    continuous_const

/-- The literal off-center radial path and the projected translated chaos form a genuine
source projection. In particular the complete radial path is independent of the lateral chaos. -/
theorem translated_radial_sourceProjection
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N) :
    let Uc := fun ω x r => Xc ω (z+x) r - Xc ω z 0
    IsSourceLateralProjection P (translatedField X Xc z) γ N
      (fun ω => lateralProjectedGMC γ (originRadialPath Uc ω) (N ω)) ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ, originRadialPath Uc ω s = Xc ω z s - Xc ω z 0) := by
  let Uc := fun ω x r => Xc ω (z+x) r - Xc ω z 0
  have hU := translated_field_isEquatorGFF P X Xc hX hc z
  have hcU := translated_field_circleAverage P X Xc hX hc z
  have hmU := translated_circle_jointMeasurable Xc hm z
  have hcontU := translated_circle_continuous P Xc hcont z
  let A := originRadialPath Uc
  have hA := originRadialPath_aemeasurable P _ Uc hcU hcontU
  have hB := originRadialPath_isBrownian P _ Uc hU hcU hcontU
  have hZ := lateralProjectedGMC_aemeasurable P γ A hA N
    (equatorGFF_GMC_aemeasurable P _ hU γ hγ hγ2 N hN) hN.1
  have hi := lateralProjectedGMC_indep P _ Uc hU hcU hmU hcontU γ hγ hγ2 N hN
  constructor
  · refine ⟨hU, hN, A, ⟨Uc, hcU, ?_⟩, hA,
      originRadialPath_zero_ae P _ Uc hcU hcontU, hB.1, hB.2,
      originRadialPath_halves_indep P _ Uc hU hcU hcontU, hZ, hi,
      ae_of_all P (fun _ => rfl)⟩
    intro s
    exact (originRadialPath_eval_ae (Xc := Uc) hcontU).mono (fun ω hω => hω s)
  · filter_upwards [originRadialPath_eval_ae (Xc := Uc) hcontU] with ω hω s
    simpa only [Uc, add_zero] using hω s


end DOZZ.Proofs
