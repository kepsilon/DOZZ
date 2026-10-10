/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedWilliamsLaw
public import DOZZ.Brownian.LateralTranslation
import Mathlib.Tactic
/-! Replacing only the independent inner lateral copy preserves the correlated outer past. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A change of lateral version with identical measure law leaves the copied polar observable
and its entire outer-past mark unchanged. -/
theorem reflected_copied_polar_law_congr
    {Ω ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace ζ]
    (P : Measure Ω) [IsProbabilityMeasure P] (γ ν : ℝ)
    (Y : Ω → ζ) (D : Ω → BrownianPath) (Z Z' : Ω → Measure ℝ)
    (hY : AEMeasurable Y P) (hD : AEMeasurable D P)
    (hZ : AEMeasurable Z P) (hZ' : AEMeasurable Z' P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤)
    (hfin' : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z' ω (Icc a b) < ⊤)
    (hlaw : P.map Z' = P.map Z) :
    (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp
        (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0) ∂Z' ω.2)) =
    (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp
        (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0) ∂Z ω.2)) := by
  let F := reflectedInwardPolarMassCode γ ν
  let H : (ζ × BrownianPath) × Measure ℝ → ζ × ℝ≥0∞ := fun p => (p.1.1, F (p.1.2,p.2))
  have hF : Measurable F := reflected_measurable_inwardPolarMassCode γ ν
  have hH : Measurable H := (measurable_fst.comp measurable_fst).prodMk
    (hF.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hp (W : Ω → Measure ℝ) (hW : AEMeasurable W P)
      (hf : ∀ᵐ ω ∂P, ∀ a b : ℝ, W ω (Icc a b) < ⊤) :
      (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
        (if 0 < t then ENNReal.ofReal (Real.exp
          (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0) ∂W ω.2)) =
      ((P.map (fun ω => (Y ω,D ω))).prod (P.map W)).map H := by
    have hpack : AEMeasurable (fun ω : Ω × Ω => ((Y ω.1,D ω.1),W ω.2)) (P.prod P) :=
      ((hY.prodMk hD).comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
        (hW.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)
    have he : (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
        (if 0 < t then ENNReal.ofReal (Real.exp
          (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0) ∂W ω.2)) =ᵐ[P.prod P]
        fun ω => H ((Y ω.1,D ω.1),W ω.2) := by
      filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hf] with ω hω
      exact Prod.ext rfl (reflected_inwardPolarMassCode_eq γ ν (D ω.1) (W ω.2) hω).symm
    rw [Measure.map_congr he]
    change (P.prod P).map (H ∘ fun ω : Ω × Ω => ((Y ω.1,D ω.1),W ω.2)) = _
    rw [← AEMeasurable.map_map_of_aemeasurable hH.aemeasurable hpack,
      reflected_map_prod_ae P (fun ω => (Y ω,D ω)) W (hY.prodMk hD) hW]
  rw [hp Z' hZ' hfin', hp Z hZ hfin, hlaw]

/-- Deterministic translation of the independent inner lateral copy leaves the Williams law
and its correlated outer-past mark unchanged. -/
theorem reflected_copied_translated_williams_joint_law
    {Ω ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace ζ]
    (P : Measure Ω) (D : Ω → BrownianPath) (hD : AEMeasurable D P)
    (hB : IsBrownianReal (fun t p => p t) (P.map D))
    (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hDZ : IndepFun D Z P) (Y : Ω → ζ) (hY : AEMeasurable Y P)
    (hYD : IndepFun Y D P) (ν : ℝ) (hν : 0 < ν)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν) (T : ℝ≥0) :
    (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp
        (γ * (D ω.1 (Real.toNNReal t) - ν * t))) else 0) ∂(Z ω.2).map (fun s => s - (T : ℝ)))) =
      (P.map Y).prod
        ((((((brownianMaximumReferenceLaw ν).prod Qν).map
          (fun v => (v.1, negativeConditionedLastExitSegment v.1 v.2))).prod Qν).prod
            (P.map Z)).map (williamsMassFunctional γ)) := by
  let _ : IsProbabilityMeasure P := hZ.2.2.1
  let ZT := fun ω => (Z ω).map (fun s => s - (T : ℝ))
  have ht := lateralGMC_random_translation P γ Z hZ D hD hDZ
    (fun _ => -(T : ℝ)) measurable_const
  have hZT : AEMeasurable ZT P := by simpa only [sub_eq_add_neg, ZT] using ht.1
  have hlaw : P.map ZT = P.map Z := by simpa only [sub_eq_add_neg, ZT] using ht.2.1
  have hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, ZT ω (Icc a b) < ⊤ := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω a b
    have he : (fun s : ℝ => s - (T : ℝ)) ⁻¹' Icc a b = Icc (a+T) (b+T) := by
      ext s
      simp only [mem_preimage, mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add]
    change (Z ω).map (fun s => s - (T : ℝ)) (Icc a b) < ⊤
    rw [Measure.map_apply (show Measurable (fun s : ℝ => s - (T : ℝ)) from measurable_id.sub_const _) measurableSet_Icc, he]
    exact hω _ _
  exact (reflected_copied_polar_law_congr P γ ν Y D Z ZT hY hD hZ.2.2.2.1 hZT
    hZ.2.2.2.2.1 hfin hlaw).trans
      (reflected_copied_williams_joint_law P D hD hB γ Z hZ hDZ Y hY hYD ν hν Qν hQν)

end DOZZ.Proofs
