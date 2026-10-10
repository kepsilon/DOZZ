/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.HeterogeneousCopies
public import DOZZ.FourPoint.Reflected.CopiedPolarTransport
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
/-! Signed expectations under the joint source Williams law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The translated restarted polar mass is measurable, including extended values. -/
theorem dual_translated_polar_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → BrownianPath)
    (hD : AEMeasurable D P) (γ ν : ℝ) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hDZ : IndepFun D Z P) (T : ℝ≥0) :
    AEMeasurable (fun ω : Ω × Ω => ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0)
        ∂(Z ω.2).map (fun s => s-(T : ℝ))) (P.prod P) := by
  let _ : IsProbabilityMeasure P := hZ.2.2.1
  let ZT := fun ω => (Z ω).map (fun s => s-(T : ℝ))
  have ht := lateralGMC_random_translation P γ Z hZ D hD hDZ
    (fun _ => -(T : ℝ)) measurable_const
  have hZT : AEMeasurable ZT P := by simpa only [sub_eq_add_neg, ZT] using ht.1
  have hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, ZT ω (Icc a b) < ⊤ := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω a b
    have he : (fun s : ℝ => s-(T : ℝ)) ⁻¹' Icc a b = Icc (a+T) (b+T) := by
      ext s
      simp only [mem_preimage, mem_Icc, le_sub_iff_add_le, sub_le_iff_le_add]
    change (Z ω).map (fun s => s-(T : ℝ)) (Icc a b) < ⊤
    rw [Measure.map_apply (show Measurable (fun s : ℝ => s-(T : ℝ)) from
      measurable_id.sub_const _) measurableSet_Icc, he]
    exact hω _ _
  have hpair : AEMeasurable (fun ω : Ω × Ω => (D ω.1,ZT ω.2)) (P.prod P) :=
    hD.comp_fst.prodMk hZT.comp_snd
  have hm := (reflected_measurable_inwardPolarMassCode γ ν).comp_aemeasurable hpair
  apply hm.congr
  filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae hfin] with ω hω
  exact reflected_inwardPolarMassCode_eq γ ν (D ω.1) (ZT ω.2) hω

/-- A measurable signed expectation is transported by the joint law, with both source
and reference observables explicitly measurable. -/
theorem dual_copied_joint_law_integral
    {Ω Λ ζ : Type*} [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace ζ]
    (P : Measure Ω) (R : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (Y : Ω → ζ) (hY : AEMeasurable Y P) (V : Ω × Ω → ℝ≥0∞)
    (hV : AEMeasurable V (P.prod P)) (J : Λ → ℝ≥0∞) (hJ : AEMeasurable J R)
    (hLaw : (P.prod P).map (fun ω => (Y ω.1,V ω)) = (P.map Y).prod (R.map J))
    (G : ζ × ℝ≥0∞ → ℝ) (hG : Measurable G) :
    (∫ ω : Ω × Ω, G (Y ω.1,V ω) ∂P.prod P) =
      ∫ ω : Ω × Λ, G (Y ω.1,J ω.2) ∂P.prod R := by
  have hs : AEMeasurable (fun ω : Ω × Ω => (Y ω.1,V ω)) (P.prod P) := hY.comp_fst.prodMk hV
  have hr : AEMeasurable (fun ω : Ω × Λ => (Y ω.1,J ω.2)) (P.prod R) := hY.comp_fst.prodMk hJ.comp_snd
  rw [← dual_independent_copy_map_law P R Y J hY hJ] at hLaw
  rw [← integral_map hs hG.aestronglyMeasurable,
    ← integral_map hr hG.aestronglyMeasurable, hLaw]

end DOZZ.Proofs
