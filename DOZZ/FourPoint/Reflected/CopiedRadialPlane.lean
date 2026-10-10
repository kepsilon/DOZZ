/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalReinsertion
import Mathlib.Tactic
/-! # The actual limiting punctured-plane chaos with an independent radial copy -/
public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Independent radial reinsertion preserves every measurable radial-path and weighted-mass observable on the full
punctured plane, including extended-real masses. -/
theorem reflected_copied_radial_plane_observable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ N : Ω → Measure ℂ,
      Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity
        (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      (∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
        originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
        (fun ω => (N ω).restrict (originLateralChart ρ))) ∧
      ∀ (f : ℂ → ℝ≥0∞), Measurable f → ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (originRadialPath Xc ω, ∫⁻ x in (({0} : Set ℂ)ᶜ), f x ∂M ω) ∂P) =
      ∫⁻ ω, G (originRadialPath Xc ω.1, ∫⁻ x in (({0} : Set ℂ)ᶜ),
        f x * ENNReal.ofReal (reflected_global_reinsertionWeight γ
          (originRadialPath Xc ω.1) x) ∂N ω.2) ∂P.prod P := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hNm, hi, hfin, heq, hNa⟩ := reflected_global_lateral_admissible
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  refine ⟨N, hNm, hi, hfin, heq, hNa, ?_⟩
  intro f hf G hG
  let U : Set ℂ := ({0} : Set ℂ)ᶜ
  have hU : IsOpen U := (isClosed_singleton (x := (0 : ℂ))).isOpen_compl
  let _ : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  let K : ℕ → Set ℂ := fun n => Subtype.val '' E n
  have hK (n : ℕ) : IsCompact (K n) := (E.isCompact n).image continuous_subtype_val
  have hKU (n : ℕ) : K n ⊆ (({0} : Set ℂ)ᶜ) := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hKm : Monotone K := by
    intro n m hnm
    exact image_mono (E.subset hnm)
  have hKe : (⋃ n, K n) = (({0} : Set ℂ)ᶜ) := by
    ext x
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, hx⟩
      exact hKU n hx
    · intro hx
      obtain ⟨n, hn⟩ := E.exists_mem ⟨x, hx⟩
      exact mem_iUnion.mpr ⟨n, ⟨⟨x, hx⟩, hn, rfl⟩⟩
  let NF : Ω → ℕ → FiniteMeasure ℂ := fun ω n =>
    ⟨(N ω).restrict (K n), ⟨by simpa only [Measure.restrict_apply_univ] using
      (hfin ω (K n) (hK n) (hKU n))⟩⟩
  have hNF : Measurable NF := Measurable.of_eval fun n => Measurable.subtype_mk
    ((measurable_measure_restrict (K n) (hK n).measurableSet).comp hNm)
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hNFc : @Measurable Ω (ℕ → FiniteMeasure ℂ)
      (MeasurableSpace.comap N inferInstance) inferInstance NF := by
    let : MeasurableSpace Ω := MeasurableSpace.comap N inferInstance
    exact Measurable.of_eval fun n => Measurable.subtype_mk
      ((measurable_measure_restrict (K n) (hK n).measurableSet).comp (comap_measurable N))
  have hAN : IndepFun A NF P :=
    indep_of_indep_of_le_right hi hNFc.comap_le
  let F : TwoSidedPath × (ℕ → FiniteMeasure ℂ) → ℝ≥0∞ := fun p =>
    G (p.1, ⨆ n, ∫⁻ x, f x * ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x)
      ∂(p.2 n : Measure ℂ))
  have hF : Measurable F := by
    apply hG.comp
    apply measurable_fst.prodMk
    apply Measurable.iSup
    intro n
    exact (measurable_lintegral_finiteMeasure_parameter
      ((hf.comp measurable_snd).mul (ENNReal.measurable_ofReal.comp
        (reflected_global_reinsertionWeight_measurable γ)))).comp
          (measurable_fst.prodMk ((measurable_pi_apply n).comp measurable_snd))
  have hmass (a : TwoSidedPath) (ω : Ω) : F (a, NF ω) =
      G (a, ∫⁻ x in (({0} : Set ℂ)ᶜ), f x * ENNReal.ofReal
        (reflected_global_reinsertionWeight γ a x) ∂N ω) := by
    change G (a, ⨆ n, ∫⁻ x in K n, f x * ENNReal.ofReal
      (reflected_global_reinsertionWeight γ a x) ∂N ω) = _
    rw [← setLIntegral_iUnion_of_directed _ hKm.directed_le, hKe]
  have hid : ∀ᵐ ω ∂P, G (A ω, ∫⁻ x in (({0} : Set ℂ)ᶜ), f x ∂M ω) = F (A ω, NF ω) := by
    filter_upwards [heq] with ω he
    rw [hmass]
    have hw : Measurable (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x)) :=
      ENNReal.measurable_ofReal.comp ((reflected_global_reinsertionWeight_measurable γ).comp
        (measurable_const.prodMk measurable_id))
    have hd := lintegral_withDensity_eq_lintegral_mul ((N ω).restrict ((({0} : Set ℂ)ᶜ))) hw hf
    simp only [Pi.mul_apply, mul_comm] at hd
    rw [← hd, ← restrict_withDensity ((isClosed_singleton (x := (0 : ℂ))).isOpen_compl).measurableSet, he,
      reflected_global_reinsertion_measure,
      Measure.restrict_restrict_of_subset (Subset.refl _)]
  have hj : P.map (fun ω => (A ω, NF ω)) = (P.map A).prod (P.map NF) :=
    (indepFun_iff_map_prod_eq_prod_map_map hA hNF.aemeasurable).mp hAN
  have hAc : AEMeasurable (fun ω : Ω × Ω => A ω.1) (P.prod P) :=
    hA.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving
  have hNc : AEMeasurable (fun ω : Ω × Ω => NF ω.2) (P.prod P) :=
    hNF.aemeasurable.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving
  have hjc : (P.prod P).map (fun ω : Ω × Ω => (A ω.1, NF ω.2)) =
      (P.map A).prod (P.map NF) := by
    have hi' := (indepFun_iff_map_prod_eq_prod_map_map hAc hNc).mp
      (indepFun_prod₀ hA hNF.aemeasurable)
    have hfst : (P.prod P).map (fun ω : Ω × Ω => A ω.1) = P.map A := by
      have h := AEMeasurable.map_map_of_aemeasurable
        (show AEMeasurable A ((P.prod P).map Prod.fst) by
          simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hA)
        measurable_fst.aemeasurable
      simpa only [Function.comp_def, Measure.map_fst_prod, measure_univ, one_smul] using h.symm
    have hsnd : (P.prod P).map (fun ω : Ω × Ω => NF ω.2) = P.map NF := by
      have h := AEMeasurable.map_map_of_aemeasurable
        (show AEMeasurable NF ((P.prod P).map Prod.snd) by
          simpa only [Measure.map_snd_prod, measure_univ, one_smul] using hNF.aemeasurable)
        measurable_snd.aemeasurable
      simpa only [Function.comp_def, Measure.map_snd_prod, measure_univ, one_smul] using h.symm
    exact hi'.trans (by rw [hfst, hsnd])
  calc
    _ = ∫⁻ ω, F (A ω, NF ω) ∂P := lintegral_congr_ae hid
    _ = ∫⁻ p, F p ∂(P.map A).prod (P.map NF) := by
      rw [← hj]
      exact (lintegral_map' hF.aemeasurable (hA.prodMk hNF.aemeasurable)).symm
    _ = ∫⁻ ω : Ω × Ω, F (A ω.1, NF ω.2) ∂P.prod P := by
      rw [← hjc]
      exact lintegral_map' hF.aemeasurable (hAc.prodMk hNc)
    _ = _ := lintegral_congr fun ω => hmass (A ω.1) ω.2

end DOZZ.Proofs
