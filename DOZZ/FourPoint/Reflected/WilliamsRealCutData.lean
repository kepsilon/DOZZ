/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.RandomCutSqueeze
public import DOZZ.FourPoint.Reflected.ReflectionCutRealMoments
public import DOZZ.Correlations.Tails.WilliamsInputCode
/-! Measurability and signed cut comparisons for the actual reflection witness. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- All maximum-dependent real cut data needed by the signed expectation squeeze are provided
by the actual supplied reflection witness and its moment theorem. -/
theorem reflected_williams_real_cut_data
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (γ α : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < Q γ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z)
    (B₀ : Measure BrownianPath) [SFinite B₀] (hB₀ : IsBrownianReal (fun t p => p t) B₀)
    (H : ℝ≥0) (hH : 0 < (H : ℝ)) :
    let J := fun v : ℝ × Ω => (twoSidedReflectionMass γ B Z v.2).toReal
    let K := fun v : ℝ × Ω => (twoSidedReflectionCutMass γ H B Z v.2).toReal
    let j := fun v : ℝ × Ω => (twoSidedReflectionCutMass γ v.1 B Z v.2).toReal
    AEMeasurable J (μ.prod P) ∧ AEMeasurable K (μ.prod P) ∧ AEMeasurable j (μ.prod P) ∧
    Integrable J (μ.prod P) ∧
    (∀ᵐ v : ℝ × Ω ∂μ.prod P, 0 ≤ j v ∧ j v ≤ J v ∧ 0 ≤ K v ∧ K v ≤ J v ∧
      ((H : ℝ) < v.1 → K v ≤ j v)) := by
  let _ : IsProbabilityMeasure P := hData.2.1.2.2.1
  let ν := Q γ-α
  have hBm := conditionedPair_aemeasurable P B ν hData.1
  have hZm := hData.2.1.2.2.2.1
  have hfin := hData.2.1.2.2.2.2.1
  have hJm := (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hBm hData.2.1).ennreal_toReal
  have hKm := (twoSidedReflectionCutMass_aemeasurable P γ H B Z hBm hZm hfin).ennreal_toReal
  have hJmp := hJm.comp_quasiMeasurePreserving
    (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving
  have hKmp := hKm.comp_quasiMeasurePreserving
    (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving
  have hpair := (hBm.prodMk hZm).comp_quasiMeasurePreserving
    (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving
  have hcode := (measurable_williamsCutMassCode γ).comp_aemeasurable
    (measurable_fst.aemeasurable.prodMk hpair)
  have hfinp := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae hfin
  have hje : (fun v : ℝ × Ω => williamsCutMassCode γ (v.1,(B v.2,Z v.2))) =ᵐ[μ.prod P]
      (fun v => twoSidedReflectionCutMass γ v.1 B Z v.2) := by
    filter_upwards [hfinp] with v hv
    exact williamsCutMassCode_eq γ v.1 (B v.2) (Z v.2) hv
  have hjm := (hcode.congr hje).ennreal_toReal
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ,hγ₂]
  have hi := (reflected_reflection_real_moment P γ α 1 B Z hα hData h4).1
  have hJi : Integrable (fun v : ℝ × Ω => (twoSidedReflectionMass γ B Z v.2).toReal) (μ.prod P) := by
    simpa only [one_mul,Real.rpow_one] using (integrable_const (1 : ℝ)).mul_prod hi
  refine ⟨hJmp,hKmp,hjm,hJi, ?_⟩
  have hcuts := reflected_random_reflection_cut_squeeze_ae P μ γ ν B Z hData.1 B₀ hB₀
    (sub_pos.mpr hα) H hH
  have htop := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae
    (reflected_reflection_mass_positive_finite_ae P γ α B Z hγ hγ₂ hα hData)
  filter_upwards [hcuts,htop] with v hv ht
  have hjJ := twoSidedReflectionCutMass_le_mass γ v.1 B Z v.2
  have hKJ := twoSidedReflectionCutMass_le_mass γ H B Z v.2
  refine ⟨ENNReal.toReal_nonneg,ENNReal.toReal_mono ht.2.ne hjJ,
    ENNReal.toReal_nonneg,ENNReal.toReal_mono ht.2.ne hKJ, ?_⟩
  intro hm
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ht.2.ne hjJ) (hv hm.le).1

end DOZZ.Proofs
