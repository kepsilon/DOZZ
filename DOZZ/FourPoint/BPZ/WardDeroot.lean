/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardMixed
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! # Signed cutoff rooting

The cutoff rooting identity for real functionals: if the functional is absolutely integrable
against the cutoff chaos, its expectation equals the reference-measure integral of the rooted
expectation. The proof applies the nonnegative identity to the positive and negative parts. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pointwise rooted expectation of a nonnegative functional, written through the cutoff
density: it is measurable in the root. -/
theorem bpz_cutoff_root_lintegral_eq (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (H : ℂ → Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hHx : ∀ x, Measurable (fun q : Measure ℂ × Measure ℂ => H x q.1 q.2)) (x : ℂ) :
    ∫⁻ ω, H x ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
        ((M ω).withDensity (bpzLimRootDensity γ r x)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)) *
        H x (regularizedGMC P Xc γ r ω) (M ω) ∂P :=
  (bpz_cutoff_root_tilt P X hX hγ hγ2 M hM Xc hXc r x (H x) (hHx x)).symm

/-- The rooted expectation of a nonnegative functional is measurable in the root. -/
theorem measurable_bpz_cutoff_root_lintegral (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (H : ℂ → Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hHm : Measurable (fun p : Ω × ℂ => H p.2 (regularizedGMC P Xc γ r p.1) (M p.1)))
    (hHx : ∀ x, Measurable (fun q : Measure ℂ × Measure ℂ => H x q.1 q.2)) :
    Measurable (fun x => ∫⁻ ω, H x ((regularizedGMC P Xc γ r ω).withDensity
      (bpzCutRootDensity γ r x)) ((M ω).withDensity (bpzLimRootDensity γ r x)) ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  simp_rw [bpz_cutoff_root_lintegral_eq P X hX hγ hγ2 M hM Xc hXc r H hHx]
  have hVm := measurable_bpz_circle_variance P Xc hXc.1 r
  have hdens : Measurable (fun p : Ω × ℂ => ENNReal.ofReal (Real.exp (γ * Xc p.1 p.2 r -
      γ ^ 2 / 2 * ∫ ω', Xc ω' p.2 r ^ 2 ∂P))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (((hXc.1 r).const_mul γ).sub
      ((hVm.comp measurable_snd).const_mul _)))
  exact ((hdens.mul hHm).comp measurable_swap).lintegral_prod_right'

/-- Integrals of jointly measurable integrands against the cutoff chaos are measurable. -/
theorem measurable_lintegral_regularizedGMC (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (G : Ω × ℂ → ℝ≥0∞) (hG : Measurable G) :
    Measurable (fun ω => ∫⁻ x, G (ω, x) ∂regularizedGMC P Xc γ r ω) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hVm := measurable_bpz_circle_variance P Xc hXc.1 r
  set dens : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * ∫ ω', Xc ω' p.2 r ^ 2 ∂P) *
      normPlus p.2 ^ (-4 : ℝ)) with hdens
  have hdm : Measurable dens := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact Real.measurable_exp.comp (((hXc.1 r).const_mul γ).sub
        ((hVm.comp measurable_snd).const_mul _))
    · exact (bpz_measurable_normPlus.comp measurable_snd).pow_const _
  have heq : ∀ ω, ∫⁻ x, G (ω, x) ∂regularizedGMC P Xc γ r ω = ∫⁻ x, dens (ω, x) * G (ω, x) := by
    intro ω
    change ∫⁻ x, G (ω, x) ∂(volume.withDensity fun x => dens (ω, x)) = _
    have hd : Measurable fun x => dens (ω, x) := hdm.comp (measurable_const.prodMk measurable_id)
    have hg : Measurable fun x => G (ω, x) := hG.comp (measurable_const.prodMk measurable_id)
    rw [lintegral_withDensity_eq_lintegral_mul _ hd hg]
    rfl
  simp_rw [heq]
  exact (hdm.mul hG).lintegral_prod_right'

/-- The signed cutoff rooting identity. -/
theorem bpz_cutoff_deroot_real (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (hMm : Measurable M) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ)
    (F : ℂ → Measure ℂ → Measure ℂ → ℝ)
    (hFm : Measurable (fun p : Ω × ℂ => F p.2 (regularizedGMC P Xc γ r p.1) (M p.1)))
    (hFx : ∀ x, Measurable (fun q : Measure ℂ × Measure ℂ => F x q.1 q.2))
    (hint : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |F x (regularizedGMC P Xc γ r ω) (M ω)|
      ∂regularizedGMC P Xc γ r ω ∂P < ⊤) :
    ∫ ω, ∫ x, F x (regularizedGMC P Xc γ r ω) (M ω) ∂regularizedGMC P Xc γ r ω ∂P =
      ∫ x, normPlus x ^ (-4 : ℝ) *
        ∫ ω, F x ((regularizedGMC P Xc γ r ω).withDensity (bpzCutRootDensity γ r x))
          ((M ω).withDensity (bpzLimRootDensity γ r x)) ∂P := by
  let _ : IsProbabilityMeasure P := hX.1
  set Mr : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω with hMr
  set T₁ : ℂ → Ω → Measure ℂ := fun x ω => (Mr ω).withDensity (bpzCutRootDensity γ r x)
  set T₂ : ℂ → Ω → Measure ℂ := fun x ω => (M ω).withDensity (bpzLimRootDensity γ r x)
  set Hp : ℂ → Measure ℂ → Measure ℂ → ℝ≥0∞ := fun x m₁ m₂ => ENNReal.ofReal (F x m₁ m₂)
  set Hn : ℂ → Measure ℂ → Measure ℂ → ℝ≥0∞ := fun x m₁ m₂ => ENNReal.ofReal (-F x m₁ m₂)
  have hHpm : Measurable (fun p : Ω × ℂ => Hp p.2 (Mr p.1) (M p.1)) :=
    ENNReal.measurable_ofReal.comp hFm
  have hHnm : Measurable (fun p : Ω × ℂ => Hn p.2 (Mr p.1) (M p.1)) :=
    ENNReal.measurable_ofReal.comp hFm.neg
  have hHpx : ∀ x, Measurable (fun q : Measure ℂ × Measure ℂ => Hp x q.1 q.2) :=
    fun x => ENNReal.measurable_ofReal.comp (hFx x)
  have hHnx : ∀ x, Measurable (fun q : Measure ℂ × Measure ℂ => Hn x q.1 q.2) :=
    fun x => ENNReal.measurable_ofReal.comp (hFx x).neg
  have hp := bpz_cutoff_deroot P X hX hγ hγ2 M hM Xc hXc r Hp hHpm hHpx
  have hn := bpz_cutoff_deroot P X hX hγ hγ2 M hM Xc hXc r Hn hHnm hHnx
  have habs : ∀ ω x, ENNReal.ofReal |F x (Mr ω) (M ω)| =
      Hp x (Mr ω) (M ω) + Hn x (Mr ω) (M ω) := by
    intro ω x
    simp only [Hp, Hn]
    rcases le_total 0 (F x (Mr ω) (M ω)) with h | h
    · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero]
    · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
  -- finiteness of the two parts
  have hApm : Measurable (fun ω => ∫⁻ x, Hp x (Mr ω) (M ω) ∂Mr ω) :=
    measurable_lintegral_regularizedGMC P X hX Xc hXc γ r (fun p => Hp p.2 (Mr p.1) (M p.1))
      hHpm
  have hAnm : Measurable (fun ω => ∫⁻ x, Hn x (Mr ω) (M ω) ∂Mr ω) :=
    measurable_lintegral_regularizedGMC P X hX Xc hXc γ r (fun p => Hn p.2 (Mr p.1) (M p.1))
      hHnm
  have hAp : ∫⁻ ω, ∫⁻ x, Hp x (Mr ω) (M ω) ∂Mr ω ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun x => ?_) hint
    rw [habs]; exact le_self_add
  have hAn : ∫⁻ ω, ∫⁻ x, Hn x (Mr ω) (M ω) ∂Mr ω ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun x => ?_) hint
    rw [habs]; exact le_add_self
  -- the left side
  have hfinω : ∀ᵐ ω ∂P, ∫⁻ x, ENNReal.ofReal |F x (Mr ω) (M ω)| ∂Mr ω < ⊤ := by
    have hm : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal |F x (Mr ω) (M ω)| ∂Mr ω) :=
      measurable_lintegral_regularizedGMC P X hX Xc hXc γ r
        (fun p => ENNReal.ofReal |F p.2 (Mr p.1) (M p.1)|)
        (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hFm))
    exact ae_lt_top hm hint.ne
  have hLHS : ∫ ω, ∫ x, F x (Mr ω) (M ω) ∂Mr ω ∂P =
      (∫⁻ ω, ∫⁻ x, Hp x (Mr ω) (M ω) ∂Mr ω ∂P).toReal -
        (∫⁻ ω, ∫⁻ x, Hn x (Mr ω) (M ω) ∂Mr ω ∂P).toReal := by
    have hcongr : (fun ω => ∫ x, F x (Mr ω) (M ω) ∂Mr ω) =ᵐ[P]
        fun ω => (∫⁻ x, Hp x (Mr ω) (M ω) ∂Mr ω).toReal -
          (∫⁻ x, Hn x (Mr ω) (M ω) ∂Mr ω).toReal := by
      filter_upwards [hfinω] with ω hω
      have hmeas : Measurable fun x => F x (Mr ω) (M ω) :=
        hFm.comp (measurable_const.prodMk measurable_id)
      have hI : Integrable (fun x => F x (Mr ω) (M ω)) (Mr ω) := by
        refine ⟨hmeas.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_norm]
        simpa only [Real.norm_eq_abs] using hω
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI
    have e1 := integral_toReal hApm.aemeasurable (ae_lt_top hApm hAp.ne)
    have e2 := integral_toReal hAnm.aemeasurable (ae_lt_top hAnm hAn.ne)
    rw [integral_congr_ae hcongr, integral_sub
      (integrable_toReal_of_lintegral_ne_top hApm.aemeasurable hAp.ne)
      (integrable_toReal_of_lintegral_ne_top hAnm.aemeasurable hAn.ne), e1, e2]
  -- the right side
  have hBpm := measurable_bpz_cutoff_root_lintegral P X hX hγ hγ2 M hM Xc hXc r Hp hHpm hHpx
  have hBnm := measurable_bpz_cutoff_root_lintegral P X hX hγ hγ2 M hM Xc hXc r Hn hHnm hHnx
  have hcoef_pos : ∀ x : ℂ, ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) ≠ 0 := by
    intro x
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (bpz_normPlus_pos x) _)).ne'
  set c : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) with hc
  have hcm : Measurable c := ENNReal.measurable_ofReal.comp (bpz_measurable_normPlus.pow_const _)
  have hBpm' : Measurable fun x => c x * ∫⁻ ω, Hp x (T₁ x ω) (T₂ x ω) ∂P := hcm.mul hBpm
  have hBnm' : Measurable fun x => c x * ∫⁻ ω, Hn x (T₁ x ω) (T₂ x ω) ∂P := hcm.mul hBnm
  have hBp : ∫⁻ x, c x * ∫⁻ ω, Hp x (T₁ x ω) (T₂ x ω) ∂P < ⊤ := by rw [← hp]; exact hAp
  have hBn : ∫⁻ x, c x * ∫⁻ ω, Hn x (T₁ x ω) (T₂ x ω) ∂P < ⊤ := by rw [← hn]; exact hAn
  have hfinp := ae_lt_top hBpm' hBp.ne
  have hfinn := ae_lt_top hBnm' hBn.ne
  have hT₁ : ∀ x, Measurable (T₁ x) := by
    intro x
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have h : (fun ω => T₁ x ω t) = (fun μ : Measure ℂ =>
        ∫⁻ y, t.indicator (bpzCutRootDensity γ r x) y ∂μ) ∘
          (fun ω => regularizedGMC P Xc γ r ω) := by
      funext ω
      simp [T₁, Mr, withDensity_apply _ ht, lintegral_indicator ht]
    rw [h]
    exact (Measure.measurable_lintegral ((measurable_bpzCutRootDensity γ r x).indicator ht)).comp
      (regularizedGMC_measurable P X hX Xc hXc γ r)
  have hT₂ : ∀ x, Measurable (T₂ x) := by
    intro x
    refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
    have h : (fun ω => T₂ x ω t) = (fun μ : Measure ℂ =>
        ∫⁻ y, t.indicator (bpzLimRootDensity γ r x) y ∂μ) ∘ M := by
      funext ω
      simp [T₂, withDensity_apply _ ht, lintegral_indicator ht]
    rw [h]
    exact (Measure.measurable_lintegral ((measurable_bpzLimRootDensity γ r x).indicator ht)).comp
      hMm
  have hRHS : ∫ x, normPlus x ^ (-4 : ℝ) * ∫ ω, F x (T₁ x ω) (T₂ x ω) ∂P =
      (∫⁻ x, c x * ∫⁻ ω, Hp x (T₁ x ω) (T₂ x ω) ∂P).toReal -
        (∫⁻ x, c x * ∫⁻ ω, Hn x (T₁ x ω) (T₂ x ω) ∂P).toReal := by
    have hcongr : (fun x => normPlus x ^ (-4 : ℝ) * ∫ ω, F x (T₁ x ω) (T₂ x ω) ∂P) =ᵐ[volume]
        fun x => (c x * ∫⁻ ω, Hp x (T₁ x ω) (T₂ x ω) ∂P).toReal -
          (c x * ∫⁻ ω, Hn x (T₁ x ω) (T₂ x ω) ∂P).toReal := by
      filter_upwards [hfinp, hfinn] with x hxp hxn
      have hc0 : c x ≠ 0 := hcoef_pos x
      have hp' : ∫⁻ ω, Hp x (T₁ x ω) (T₂ x ω) ∂P < ⊤ := by
        rcases ENNReal.mul_lt_top_iff.mp hxp with h | h | h
        · exact h.2
        · exact absurd h hc0
        · rw [h]; exact ENNReal.zero_lt_top
      have hn' : ∫⁻ ω, Hn x (T₁ x ω) (T₂ x ω) ∂P < ⊤ := by
        rcases ENNReal.mul_lt_top_iff.mp hxn with h | h | h
        · exact h.2
        · exact absurd h hc0
        · rw [h]; exact ENNReal.zero_lt_top
      have hmeasω : Measurable fun ω => F x (T₁ x ω) (T₂ x ω) :=
        (hFx x).comp ((hT₁ x).prodMk (hT₂ x))
      have hIω : Integrable (fun ω => F x (T₁ x ω) (T₂ x ω)) P := by
        refine ⟨hmeasω.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_norm]
        simp only [Real.norm_eq_abs]
        have hsplit : ∀ ω, ENNReal.ofReal |F x (T₁ x ω) (T₂ x ω)| =
            Hp x (T₁ x ω) (T₂ x ω) + Hn x (T₁ x ω) (T₂ x ω) := by
          intro ω
          simp only [Hp, Hn]
          rcases le_total 0 (F x (T₁ x ω) (T₂ x ω)) with h | h
          · rw [abs_of_nonneg h, ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero]
          · rw [abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
        simp_rw [hsplit]
        have hmHp : Measurable fun ω => Hp x (T₁ x ω) (T₂ x ω) :=
          ENNReal.measurable_ofReal.comp hmeasω
        rw [lintegral_add_left hmHp]
        exact ENNReal.add_lt_top.mpr ⟨hp', hn'⟩
      rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hIω, ENNReal.toReal_mul,
        ENNReal.toReal_mul, hc, ENNReal.toReal_ofReal (Real.rpow_nonneg
          (bpz_normPlus_pos x).le _)]
      ring
    have e1 := integral_toReal hBpm'.aemeasurable hfinp
    have e2 := integral_toReal hBnm'.aemeasurable hfinn
    rw [integral_congr_ae hcongr, integral_sub
      (integrable_toReal_of_lintegral_ne_top hBpm'.aemeasurable hBp.ne)
      (integrable_toReal_of_lintegral_ne_top hBnm'.aemeasurable hBn.ne), e1, e2]
  change ∫ ω, ∫ x, F x (Mr ω) (M ω) ∂Mr ω ∂P =
    ∫ x, normPlus x ^ (-4 : ℝ) * ∫ ω, F x (T₁ x ω) (T₂ x ω) ∂P
  rw [hLHS, hRHS, hp, hn]

end DOZZ.Proofs
