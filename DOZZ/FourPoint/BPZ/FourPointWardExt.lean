/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.FourPointSingular

/-! # Extension of the four-point Ward identity to limits of test functions

If compactly supported test functions `φ_n` agree eventually with `φ` near every regular point
and satisfy bounds singular only at `z`,

  `|∂_v(φ_n k̃)| ≤ A (1 + |x − z|^{-2}) k̃`,
  `|(φ_n(x) − φ_n(y)) K_v(x − y)| ≤ A (1 + |x − z|^{-2} + |y − z|^{-2})`,

then the Ward identity passes to `φ` by dominated convergence, the dominating function being
`E[I^{-q} ∫ (1 + |x − z|^{-2}) k dM] < ∞`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- Almost surely the singular weight `(1 + |x − z|^{-2}) k` is integrable and the four-point mass
is positive and finite. -/
theorem bpz_singular_integrable_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    {q : ℝ} (hq1 : 1 ≤ q) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∀ᵐ ω ∂P, Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) *
        bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x) (M ω) ∧
      0 < bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ∧ bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z < ⊤ := by
  have hfin := bpz_singular_moment_lt_top (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hχ hq1 hz0 hz1
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hgm : Measurable fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x :=
    (measurable_const.add ((measurable_id.sub measurable_const).norm.pow_const _)).mul hkm
  have hmeas : AEMeasurable (fun ω => bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) *
      ∫⁻ x, ENNReal.ofReal ((1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x)
        ∂M ω) P :=
    ((gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (ENNReal.measurable_ofReal.comp hkm)).pow_const _).mul
      (gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _ (ENNReal.measurable_ofReal.comp hgm))
  have hae := ae_lt_top' hmeas hfin.ne
  filter_upwards [hae, bpzMass_pos_ae P X hX hγ hγ2 M hM 0 le_rfl zero_le_one z,
    bpzMass_lt_top_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ 0 z hz0 hz1] with ω h1 h2 h3
  refine ⟨⟨hgm.aestronglyMeasurable, ?_⟩, h2, h3⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => mul_nonneg (by positivity)
    (bpzSoftWeight_nonneg 0 z x))]
  have hpos : bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z ^ (-q) ≠ 0 :=
    (ENNReal.rpow_pos h2 h3.ne).ne'
  by_contra hinf
  rw [not_lt, top_le_iff] at hinf
  rw [hinf, ENNReal.mul_top hpos] at h1
  exact lt_irrefl _ h1

/-- The dominating function `I^{-q} ∫ (1 + |x − z|^{-2}) k dM` is integrable. -/
theorem bpz_singular_dom_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {q : ℝ} (hq1 : 1 ≤ q) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    Integrable (fun ω => (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-q) *
      ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) P := by
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hgm : Measurable fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x :=
    (measurable_const.add ((measurable_id.sub measurable_const).norm.pow_const _)).mul hkm
  have hIm : Measurable fun ω => ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω :=
    (measurable_integral_measure hkm).comp hMm
  have hGm : Measurable fun ω => ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) *
      bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω :=
    (measurable_integral_measure hgm).comp hMm
  refine ⟨((hIm.pow_const _).mul hGm).aestronglyMeasurable, ?_⟩
  have hfin := bpz_singular_moment_lt_top (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hχ hq1 hz0 hz1
  refine (hasFiniteIntegral_iff_ofReal ?_).mpr (lt_of_le_of_lt (le_of_eq ?_) hfin)
  · filter_upwards with ω
    exact mul_nonneg (Real.rpow_nonneg (integral_nonneg fun x => bpzSoftWeight_nonneg 0 z x) _)
      (integral_nonneg fun x => mul_nonneg (by positivity) (bpzSoftWeight_nonneg 0 z x))
  · refine lintegral_congr_ae ?_
    filter_upwards [bpz_singular_integrable_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M
      hM hχ hα₁ hα₂ hα₃ hq1 hz0 hz1] with ω ⟨hg, hpos, hfin'⟩
    have hk : Integrable (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) (M ω) :=
      hg.mono' hkm.aestronglyMeasurable (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (bpzSoftWeight_nonneg 0 z x)]
        have hW := bpzSoftWeight_nonneg (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z x
        have : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := by positivity
        linarith only [mul_nonneg this hW])
    have hI : ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω =
        (bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
        bpzSoftWeight_nonneg 0 z x) hkm.aestronglyMeasurable]
      rfl
    have hIpos : 0 < (bpzMass γ χ α₁ α₂ α₃ 0 (M ω) z).toReal := ENNReal.toReal_pos hpos.ne' hfin'.ne
    rw [hI, ENNReal.ofReal_mul (Real.rpow_nonneg hIpos.le _), ← ENNReal.ofReal_rpow_of_pos hIpos,
      ENNReal.ofReal_toReal hfin'.ne, ofReal_integral_eq_lintegral_ofReal hg
        (Eventually.of_forall fun x => mul_nonneg (by positivity) (bpzSoftWeight_nonneg 0 z x))]

theorem bpz_ae_regular {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂M ω, x ∈ bpzRegular z := by
  filter_upwards [gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z] with ω h0 h1 hz
  have h : ∀ c : ℂ, M ω {c} = 0 → ∀ᵐ x ∂M ω, x ≠ c := fun c hc => by
    rw [ae_iff]; simpa using hc
  filter_upwards [h 0 h0, h 1 h1, h z hz] with x a b c
  exact ⟨a, b, c⟩

/-- The right side of the Ward identity converges along the test functions. -/
theorem bpz_ward_rhs_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {q : ℝ} (hq1 : 1 ≤ q)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {φ : ℂ → ℝ} {φn : ℕ → ℂ → ℝ}
    (hφnm : ∀ n, Measurable (φn n)) (hφm : Measurable φ)
    (hval : ∀ x ∈ bpzRegular z, ∀ᶠ n in atTop, φn n x = φ x) (v : ℂ) {A : ℝ} (hA0 : 0 ≤ A)
    (hb3 : ∀ n, ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(φn n x - φn n y) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ))) :
    Tendsto (fun n => ∫ ω, q * ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-q - 1) *
        (γ ^ 2 * ∫ x, ∫ y, (φn n x - φn n y) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x *
          bpzSoftWeight γ χ α₁ α₂ α₃ 0 z y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω)) ∂P) atTop
      (𝓝 (∫ ω, q * ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-q - 1) *
        (γ ^ 2 * ∫ x, ∫ y, (φ x - φ y) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x *
          bpzSoftWeight γ χ α₁ α₂ α₃ 0 z y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω)) ∂P)) := by
  have : IsProbabilityMeasure P := hX.1
  set k : ℂ → ℝ := bpzSoftWeight γ χ α₁ α₂ α₃ 0 z with hkdef
  set g : ℂ → ℝ := fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x with hgdef
  have hkm : Measurable k := measurable_bpzSoftWeight 0 z
  have hk0 : ∀ x, 0 ≤ k x := bpzSoftWeight_nonneg 0 z
  have hq0 : 0 ≤ q := by linarith
  set H : (ℂ → ℝ) → ℂ → ℂ → ℝ := fun f x y =>
    (f x - f y) * (k x * k y) * bpzKern v (x - y) / 2 with hHdef
  have hHm : ∀ f : ℂ → ℝ, Measurable f → Measurable (Function.uncurry (H f)) := fun f hf =>
    ((((hf.comp measurable_fst).sub (hf.comp measurable_snd)).mul
      ((hkm.comp measurable_fst).mul (hkm.comp measurable_snd))).mul
        ((measurable_bpzKern v).comp (measurable_fst.sub measurable_snd))).div_const _
  have hgood := bpz_singular_integrable_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hreg := bpz_ae_regular P X hX hγ hγ2 M hM z
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M
    hM hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  -- the pointwise bound on the regular region
  have hHb : ∀ n x y, x ∈ bpzRegular z → y ∈ bpzRegular z →
      |H (φn n) x y| ≤ A / 2 * (g x * k y + k x * g y) := by
    intro n x y hx hy
    have hb := hb3 n x hx y hy
    have hkk : 0 ≤ k x * k y := mul_nonneg (hk0 x) (hk0 y)
    simp only [hHdef, hgdef]
    rw [abs_div, abs_two, show (φn n x - φn n y) * (k x * k y) * bpzKern v (x - y) =
      ((φn n x - φn n y) * bpzKern v (x - y)) * (k x * k y) by ring, abs_mul, abs_of_nonneg hkk]
    have h1 : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := by positivity
    have h2 : 0 ≤ ‖y - z‖ ^ (-2 : ℝ) := by positivity
    calc |(φn n x - φn n y) * bpzKern v (x - y)| * (k x * k y) / 2
        ≤ A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) * (k x * k y) / 2 := by gcongr
      _ ≤ A / 2 * ((1 + ‖x - z‖ ^ (-2 : ℝ)) * k x * k y + k x * ((1 + ‖y - z‖ ^ (-2 : ℝ)) * k y))
          := by linarith only [mul_nonneg hA0 hkk]
  -- the inner limit, for good samples
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, ∫ y, H (φn n) x y ∂M ω ∂M ω) atTop
      (𝓝 (∫ x, ∫ y, H φ x y ∂M ω ∂M ω)) := by
    filter_upwards [hgood, hreg] with ω hgω hω
    obtain ⟨hgi, -, -⟩ := hgω
    have := hM.1 ω
    have hki : Integrable k (M ω) := hgi.mono' hkm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hk0 x)]
        have : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := by positivity
        linarith only [mul_nonneg this (hk0 x)])
    have hbi : Integrable (fun p : ℂ × ℂ => A / 2 * (g p.1 * k p.2 + k p.1 * g p.2))
        ((M ω).prod (M ω)) := ((hgi.mul_prod hki).add (hki.mul_prod hgi)).const_mul _
    have hreg2 : ∀ᵐ p ∂((M ω).prod (M ω)), p.1 ∈ bpzRegular z ∧ p.2 ∈ bpzRegular z := by
      have h1 := (Measure.quasiMeasurePreserving_fst (μ := M ω) (ν := M ω)).ae hω
      have h2 := (Measure.quasiMeasurePreserving_snd (μ := M ω) (ν := M ω)).ae hω
      filter_upwards [h1, h2] with p hp1 hp2
      exact ⟨hp1, hp2⟩
    have hint : ∀ f : ℂ → ℝ, Measurable f → (∀ x y, x ∈ bpzRegular z → y ∈ bpzRegular z →
        |H f x y| ≤ A / 2 * (g x * k y + k x * g y)) →
        Integrable (fun p : ℂ × ℂ => H f p.1 p.2) ((M ω).prod (M ω)) := fun f hf hfb =>
      hbi.mono' (hHm f hf).aestronglyMeasurable (by
        filter_upwards [hreg2] with p hp
        rw [Real.norm_eq_abs]; exact hfb p.1 p.2 hp.1 hp.2)
    have hHφb : ∀ x y, x ∈ bpzRegular z → y ∈ bpzRegular z →
        |H φ x y| ≤ A / 2 * (g x * k y + k x * g y) := by
      intro x y hx hy
      obtain ⟨n, hn⟩ := ((hval x hx).and (hval y hy)).exists
      have := hHb n x y hx hy
      simp only [hHdef] at this ⊢
      rwa [hn.1, hn.2] at this
    rw [← integral_prod (fun p : ℂ × ℂ => H φ p.1 p.2) (hint φ hφm hHφb)]
    have heq : ∀ n, ∫ x, ∫ y, H (φn n) x y ∂M ω ∂M ω =
        ∫ p : ℂ × ℂ, H (φn n) p.1 p.2 ∂((M ω).prod (M ω)) := fun n =>
      (integral_prod _ (hint (φn n) (hφnm n) (hHb n))).symm
    simp_rw [heq]
    refine tendsto_integral_of_dominated_convergence _
      (fun n => (hHm (φn n) (hφnm n)).aestronglyMeasurable) hbi (fun n => ?_) ?_
    · filter_upwards [hreg2] with p hp
      rw [Real.norm_eq_abs]; exact hHb n p.1 p.2 hp.1 hp.2
    · filter_upwards [hreg2] with p hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hval p.1 hp.1, hval p.2 hp.2] with n h1 h2
      simp only [hHdef]
      rw [h1, h2]
  -- the outer limit
  refine tendsto_integral_of_dominated_convergence
    (fun ω => q * γ ^ 2 * A * ((∫ x, k x ∂M ω) ^ (-q) * ∫ x, g x ∂M ω)) (fun n => ?_)
    (hdom.const_mul _) (fun n => ?_) ?_
  · exact (measurable_const.mul ((((measurable_integral_measure hkm).comp hMm).pow_const _).mul
      (measurable_const.mul (bpz_measurable_double_integral hMm hM.1 hMm hM.1 _
        (hHm (φn n) (hφnm n)))))).aestronglyMeasurable
  · filter_upwards [hgood, hreg] with ω hgω hω
    obtain ⟨hgi, hpos, hfin⟩ := hgω
    have := hM.1 ω
    have hki : Integrable k (M ω) := hgi.mono' hkm.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hk0 x)]
        have : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := by positivity
        linarith only [mul_nonneg this (hk0 x)])
    set I : ℝ := ∫ x, k x ∂M ω with hI
    set G : ℝ := ∫ x, g x ∂M ω with hG
    have hIpos : 0 < I := by
      rw [hI, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hk0)
        hkm.aestronglyMeasurable]
      exact ENNReal.toReal_pos hpos.ne' hfin.ne
    have hG0 : 0 ≤ G := integral_nonneg fun x => mul_nonneg (by positivity) (hk0 x)
    have hreg2 : ∀ᵐ p ∂((M ω).prod (M ω)), p.1 ∈ bpzRegular z ∧ p.2 ∈ bpzRegular z := by
      have h1 := (Measure.quasiMeasurePreserving_fst (μ := M ω) (ν := M ω)).ae hω
      have h2 := (Measure.quasiMeasurePreserving_snd (μ := M ω) (ν := M ω)).ae hω
      filter_upwards [h1, h2] with p hp1 hp2
      exact ⟨hp1, hp2⟩
    have hbi : Integrable (fun p : ℂ × ℂ => A / 2 * (g p.1 * k p.2 + k p.1 * g p.2))
        ((M ω).prod (M ω)) := ((hgi.mul_prod hki).add (hki.mul_prod hgi)).const_mul _
    have hdbl : |∫ x, ∫ y, H (φn n) x y ∂M ω ∂M ω| ≤ A * (G * I) := by
      have hHi : Integrable (fun p : ℂ × ℂ => H (φn n) p.1 p.2) ((M ω).prod (M ω)) :=
        hbi.mono' (hHm (φn n) (hφnm n)).aestronglyMeasurable (by
          filter_upwards [hreg2] with p hp
          rw [Real.norm_eq_abs]; exact hHb n p.1 p.2 hp.1 hp.2)
      rw [← integral_prod _ hHi, ← Real.norm_eq_abs]
      refine (norm_integral_le_of_norm_le hbi (by
        filter_upwards [hreg2] with p hp
        rw [Real.norm_eq_abs]; exact hHb n p.1 p.2 hp.1 hp.2)).trans (le_of_eq ?_)
      rw [integral_const_mul, integral_add (hgi.mul_prod hki) (hki.mul_prod hgi),
        integral_prod_mul (f := g) (g := k), integral_prod_mul (f := k) (g := g)]
      ring
    have hIq : 0 ≤ I ^ (-q - 1) := Real.rpow_nonneg hIpos.le _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hq0, abs_of_nonneg hIq,
      abs_of_nonneg (sq_nonneg γ)]
    calc q * (I ^ (-q - 1) * (γ ^ 2 * |∫ x, ∫ y, H (φn n) x y ∂M ω ∂M ω|))
        ≤ q * (I ^ (-q - 1) * (γ ^ 2 * (A * (G * I)))) := by gcongr
      _ = q * γ ^ 2 * A * ((I ^ (-q - 1) * I) * G) := by ring
      _ = q * γ ^ 2 * A * (I ^ (-q) * G) := by
          rw [← Real.rpow_add_one hIpos.ne']; ring_nf
  · filter_upwards [hinner] with ω hω
    exact ((hω.const_mul (γ ^ 2)).const_mul _).const_mul q

/-- **Extension of the four-point Ward identity to limits of test functions.** -/
theorem bpz_fourPoint_ward_extend {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 0 ≤ fourPointSExp γ (-χ) α₁ α₂ α₃)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {φ : ℂ → ℝ} {φn : ℕ → ℂ → ℝ}
    (hφn : ∀ n, ContDiff ℝ 1 (φn n)) (hφnc : ∀ n, HasCompactSupport (φn n))
    (hφnU : ∀ n, tsupport (φn n) ⊆ bpzRegular z)
    (hφm : Measurable φ) (hloc : ∀ x ∈ bpzRegular z, ∀ᶠ n in atTop, φn n =ᶠ[𝓝 x] φ) (v : ℂ)
    {A : ℝ} (hb1 : ∀ n, ∀ x ∈ bpzRegular z,
      |fderiv ℝ (fun x => φn n x * bpzTildeWeight γ χ α₁ α₂ z x) x v| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzTildeWeight γ χ α₁ α₂ z x)
    (hb3 : ∀ n, ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(φn n x - φn n y) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ))) :
    ∫ ω, (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-(fourPointSExp γ (-χ) α₁ α₂ α₃ + 1)) *
        ∫ x, fderiv ℝ (fun x => φ x * bpzTildeWeight γ χ α₁ α₂ z x) x v *
          normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) ∂M ω ∂P =
      ∫ ω, (fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) *
        ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^
          (-(fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) - 1) *
        (γ ^ 2 * ∫ x, ∫ y, (φ x - φ y) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x *
          bpzSoftWeight γ χ α₁ α₂ α₃ 0 z y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω)) ∂P := by
  have : IsProbabilityMeasure P := hX.1
  set q : ℝ := fourPointSExp γ (-χ) α₁ α₂ α₃ + 1 with hqdef
  have hq1 : 1 ≤ q := by linarith
  set k : ℂ → ℝ := bpzSoftWeight γ χ α₁ α₂ α₃ 0 z with hkdef
  set kt : ℂ → ℝ := bpzTildeWeight γ χ α₁ α₂ z with hktdef
  set ex : ℂ → ℝ := fun x => normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) with hexdef
  set g : ℂ → ℝ := fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x with hgdef
  have hkm : Measurable k := measurable_bpzSoftWeight 0 z
  have hk0 : ∀ x, 0 ≤ k x := bpzSoftWeight_nonneg 0 z
  have hkkt : ∀ x, k x = kt x * ex x := fun x => bpzSoftWeight_zero_eq z x
  have hgm : Measurable g :=
    (measurable_const.add ((measurable_id.sub measurable_const).norm.pow_const _)).mul hkm
  have hg0 : ∀ x, 0 ≤ g x := fun x => mul_nonneg (by positivity) (hk0 x)
  have hA0 : 0 ≤ A := by
    have := hb3 0 (‖z‖ + 2 : ℝ) ?_ (‖z‖ + 2 : ℝ) ?_
    · simp only [sub_self, zero_mul, abs_zero] at this
      by_contra hneg
      push Not at hneg
      have hpos : 0 < 1 + ‖((‖z‖ + 2 : ℝ) : ℂ) - z‖ ^ (-2 : ℝ) +
          ‖((‖z‖ + 2 : ℝ) : ℂ) - z‖ ^ (-2 : ℝ) := by positivity
      linarith only [this, mul_neg_of_neg_of_pos hneg hpos]
    all_goals
      have hn : ‖((‖z‖ + 2 : ℝ) : ℂ)‖ = ‖z‖ + 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have := congrArg norm h; rw [hn, norm_zero] at this; linarith [norm_nonneg z]
      · have := congrArg norm h; rw [hn, norm_one] at this; linarith [norm_nonneg z]
      · have := congrArg norm h; rw [hn] at this; linarith
  -- the identity at each stage
  have hW := fun n => bpz_fourPoint_ward (α₃ := α₃) P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hs
    hz0 hz1 (hφn n) (hφnc n) (hφnU n) v
  -- the good event
  have hgood := bpz_singular_integrable_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hreg := bpz_ae_regular P X hX hγ hγ2 M hM z
  have hdom := (bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M
    hM hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1)
  -- pointwise identification of the derivatives
  have hfd : ∀ x ∈ bpzRegular z, ∀ᶠ n in atTop,
      fderiv ℝ (fun x => φn n x * kt x) x v = fderiv ℝ (fun x => φ x * kt x) x v := by
    intro x hx
    filter_upwards [hloc x hx] with n hn
    have : (fun y => φn n y * kt y) =ᶠ[𝓝 x] fun y => φ y * kt y := by
      filter_upwards [hn] with y hy; rw [hy]
    rw [this.fderiv_eq]
  have hval : ∀ x ∈ bpzRegular z, ∀ᶠ n in atTop, φn n x = φ x := fun x hx =>
    (hloc x hx).mono fun n hn => hn.eq_of_nhds
  -- left side
  have hL : Tendsto (fun n => ∫ ω, (∫ x, k x ∂M ω) ^ (-q) *
      ∫ x, fderiv ℝ (fun x => φn n x * kt x) x v * ex x ∂M ω ∂P) atTop
      (𝓝 (∫ ω, (∫ x, k x ∂M ω) ^ (-q) *
        ∫ x, fderiv ℝ (fun x => φ x * kt x) x v * ex x ∂M ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω => A * ((∫ x, k x ∂M ω) ^ (-q) *
      ∫ x, g x ∂M ω)) (fun n => ?_) (hdom.const_mul A) (fun n => ?_) ?_
    · exact (((measurable_integral_measure hkm).comp hMm).pow_const _ |>.mul
        ((measurable_integral_measure ((measurable_fderiv_apply_const ℝ _ v).mul
          (bpz_measurable_normPlus.pow_const _))).comp hMm)).aestronglyMeasurable
    · filter_upwards [hgood, hreg] with ω hgω hω
      obtain ⟨hgi, -, -⟩ := hgω
      have hI0 : 0 ≤ (∫ x, k x ∂M ω) ^ (-q) :=
        Real.rpow_nonneg (integral_nonneg hk0) _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hI0, mul_left_comm]
      refine mul_le_mul_of_nonneg_left ?_ hI0
      rw [← integral_const_mul, ← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le (hgi.const_mul A) ?_
      filter_upwards [hω] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (bpz_normPlus_pos x).le _)]
      calc |fderiv ℝ (fun x => φn n x * kt x) x v| * ex x
          ≤ A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * kt x * ex x :=
            mul_le_mul_of_nonneg_right (hb1 n x hx) (Real.rpow_nonneg (bpz_normPlus_pos x).le _)
        _ = A * g x := by simp only [hgdef, hkkt x]; ring
    · filter_upwards [hgood, hreg] with ω hgω hω
      obtain ⟨hgi, -, -⟩ := hgω
      refine Tendsto.const_mul _ (tendsto_integral_of_dominated_convergence (fun x => A * g x)
        (fun n => ((measurable_fderiv_apply_const ℝ _ v).mul
          (bpz_measurable_normPlus.pow_const _)).aestronglyMeasurable) (hgi.const_mul A)
        (fun n => ?_) ?_)
      · filter_upwards [hω] with x hx
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (bpz_normPlus_pos x).le _)]
        calc |fderiv ℝ (fun x => φn n x * kt x) x v| * ex x
            ≤ A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * kt x * ex x :=
              mul_le_mul_of_nonneg_right (hb1 n x hx)
                (Real.rpow_nonneg (bpz_normPlus_pos x).le _)
          _ = A * g x := by simp only [hgdef, hkkt x]; ring
      · filter_upwards [hω] with x hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hfd x hx] with n hn
        rw [hn]
  have hR := bpz_ward_rhs_tendsto (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM hMm hχ
    hα₁ hα₂ hα₃ hq1 hz0 hz1 (fun n => (hφn n).continuous.measurable) hφm hval v hA0 hb3
  exact tendsto_nhds_unique (hL.congr fun n => hW n) hR

end DOZZ.Proofs
