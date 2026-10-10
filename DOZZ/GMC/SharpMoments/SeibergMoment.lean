/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergDecomp
public import DOZZ.GMC.SharpMoments.SeibergPieces

/-! # Positive moments of the Coulomb mass

Below the bulk threshold and every insertion threshold, including the one at infinity, the
Coulomb mass has a finite moment of every positive order: the root pieces are weighted local
masses, the bulk piece is the mass of a bounded disk, and the exterior piece is a weighted local
mass of the inverted measure, which has the law of the original one. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Integrals against an `IsGMCOf` version of a fixed measurable function are a.e. measurable. -/
theorem gmc_lintegral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    AEMeasurable (fun ω => ∫⁻ x, f x ∂M ω) P := by
  simpa using gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM f hf Set.univ MeasurableSet.univ

/-- Coulomb masses of an `IsGMCOf` version are a.e. measurable. -/
theorem gmc_coulombMass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) :
    AEMeasurable (fun ω => coulombMass γ (M ω) α z αinf) P := by
  simp only [coulombMass_eq_lintegral_coulombWeight]
  exact gmc_lintegral_aemeasurable P X hX γ hγ hγ2 M hM _ (measurable_coulombWeight γ α z αinf)

/-- A constant multiple of a positive power of an a.e. measurable function with finite
expectation has finite expectation. -/
theorem lintegral_const_mul_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {c : ℝ≥0∞} (hc : c ≠ ⊤) {t : ℝ} (ht : 0 < t)
    (hfin : ∫⁻ ω, f ω ^ t ∂P < ⊤) :
    ∫⁻ ω, (c * f ω) ^ t ∂P < ⊤ := by
  rw [lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg c (f ω) ht.le,
    lintegral_const_mul'' _ (hf.pow_const t)]
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ht.le hc) hfin

/-- Below the bulk threshold and every insertion threshold, the Coulomb mass has a finite moment
of every positive order. -/
theorem coulombMass_moment_lt_top_of_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (t : ℝ) (ht : 0 < t) (htb : t < 4 / γ ^ 2) (hti : ∀ k, t < 2 / γ * (Q γ - α k))
    (htinf : t < 2 / γ * (Q γ - αinf)) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P < ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨δ, hδ, hδ8, hsep⟩ := exists_root_separation z hz
  have hδ1 : δ ≤ 1 := hδ8.trans (by norm_num)
  set Rr : ℝ := 1 + 2 * ∑ j, ‖z j‖ with hRr
  obtain ⟨hRr1, hzRr⟩ := coulomb_exterior_radius_bounds z
  have hRr0 : 0 < Rr := by linarith
  set cR : ℝ≥0∞ := ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^
    (∑ j, |γ * α j| + |γ * αinf|)) with hcR
  set cB : ℝ≥0∞ := ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^
    (∑ j, |γ * α j| + |γ * αinf|)) with hcB
  set cE : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) with hcE
  set W : Fin N → Ω → ℝ≥0∞ := fun k ω => weightedGmcBallMass γ (M ω) (α k) (z k) δ with hW
  set MB : Ω → ℝ≥0∞ := fun ω => M ω (Metric.closedBall 0 Rr) with hMB
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | Rr < ‖x‖},
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) ∂M ω with hV
  set L : ℝ≥0∞ := ENNReal.LpAddConst (ENNReal.ofReal t)⁻¹ with hL
  have hLtop : L ≠ ⊤ := (ENNReal.LpAddConst_lt_top _).ne
  set n : ℝ≥0∞ := ((Finset.univ : Finset (Fin N)).card : ℝ≥0∞) with hn
  -- measurability of the pieces
  have hWm : ∀ k, AEMeasurable (W k) P := fun k =>
    gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM (α k) (z k) δ
  have hMBm : AEMeasurable MB P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isClosed_closedBall.measurableSet
  have hg : Measurable fun x : ℂ => ENNReal.rpow (ENNReal.ofReal ‖x‖) (γ * αinf) :=
    (ENNReal.continuous_rpow_const (y := γ * αinf)).measurable.comp
      (ENNReal.measurable_ofReal.comp measurable_norm)
  have hVm : AEMeasurable V P :=
    gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ hg _
      (measurableSet_lt measurable_const measurable_norm)
  -- finiteness of the piece moments
  have hWfin : ∀ k, ∫⁻ ω, (cR * W k ω) ^ t ∂P < ⊤ := fun k =>
    lintegral_const_mul_rpow_lt_top (hWm k) ENNReal.ofReal_ne_top ht
      (weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM (α k) (z k) δ hδ t ht
        (lt_min htb (hti k)))
  have hMBfin : ∫⁻ ω, (cB * MB ω) ^ t ∂P < ⊤ :=
    lintegral_const_mul_rpow_lt_top hMBm ENNReal.ofReal_ne_top ht
      (gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM _ Metric.isBounded_closedBall t ht.le htb)
  have hVfin : ∫⁻ ω, (cE * V ω) ^ t ∂P < ⊤ :=
    lintegral_const_mul_rpow_lt_top hVm ENNReal.ofReal_ne_top ht
      (lt_of_le_of_lt (gmc_exterior_moment_le_weighted P X hX γ hγ hγ2 M hM αinf hRr0 t ht.le)
        (weightedGmcBallMoment_lt_top_of_sharp_range P X hX γ hγ hγ2 M hM αinf 0 (1 / Rr)
          (by positivity) t ht (lt_min htb htinf)))
  -- the pointwise bound
  have hatoms : ∀ᵐ ω ∂P, ∀ k, M ω {z k} = 0 :=
    ae_all_iff.mpr fun k => gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (z k)
  have hpt : ∀ᵐ ω ∂P, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ≤
      L * (L * (n ^ t * ∑ k, (cR * W k ω) ^ t + (cB * MB ω) ^ t) +
        (cE * V ω) ^ t) := by
    filter_upwards [hatoms] with ω hω
    have hdec := coulombMass_le_pieces (M ω) γ α z αinf hδ hδ1 hsep hω hRr1 hzRr
    calc ENNReal.rpow (coulombMass γ (M ω) α z αinf) t
        ≤ ((∑ k, cR * W k ω + cB * MB ω) + cE * V ω) ^ t := ENNReal.rpow_le_rpow hdec ht.le
      _ ≤ L * ((∑ k, cR * W k ω + cB * MB ω) ^ t + (cE * V ω) ^ t) :=
          ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ ht.le
      _ ≤ L * (L * ((∑ k, cR * W k ω) ^ t + (cB * MB ω) ^ t) + (cE * V ω) ^ t) := by
          gcongr
          exact ENNReal.rpow_add_le_mul_rpow_add_rpow' _ _ ht.le
      _ ≤ _ := by
          gcongr
          exact ennreal_finset_sum_rpow_le_card_rpow_sum_of_pos _ _ ht
  -- integrate the bound
  have hsumm : ∀ k ∈ Finset.univ, AEMeasurable (fun ω => (cR * W k ω) ^ t) P := fun k _ =>
    (aemeasurable_const.mul (hWm k)).pow_const t
  have hsumfin : ∫⁻ ω, ∑ k, (cR * W k ω) ^ t ∂P < ⊤ := by
    rw [lintegral_finsetSum' _ hsumm]
    exact ENNReal.sum_lt_top.mpr fun k _ => hWfin k
  have hS : AEMeasurable (fun ω => ∑ k, (cR * W k ω) ^ t) P :=
    Finset.aemeasurable_fun_sum _ hsumm
  have hA : AEMeasurable (fun ω => n ^ t * ∑ k, (cR * W k ω) ^ t) P :=
    aemeasurable_const.mul hS
  have hAfin : ∫⁻ ω, n ^ t * ∑ k, (cR * W k ω) ^ t ∂P < ⊤ := by
    rw [lintegral_const_mul'' _ hS]
    exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg ht.le (ENNReal.natCast_ne_top _))
      hsumfin
  have hABfin : ∫⁻ ω, (n ^ t * ∑ k, (cR * W k ω) ^ t +
      (cB * MB ω) ^ t) ∂P < ⊤ := by
    rw [lintegral_add_left' hA]
    exact ENNReal.add_lt_top.mpr ⟨hAfin, hMBfin⟩
  have hAB : AEMeasurable (fun ω => n ^ t * ∑ k, (cR * W k ω) ^ t +
      (cB * MB ω) ^ t) P := hA.add ((aemeasurable_const.mul hMBm).pow_const t)
  have hLAB : AEMeasurable (fun ω => L * (n ^ t *
      ∑ k, (cR * W k ω) ^ t + (cB * MB ω) ^ t)) P := aemeasurable_const.mul hAB
  have hLABfin : ∫⁻ ω, L * (n ^ t * ∑ k, (cR * W k ω) ^ t +
      (cB * MB ω) ^ t) ∂P < ⊤ := by
    rw [lintegral_const_mul'' _ hAB]
    exact ENNReal.mul_lt_top hLtop.lt_top hABfin
  have hall : ∫⁻ ω, L * (L * (n ^ t * ∑ k, (cR * W k ω) ^ t +
      (cB * MB ω) ^ t) + (cE * V ω) ^ t) ∂P < ⊤ := by
    have hLABV : AEMeasurable (fun ω => L * (n ^ t * ∑ k, (cR * W k ω) ^ t +
        (cB * MB ω) ^ t) + (cE * V ω) ^ t) P :=
      hLAB.add ((aemeasurable_const.mul hVm).pow_const t)
    rw [lintegral_const_mul'' _ hLABV, lintegral_add_left' hLAB]
    exact ENNReal.mul_lt_top hLtop.lt_top (ENNReal.add_lt_top.mpr ⟨hLABfin, hVfin⟩)
  exact lt_of_le_of_lt (lintegral_mono_ae hpt) hall

/-- A lower integral of an a.e. positive a.e. measurable function against a probability measure
is positive. -/
theorem lintegral_pos_of_ae_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) (h : ∀ᵐ ω ∂P, 0 < f ω) :
    0 < ∫⁻ ω, f ω ∂P := by
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  have hz := (lintegral_eq_zero_iff' hf).mp h0
  obtain ⟨ω, hω1, hω2⟩ := (h.and hz).exists
  exact (ne_of_gt hω1) hω2

/-- The global extended moment on `U_N`. -/
theorem equatorGFF_extendedSeiberg_moment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ} (z : Fin N → ℂ) (hz : Function.Injective z)
    (α : Fin N → ℝ) (αinf : ℝ) (hαQ : ∀ k, α k < Q γ) (hαinf : αinf < Q γ)
    (hbulk : (2 * Q γ - (∑ k, α k + αinf)) / γ < 4 / γ ^ 2)
    (hins : ∀ k, (2 * Q γ - (∑ k, α k + αinf)) / γ < 2 / γ * (Q γ - α k))
    (hinsinf : (2 * Q γ - (∑ k, α k + αinf)) / γ < 2 / γ * (Q γ - αinf)) :
    0 < ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf)
        ((2 * Q γ - (∑ k, α k + αinf)) / γ) ∂P ∧
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf)
        ((2 * Q γ - (∑ k, α k + αinf)) / γ) ∂P < ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  set s : ℝ := (2 * Q γ - (∑ k, α k + αinf)) / γ with hs
  set Z : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) α z αinf with hZ
  have hZm : AEMeasurable Z P := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf
  -- the lower bound by a fixed exterior disk
  set c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
    ENNReal.ofReal ((1 + 2 * ∑ j, ‖z j‖ + 2) ^ (-|γ * αinf|)) with hc
  set B : Set ℂ := Metric.ball (((1 + 2 * ∑ j, ‖z j‖ + 1 : ℝ)) : ℂ) (1 / 8) with hB
  have hc0 : c ≠ 0 := by
    have hsum : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    refine mul_ne_zero ?_ ?_
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
    · exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hctop : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  obtain ⟨hRr1, hzRr⟩ := coulomb_exterior_radius_bounds z
  have hlow : ∀ ω, c * M ω B ≤ Z ω := fun ω =>
    coulombMass_ge_exterior_ball (M ω) γ α z αinf hRr1 hzRr
  have hBpos := gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM
    (((1 + 2 * ∑ j, ‖z j‖ + 1 : ℝ)) : ℂ) (1 / 8) (by norm_num)
  have hBm : AEMeasurable (fun ω => M ω B) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B Metric.isOpen_ball.measurableSet
  -- almost surely the Coulomb mass is positive and finite
  have h4 : (0 : ℝ) < 4 / γ ^ 2 := by positivity
  have hinf0 : 0 < 2 / γ * (Q γ - αinf) := mul_pos (by positivity) (sub_pos.mpr hαinf)
  have hk0 : ∀ k, 0 < 2 / γ * (Q γ - α k) := fun k => mul_pos (by positivity) (sub_pos.mpr (hαQ k))
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (4 / γ ^ 2) := Ioo_mem_nhdsGT h4
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioo 0 (2 / γ * (Q γ - αinf)) := Ioo_mem_nhdsGT hinf0
  have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, t ∈ Set.Ioo 0 (2 / γ * (Q γ - α k)) :=
    eventually_all.mpr fun k => Ioo_mem_nhdsGT (hk0 k)
  obtain ⟨t, ht⟩ := (e1.and (e2.and e3)).exists
  have htfin := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf t ht.1.1
    ht.1.2 (fun k => (ht.2.2 k).2) ht.2.1.2
  have hZfin : ∀ᵐ ω ∂P, Z ω < ⊤ := by
    filter_upwards [ae_lt_top' (hZm.pow_const t) htfin.ne] with ω hω
    by_contra hcon
    rw [not_lt_top_iff.mp hcon, ENNReal.top_rpow_of_pos ht.1.1] at hω
    exact lt_irrefl _ hω
  have hZpos : ∀ᵐ ω ∂P, 0 < Z ω := by
    filter_upwards [hBpos] with ω hω
    exact lt_of_lt_of_le (ENNReal.mul_pos hc0 hω.ne') (hlow ω)
  refine ⟨lintegral_pos_of_ae_pos (hZm.pow_const s) ?_, ?_⟩
  · filter_upwards [hZfin, hZpos] with ω h1 h2
    exact ENNReal.rpow_pos h2 h1.ne
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · -- negative Seiberg exponent: the inverse moments of a fixed disk
    calc ∫⁻ ω, ENNReal.rpow (Z ω) s ∂P ≤ ∫⁻ ω, (c * M ω B) ^ s ∂P :=
          lintegral_mono fun ω => ennreal_rpow_antitone_of_nonpos (hlow ω) hneg.le
      _ = c ^ s * gmcMassMoment P M B s := by
          rw [lintegral_congr fun ω => ennreal_mul_rpow_of_ne_zero_ne_top c (M ω B) hc0 hctop s,
            lintegral_const_mul'' _ (hBm.pow_const s)]
          rfl
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc0 hctop).lt_top
          (gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM _ (1 / 8) (by norm_num) le_rfl
            s (by linarith))
  · -- zero Seiberg exponent
    have h1 : ∀ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) s = 1 := fun ω => by
      rw [hzero]
      exact ENNReal.rpow_zero
    simp only [h1, lintegral_const, measure_univ, mul_one]
    exact ENNReal.one_lt_top
  · -- positive Seiberg exponent
    exact coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf s hpos hbulk hins
      hinsinf

end DOZZ.Proofs
