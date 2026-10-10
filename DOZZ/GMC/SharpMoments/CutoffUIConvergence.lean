/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBadLimit
public import DOZZ.GMC.SharpMoments.CoulombCutoffLimit
public import DOZZ.GMC.SharpMoments.GoodPart
public import DOZZ.GMC.SharpMoments.CutoffUIConvergenceAux
public import DOZZ.GMC.SharpMoments.CutoffUIMoment

/-! # Convergence in probability of regularized Coulomb masses, uniformly on compact sets

Split the plane into a bad region, small disks about the roots and the exterior of a large disk,
and its complement. The bad parts of the regularized and of the limiting Coulomb masses have
small moments uniformly in the parameters and in the cutoff. On the complement the regularized
weight converges uniformly to the Coulomb weight, and the bounded Coulomb weight integrated
against the cutoff chaos converges in `L¹`, uniformly in the parameters, by the uniform `L¹`
convergence of cutoff chaos over compact couplings. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Admissible compact parameter sets carry a uniform small admissible order: a positive order
admissible at every root charge, at its positive part, and at the positive part of the charge at
infinity, together with a uniform root separation. -/
theorem cutoffUI_uniform_order
    {N : ℕ} (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1) :
    ∃ tst : ℝ, 0 < tst ∧
      (∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, c.2.2.1 k, tst)) ∧
      (∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, max (c.2.2.1 k) 0, tst)) ∧
      (∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, tst)) ∧
      ∃ ρs : ℝ, 0 < ρs ∧ ρs ≤ 1 ∧ ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖ := by
  classical
  have hne : ∀ c ∈ S, c.1 ≠ 0 := fun c hc => (hadm c hc).1.ne'
  have hconton : ∀ f : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ,
      (∀ c ∈ S, ContinuousAt f c) → ContinuousOn f S := fun f hf c hc =>
    (hf c hc).continuousWithinAt
  have hQpos : ∀ c ∈ S, 0 < Q c.1 := fun c hc => by
    have := (hadm c hc).1
    rw [Q]
    positivity
  have e1 : ∀ᶠ m in 𝓝[>] (0 : ℝ), ∀ c ∈ S, m ≤ 4 / c.1 ^ 2 :=
    eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc => by
        have := (hadm c hc).1
        positivity
  have e2 : ∀ k, ∀ᶠ m in 𝓝[>] (0 : ℝ), ∀ c ∈ S, m ≤ 2 / c.1 * (Q c.1 - max (c.2.2.1 k) 0) :=
    fun k => eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc =>
        mul_pos (div_pos two_pos (hadm c hc).1)
          (sub_pos.mpr (max_lt ((hadm c hc).2.2.2.1 k) (hQpos c hc)))
  have e3 : ∀ᶠ m in 𝓝[>] (0 : ℝ), ∀ c ∈ S, m ≤ 2 / c.1 * (Q c.1 - max c.2.2.2 0) :=
    eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc =>
        mul_pos (div_pos two_pos (hadm c hc).1)
          (sub_pos.mpr (max_lt (hadm c hc).2.2.2.2 (hQpos c hc)))
  have e4 : ∀ j k : Fin N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      j ≠ k → ∀ c ∈ S, 2 * ε ≤ ‖c.2.1 j - c.2.1 k‖ := by
    intro j k
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ h => absurd hjk h
    · filter_upwards [eventually_le_of_isCompact_of_pos hS
        (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ‖c.2.1 j - c.2.1 k‖ / 2)
        (by fun_prop)
        fun c hc => half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr
          ((hadm c hc).2.2.1.ne hjk)))] with ε hε _ c hc
      linarith [hε c hc]
  obtain ⟨m, h1, h2, h3, h4, hm0, hm1⟩ := (e1.and ((eventually_all.mpr e2).and (e3.and
    ((eventually_all.mpr fun j => eventually_all.mpr (e4 j)).and (Ioo_mem_nhdsGT
      (show (0 : ℝ) < 1 by norm_num)))))).exists
  have hm : 0 < m := hm0
  refine ⟨m / 2, half_pos hm, ?_, ?_, ?_, m, hm, hm1.le, fun c hc j k hjk => h4 j k hjk c hc⟩
  · intro c hc k
    obtain ⟨hγ0, hγ2, -, hαQ, -⟩ := hadm c hc
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, hαQ k, half_pos hm, lt_min ?_ ?_⟩
    · linarith [h1 c hc]
    · have hle : 2 / c.1 * (Q c.1 - max (c.2.2.1 k) 0) ≤ 2 / c.1 * (Q c.1 - c.2.2.1 k) :=
        mul_le_mul_of_nonneg_left (by linarith [le_max_left (c.2.2.1 k) 0])
          (div_pos two_pos hγ0).le
      linarith [h2 k c hc]
  · intro c hc k
    obtain ⟨hγ0, hγ2, -, hαQ, -⟩ := hadm c hc
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, max_lt (hαQ k) (hQpos c hc),
      half_pos hm, lt_min ?_ ?_⟩
    · linarith [h1 c hc]
    · linarith [h2 k c hc]
  · intro c hc
    obtain ⟨hγ0, hγ2, -, -, hαinf⟩ := hadm c hc
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, max_lt hαinf (hQpos c hc),
      half_pos hm, lt_min ?_ ?_⟩
    · linarith [h1 c hc]
    · linarith [h3 c hc]

/-- Regularized Coulomb masses converge in probability to the Coulomb masses of the limiting
chaos, uniformly over compact admissible parameter sets: the convergence half of the
extended-Seiberg cutoff uniform integrability. -/
theorem regularizedCoulombMass_tendstoInProbability_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (partition : GMCChartPartition)
    (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ)) {N : ℕ}
    (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1) :
    ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun r : ℝ => ⨆ c ∈ S, P {ω | ε ≤ edist
        (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω).toReal
        (coulombMass c.1 (Mfam c.1 ω) c.2.2.1 c.2.1 c.2.2.2).toReal})
      atTop (𝓝 0) := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  intro ε hε
  -- uniform parameters
  obtain ⟨tst, htst, hroot, hrootp, hinf, ρs, hρs, hρs1, hsep⟩ := cutoffUI_uniform_order S hS hadm
  obtain ⟨ρ1, hρ1, A1, hA1, κ1, hκ1, hbad1⟩ := cutoffUI_bad_cutoff_moment_le P X hX Xc hXc
    partition N S hS htst hroot hinf hρs hρs1 hsep
  obtain ⟨ρ2, hρ2, A2, hA2, κ2, hκ2, hbad2⟩ := cutoffUI_bad_limit_moment_le P X hX Xc hXc Mfam
    hMfam N S hS htst hrootp hinf hρs hρs1 hsep
  obtain ⟨Zs0, hZs0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E0, hE0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
      ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|) (by fun_prop)
  set Zs : ℝ := max Zs0 0 with hZsdef
  set E : ℝ := max E0 0 with hEdef
  have hZs : 0 ≤ Zs := le_max_right _ _
  have hE : 0 ≤ E := le_max_right _ _
  have hZc : ∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Zs := fun c hc => by
    have h := hZs0 c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  have hEsum : ∀ c ∈ S, ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ E := fun c hc => by
    have h := hE0 c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (Finset.sum_nonneg fun j _ =>
      abs_nonneg _) (abs_nonneg _))] at h
    exact h.trans (le_max_left _ _)
  have hEα : ∀ c ∈ S, ∀ j, |c.1 * c.2.2.1 j| ≤ E := fun c hc j => by
    have := Finset.single_le_sum (f := fun j => |c.1 * c.2.2.1 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith [hEsum c hc, abs_nonneg (c.1 * c.2.2.2)]
  have hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E := fun c hc => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (c.1 * c.2.2.1 j))
    linarith [hEsum c hc]
  set Γ : Set ℝ := (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => c.1) '' S with hΓdef
  have hΓ : IsCompact Γ := hS.image continuous_fst
  have hΓ2 : Γ ⊆ Set.Ioo 0 2 := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(hadm c hc).1, (hadm c hc).2.1⟩
  -- the threshold
  set e : ℝ := (min ε 1).toReal with hedef
  have hmin1 : min ε 1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _)
  have he : 0 < e := ENNReal.toReal_pos (lt_min hε one_pos).ne' hmin1
  have hεe : ENNReal.ofReal e ≤ ε := by
    rw [hedef, ENNReal.ofReal_toReal hmin1]
    exact min_le_left _ _
  set a : ℝ≥0∞ := ENNReal.ofReal (e / 3) with ha
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hat0 : a ^ tst ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ha0) hat).ne'
  have hatt : a ^ tst ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg htst.le hat
  refine ENNReal.tendsto_atTop_zero.mpr fun θ hθ => ?_
  -- choose the radius of the bad region
  have hT : ∀ (A : ℝ≥0∞) (κ : ℝ), A ≠ ⊤ → 0 < κ →
      Tendsto (fun ρ : ℝ => A * ENNReal.ofReal (ρ ^ κ)) (𝓝[>] 0) (𝓝 0) := by
    intro A κ hA hκ
    have h0 : Tendsto (fun ρ : ℝ => ρ ^ κ) (𝓝[>] 0) (𝓝 0) := by
      have h0' : Tendsto (fun ρ : ℝ => ρ ^ κ) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ κ)) :=
        ((Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto).mono_left
          nhdsWithin_le_nhds
      rwa [Real.zero_rpow hκ.ne'] at h0'
    have h1 := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal h0) (Or.inr hA)
    simpa using h1
  set δ1 : ℝ≥0∞ := θ / 3 * a ^ tst with hδ1
  have hδ1pos : 0 < δ1 := ENNReal.mul_pos (ENNReal.div_pos hθ.ne' (by norm_num)).ne' hat0
  obtain ⟨ρ, ⟨hρb1, hρb2⟩, hρint⟩ := (((hT A1 κ1 hA1.ne hκ1).eventually (Iio_mem_nhds hδ1pos)).and
    ((hT A2 κ2 hA2.ne hκ2).eventually (Iio_mem_nhds hδ1pos))).and
    (Ioo_mem_nhdsGT (lt_min (lt_min hρ1 hρ2) one_pos)) |>.exists
  have hρ : 0 < ρ := hρint.1
  have hρle1 : ρ ≤ ρ1 := (hρint.2.le.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hρle2 : ρ ≤ ρ2 := (hρint.2.le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hρ1' : ρ ≤ 1 := hρint.2.le.trans (min_le_right _ _)
  -- the good part
  obtain ⟨L, hL0, hL⟩ := coulombCutoffWeight_sub_coulombWeight_le partition N hZs hE hρ hρ1'
  set L2 : ℝ := ((1 + 1 / ρ + Zs) / ρ) ^ ((N + 1) * E) with hL2
  have hUL1 := equatorGFF_GMC_uniform_L1 P X hX Xc hXc Mfam hMfam Γ hΓ hΓ2
    (closedBall 0 (1 / ρ)) (isCompact_closedBall _ _) L2
  set Sρ : ℝ → ℝ≥0∞ := fun r => ⨆ γ ∈ Γ, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
      (_ : ∀ x, |f x| ≤ L2) (_ : ∀ x ∉ closedBall (0 : ℂ) (1 / ρ), f x = 0),
      ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P
    with hSρ
  have hrefFin : gmcReferenceMeasure Set.univ ≠ ⊤ := gmcReferenceMeasure_univ_ne_top
  have hT3 : Tendsto (fun r : ℝ => ENNReal.ofReal (L * Real.exp (-r)) *
      gmcReferenceMeasure Set.univ + Sρ r) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => L * Real.exp (-r)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul L
      rwa [mul_zero] at this
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hrefFin)
    rw [ENNReal.ofReal_zero, zero_mul] at h2
    simpa using h2.add hUL1
  set δ3 : ℝ≥0∞ := θ / 3 * a with hδ3
  have hδ3pos : 0 < δ3 := ENNReal.mul_pos (ENNReal.div_pos hθ.ne' (by norm_num)).ne' ha0
  obtain ⟨r0, hr0⟩ := eventually_atTop.mp ((hT3.eventually (Iio_mem_nhds hδ3pos)))
  refine ⟨max r0 (Real.log (1 / ρ)), fun r hr => iSup₂_le fun c hc => ?_⟩
  have hrr0 : r0 ≤ r := (le_max_left _ _).trans hr
  have hrlog : Real.log (1 / ρ) ≤ r := (le_max_right _ _).trans hr
  have hr0' : 0 ≤ r := le_trans (Real.log_nonneg (by rw [le_div_iff₀ hρ]; linarith)) hrlog
  obtain ⟨hγ0, hγ2, -, -, -⟩ := hadm c hc
  set M : Ω → Measure ℂ := Mfam c.1 with hMdef
  have hM : IsGMCOf P X c.1 M := hMfam c.1 ⟨hγ0, hγ2⟩
  set Bad : Set ℂ := coulombBadRegion c.2.1 ρ with hBad
  have hBadm : MeasurableSet Bad := measurableSet_coulombBadRegion c.2.1 ρ
  set G : ℂ → ℝ≥0∞ := coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r with hG
  set F : ℂ → ℝ≥0∞ := coulombWeight c.1 c.2.2.1 c.2.1 c.2.2.2 with hF
  have hGm : Measurable G := measurable_coulombCutoffWeight _ _ _ _ _ _
  have hFm : Measurable F := measurable_coulombWeight _ _ _ _
  set badr : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Bad, G x ∂regularizedGMC P Xc c.1 r ω with hbadr
  set goodr : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Badᶜ, G x ∂regularizedGMC P Xc c.1 r ω with hgoodr
  set badl : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Bad, F x ∂M ω with hbadl
  set goodl : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in Badᶜ, F x ∂M ω with hgoodl
  -- moments of the bad parts
  have hB1 : ∫⁻ ω, badr ω ^ tst ∂P ≤ A1 * ENNReal.ofReal (ρ ^ κ1) :=
    hbad1 c hc ρ hρ hρle1 r hrlog
  have hB2 : ∫⁻ ω, badl ω ^ tst ∂P ≤ A2 * ENNReal.ofReal (ρ ^ κ2) :=
    hbad2 c hc ρ hρ hρle2
  -- measurability
  have hsetm : ∀ (s : Set ℂ) (hs : MeasurableSet s) (f : ℂ → ℝ≥0∞) (hf : Measurable f) (r' : ℝ),
      Measurable fun ω => ∫⁻ x in s, f x ∂regularizedGMC P Xc c.1 r' ω := by
    intro s hs f hf r'
    have h := (Measure.measurable_lintegral (hf.indicator hs)).comp
      (regularizedGMC_measurable P X hX Xc hXc c.1 r')
    convert h using 1
    funext ω
    simp only [Function.comp_apply, lintegral_indicator hs]
  have hbadrm : AEMeasurable badr P := (hsetm Bad hBadm G hGm r).aemeasurable
  have hgoodrm : AEMeasurable goodr P := (hsetm Badᶜ hBadm.compl G hGm r).aemeasurable
  have hbadlm : AEMeasurable badl P :=
    gmc_setLIntegral_aemeasurable P X hX c.1 hγ0 hγ2 M hM F hFm Bad hBadm
  have hgoodlm : AEMeasurable goodl P :=
    gmc_setLIntegral_aemeasurable P X hX c.1 hγ0 hγ2 M hM F hFm Badᶜ hBadm.compl
  -- finiteness
  have hfin_of_moment : ∀ f : Ω → ℝ≥0∞, AEMeasurable f P → ∫⁻ ω, f ω ^ tst ∂P < ⊤ →
      ∀ᵐ ω ∂P, f ω ≠ ⊤ := by
    intro f hf hint
    filter_upwards [ae_lt_top' (hf.pow_const tst) hint.ne] with ω hω htop
    rw [htop, ENNReal.top_rpow_of_pos htst] at hω
    exact lt_irrefl _ hω
  have hbr : ∀ᵐ ω ∂P, badr ω ≠ ⊤ := hfin_of_moment badr hbadrm
    (lt_of_le_of_lt hB1 (ENNReal.mul_lt_top hA1 ENNReal.ofReal_lt_top))
  have hbl : ∀ᵐ ω ∂P, badl ω ≠ ⊤ := hfin_of_moment badl hbadlm
    (lt_of_le_of_lt hB2 (ENNReal.mul_lt_top hA2 ENNReal.ofReal_lt_top))
  -- bounds on the good region
  have hgoodbd : ∀ x ∈ Badᶜ, x ≠ 0 → G x ≤ ENNReal.ofReal L ∧ F x ≤ ENNReal.ofReal L ∧
      |(G x).toReal - (F x).toReal| ≤ L * Real.exp (-r) := by
    intro x hx hx0
    rw [mem_coulombBadRegion_compl] at hx
    exact hL c.1 c.2.2.1 c.2.1 c.2.2.2 r x hr0' (hZc c hc) (hEα c hc) (hEinf c hc) hx.1 hx.2 hx0
  have hFbulk : ∀ x ∈ Badᶜ, F x ≤ ENNReal.ofReal L2 := by
    intro x hx
    rw [mem_coulombBadRegion_compl] at hx
    refine (coulombWeight_le_bulk c.1 c.2.2.1 c.2.1 c.2.2.2 hρ hρ1' (by positivity) hx.1
      hx.2).trans (ENNReal.ofReal_le_ofReal (real_rpow_le_rpow_of_le_of_le ?_ ?_ ?_ ?_))
    · rw [le_div_iff₀ hρ]
      have : (1 : ℝ) ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; linarith
      linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => norm_nonneg (c.2.1 j))]
    · exact div_le_div_of_nonneg_right (by linarith [hZc c hc]) hρ.le
    · exact add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _)
    · linarith [hEsum c hc, (by
        have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (c.1 * c.2.2.1 j))
        calc ∑ j, |c.1 * c.2.2.1 j| ≤ ∑ _j : Fin N, E := Finset.sum_le_sum fun j _ => hEα c hc j
          _ = N * E := by simp : ∑ j, |c.1 * c.2.2.1 j| ≤ N * E), hEinf c hc]
  have hfinr : ∀ᵐ ω ∂P, IsFiniteMeasure (regularizedGMC P Xc c.1 r ω) :=
    regularizedGMC_finite_ae P X hX Xc hXc c.1 r
  have hgr : ∀ᵐ ω ∂P, goodr ω ≠ ⊤ := by
    filter_upwards [hfinr] with ω hω
    have hne0 : ∀ᵐ x ∂(regularizedGMC P Xc c.1 r ω).restrict Badᶜ, x ≠ 0 :=
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp
        (regularizedGMC_singleton_eq_zero P Xc c.1 r ω 0))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := L))
      (measure_ne_top (regularizedGMC P Xc c.1 r ω) Badᶜ)) ?_
    rw [hgoodr]
    simp only []
    rw [← setLIntegral_const]
    refine lintegral_mono_ae ?_
    filter_upwards [hne0, ae_restrict_mem hBadm.compl] with x hx0 hx
    exact (hgoodbd x hx hx0).1
  have hgl : ∀ᵐ ω ∂P, goodl ω ≠ ⊤ := by
    refine Eventually.of_forall fun ω => ?_
    have := hM.1 ω
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := L2))
      (measure_ne_top (M ω) Badᶜ)) ?_
    rw [hgoodl]
    simp only []
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hBadm.compl fun x hx => hFbulk x hx
  -- the splitting
  have hZr : ∀ᵐ ω ∂P, regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω =
      badr ω + goodr ω := Eventually.of_forall fun ω => by
    rw [regularizedCoulombMass_eq_lintegral P X hX Xc hXc, hbadr, hgoodr]
    exact (lintegral_add_compl _ hBadm).symm
  have hZ : ∀ᵐ ω ∂P, coulombMass c.1 (M ω) c.2.2.1 c.2.1 c.2.2.2 = badl ω + goodl ω :=
    Eventually.of_forall fun ω => by
      rw [coulombMass_eq_lintegral_coulombWeight, hbadl, hgoodl]
      exact (lintegral_add_compl _ hBadm).symm
  have hgm : AEMeasurable (fun ω => ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal|) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
      ((ENNReal.measurable_toReal.comp_aemeasurable hgoodrm).sub
        (ENNReal.measurable_toReal.comp_aemeasurable hgoodlm)))
  refine (prob_edist_le_of_split P _ _ badr badl goodr goodl hZr hZ hbr hbl hgr hgl hbadrm
    hbadlm hgm he hεe htst).trans ?_
  -- the good part in L¹
  set h : ℂ → ℝ := Badᶜ.indicator (fun x => (F x).toReal) with hh
  have hhm : Measurable h := (ENNReal.measurable_toReal.comp hFm).indicator hBadm.compl
  have hhb : ∀ x, |h x| ≤ L2 := by
    intro x
    by_cases hx : x ∈ Badᶜ
    · rw [hh, Set.indicator_of_mem hx, abs_of_nonneg ENNReal.toReal_nonneg]
      calc (F x).toReal ≤ (ENNReal.ofReal L2).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hFbulk x hx)
        _ = L2 := ENNReal.toReal_ofReal (by positivity)
    · rw [hh, Set.indicator_of_notMem hx, abs_zero]
      positivity
  have hhK : ∀ x ∉ closedBall (0 : ℂ) (1 / ρ), h x = 0 := by
    intro x hx
    have hxB : x ∉ Badᶜ := by
      rw [mem_coulombBadRegion_compl]
      rintro ⟨h1, -⟩
      exact hx (by rw [mem_closedBall, dist_zero_right]; exact h1)
    rw [hh, Set.indicator_of_notMem hxB]
  have hatom0 : ∀ᵐ ω ∂P, M ω {0} = 0 := gmc_singleton_mass_eq_zero_ae P X hX c.1 hγ0 hγ2 M hM 0
  have hgoodL1 : ∫⁻ ω, ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal| ∂P ≤
      ENNReal.ofReal (L * Real.exp (-r)) * gmcReferenceMeasure Set.univ + Sρ r := by
    have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal| ≤
        ENNReal.ofReal (L * Real.exp (-r)) * regularizedGMC P Xc c.1 r ω Badᶜ +
          ENNReal.ofReal |∫ x, h x ∂regularizedGMC P Xc c.1 r ω - ∫ x, h x ∂M ω| := by
      filter_upwards [hfinr, hatom0] with ω hω h0
      have := hM.1 ω
      exact goodPart_ofReal_abs_le _ _ Badᶜ hBadm.compl G F hGm hFm L (L * Real.exp (-r))
        (by positivity) hgoodbd (regularizedGMC_singleton_eq_zero P Xc c.1 r ω 0) h0
    have hmass : ∫⁻ ω, regularizedGMC P Xc c.1 r ω Badᶜ ∂P ≤ gmcReferenceMeasure Set.univ := by
      have h1 := regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc c.1 r
        (Badᶜ.indicator fun _ => 1) (measurable_const.indicator hBadm.compl)
      simp only [lintegral_indicator_const hBadm.compl, one_mul] at h1
      rw [h1]
      exact measure_mono (Set.subset_univ _)
    have hdiff : ∫⁻ ω, ENNReal.ofReal |∫ x, h x ∂regularizedGMC P Xc c.1 r ω - ∫ x, h x ∂M ω|
        ∂P ≤ Sρ r := by
      rw [hSρ]
      refine le_iSup_of_le c.1 ?_
      refine le_iSup_of_le ⟨c, hc, rfl⟩ ?_
      refine le_iSup_of_le h ?_
      refine le_iSup_of_le hhm ?_
      refine le_iSup_of_le hhb ?_
      exact le_iSup_of_le hhK le_rfl
    calc ∫⁻ ω, ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal| ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (L * Real.exp (-r)) * regularizedGMC P Xc c.1 r ω Badᶜ +
            ENNReal.ofReal |∫ x, h x ∂regularizedGMC P Xc c.1 r ω - ∫ x, h x ∂M ω|) ∂P :=
          lintegral_mono_ae hpt
      _ = ENNReal.ofReal (L * Real.exp (-r)) * ∫⁻ ω, regularizedGMC P Xc c.1 r ω Badᶜ ∂P +
            ∫⁻ ω, ENNReal.ofReal |∫ x, h x ∂regularizedGMC P Xc c.1 r ω - ∫ x, h x ∂M ω| ∂P := by
          have hMm : AEMeasurable (fun ω => regularizedGMC P Xc c.1 r ω Badᶜ) P :=
            ((Measure.measurable_coe hBadm.compl).comp
              (regularizedGMC_measurable P X hX Xc hXc c.1 r)).aemeasurable
          have hmm : AEMeasurable (fun ω => ENNReal.ofReal (L * Real.exp (-r)) *
              regularizedGMC P Xc c.1 r ω Badᶜ) P := aemeasurable_const.mul hMm
          rw [lintegral_add_left' hmm, lintegral_const_mul'' _ hMm]
      _ ≤ _ := add_le_add (mul_le_mul' le_rfl hmass) hdiff
  -- assemble the three probabilities
  have hp1 : (∫⁻ ω, badr ω ^ tst ∂P) / a ^ tst ≤ θ / 3 := by
    refine ENNReal.div_le_of_le_mul ?_
    exact hB1.trans (le_of_lt (by simpa [hδ1, mul_comm] using hρb1))
  have hp2 : (∫⁻ ω, badl ω ^ tst ∂P) / a ^ tst ≤ θ / 3 := by
    refine ENNReal.div_le_of_le_mul ?_
    exact hB2.trans (le_of_lt (by simpa [hδ1, mul_comm] using hρb2))
  have hp3 : (∫⁻ ω, ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal| ∂P) / a ≤ θ / 3 := by
    refine ENNReal.div_le_of_le_mul ?_
    exact hgoodL1.trans (le_of_lt (by simpa [hδ3, mul_comm] using hr0 r hrr0))
  calc _ ≤ θ / 3 + θ / 3 + θ / 3 := add_le_add (add_le_add hp1 hp2) hp3
    _ = θ := ENNReal.add_thirds θ

end DOZZ.Proofs
