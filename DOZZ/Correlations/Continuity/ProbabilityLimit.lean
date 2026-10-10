/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Continuity.CutoffContinuity
public import DOZZ.GMC.SharpMoments.MomentConvergence
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Uniform approximation in probability by parameter-continuous random variables
preserves parameter continuity in probability. -/
theorem uniform_approximation_in_measure_continuous
    {Ω T : Type*} [MeasurableSpace Ω] [TopologicalSpace T]
    (P : Measure Ω) (F : ℝ → T → Ω → ℝ) (G : T → Ω → ℝ) (q₀ : T)
    (happrox : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun r => ⨆ q, P {ω | ε ≤ dist (F r q ω) (G q ω)}) atTop (𝓝 0))
    (hcont : ∀ r, 0 ≤ r → TendstoInMeasure P (F r) (𝓝 q₀) (F r q₀)) :
    TendstoInMeasure P G (𝓝 q₀) (G q₀) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ3 : 0 < δ / 3 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨r, hr, hr0⟩ := ((happrox (ε / 3) (by linarith)).eventually
    (Iio_mem_nhds hδ3) |>.and (eventually_ge_atTop (0 : ℝ))).exists
  have hmid := (tendstoInMeasure_iff_dist.mp (hcont r hr0)) (ε / 3) (by linarith)
  filter_upwards [hmid.eventually (Iio_mem_nhds hδ3)] with q hq
  have hset : {ω | ε ≤ dist (G q ω) (G q₀ ω)} ⊆
      ({ω | ε / 3 ≤ dist (F r q ω) (G q ω)} ∪
        {ω | ε / 3 ≤ dist (F r q ω) (F r q₀ ω)}) ∪
          {ω | ε / 3 ≤ dist (F r q₀ ω) (G q₀ ω)} := by
    intro ω hω
    have htri : dist (G q ω) (G q₀ ω) ≤ dist (F r q ω) (G q ω) +
        dist (F r q ω) (F r q₀ ω) + dist (F r q₀ ω) (G q₀ ω) := by
      calc _ ≤ dist (G q ω) (F r q ω) + dist (F r q ω) (G q₀ ω) := dist_triangle _ _ _
        _ ≤ dist (G q ω) (F r q ω) +
            (dist (F r q ω) (F r q₀ ω) + dist (F r q₀ ω) (G q₀ ω)) :=
          add_le_add le_rfl (dist_triangle _ _ _)
        _ = _ := by rw [dist_comm (G q ω) (F r q ω), add_assoc]
    rcases le_of_three_le_sum hω htri with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  calc P {ω | ε ≤ dist (G q ω) (G q₀ ω)} ≤ _ := measure_mono hset
    _ ≤ (P {ω | ε / 3 ≤ dist (F r q ω) (G q ω)} +
        P {ω | ε / 3 ≤ dist (F r q ω) (F r q₀ ω)}) +
          P {ω | ε / 3 ≤ dist (F r q₀ ω) (G q₀ ω)} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ δ / 3 + δ / 3 + δ / 3 := add_le_add
      (add_le_add ((le_iSup _ q).trans hr.le) hq.le) ((le_iSup _ q₀).trans hr.le)
    _ = δ := ENNReal.add_thirds δ

/-- The actual singular Coulomb masses vary continuously in probability; the uniform cutoff limit
(`regularizedCoulombMass_tendstoInProbability_uniform`) is taken on the entire compact
parameter set. -/
theorem coulombMass_continuous_in_measure_on_compact
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : ℝ → Ω → Measure ℂ)
    (hM : ∀ γ ∈ Ioo (0 : ℝ) 2, IsGMCOf P X γ (M γ))
    (S : Set (ContinuityCoulombParameter N)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1) (c₀ : S) :
    TendstoInMeasure P (fun c : S => fun ω =>
      (coulombMass c.val.1 (M c.val.1 ω) c.val.2.2.1 c.val.2.1 c.val.2.2.2).toReal)
      (𝓝 c₀) (fun ω =>
        (coulombMass c₀.val.1 (M c₀.val.1 ω) c₀.val.2.2.1 c₀.val.2.1 c₀.val.2.2.2).toReal) := by
  let partition := continuityChartPartition
  let F : ℝ → S → Ω → ℝ := fun r c ω =>
    (regularizedCoulombMass P Xc c.val.1 partition c.val.2.2.1 c.val.2.1 c.val.2.2.2 r ω).toReal
  have hFm : ∀ r c, Measurable (F r c) := fun r c => by
    simp only [F, regularizedCoulombMass_real_eq_integral_test P X hX Xc hXc]
    exact DOZZ.Assembly.regularizedGMC_integral_measurable P X hX Xc hXc _ r _
      (continuityCutoffTest_measurable partition r c.val)
  apply uniform_approximation_in_measure_continuous P F _ c₀
  · intro ε hε
    have h := regularizedCoulombMass_tendstoInProbability_uniform P X hX Xc hXc
      partition M hM S hS hadm (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => zero_le) (fun r => iSup_le fun (c : S) => ?_)
    refine le_iSup_of_le c.val (le_iSup_of_le c.property ?_)
    apply measure_mono
    intro ω hω
    change ENNReal.ofReal ε ≤ edist (F r c ω)
      (coulombMass c.val.1 (M c.val.1 ω) c.val.2.2.1 c.val.2.1 c.val.2.2.2).toReal
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hω
  · intro r hr
    exact DOZZ.Assembly.tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P (F r) (F r c₀)
      (fun c => (hFm r c).aestronglyMeasurable) (hFm r c₀).aestronglyMeasurable
      (regularizedCoulombMass_L1_continuous_on_compact P X hX Xc hXc partition r hr S hS c₀)

/-- Positive finite limits allow both the random base and the real exponent to
vary. In particular there is no restriction at exponent zero. -/
theorem continuity_tendstoInMeasure_varying_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ≥0∞) (g : Ω → ℝ≥0∞) (p : ℕ → ℝ) (p₀ : ℝ)
    (hf : ∀ n, AEMeasurable (f n) P)
    (hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤) (hgpos : ∀ᵐ ω ∂P, g ω ≠ 0)
    (hconv : TendstoInMeasure P (fun n ω => (f n ω).toReal) atTop
      (fun ω => (g ω).toReal)) (hp : Tendsto p atTop (𝓝 p₀)) :
    TendstoInMeasure P (fun n ω => (f n ω ^ p n).toReal) atTop
      (fun ω => (g ω ^ p₀).toReal) := by
  have hreal : ∀ n, AEStronglyMeasurable (fun ω => (f n ω).toReal) P :=
    fun n => (hf n).ennreal_toReal.aestronglyMeasurable
  have hpow : ∀ n, AEStronglyMeasurable (fun ω => (f n ω ^ p n).toReal) P :=
    fun n => ((hf n).pow_const (p n)).ennreal_toReal.aestronglyMeasurable
  rw [exists_seq_tendstoInMeasure_atTop_iff hpow]
  intro ns hns
  obtain ⟨ns', hns', hae⟩ := (exists_seq_tendstoInMeasure_atTop_iff hreal).mp hconv ns hns
  refine ⟨ns', hns', ?_⟩
  filter_upwards [hae, hgfin, hgpos] with ω hω hfin hpos
  have hp' := hp.comp ((hns.comp hns').tendsto_atTop)
  have h := (Real.continuousAt_rpow ((g ω).toReal, p₀)
    (Or.inl (ENNReal.toReal_pos hpos hfin).ne')).tendsto.comp (hω.prodMk_nhds hp')
  simpa only [Function.comp_def, ← ENNReal.toReal_rpow] using h

/-- Subcritical root charges give a strictly positive finite actual Coulomb mass
on one probability-one event, independently of the chosen moment power. -/
theorem continuity_coulombMass_positive_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (hα : ∀ k, α k < Q γ) (hinf : αinf < Q γ) :
    ∀ᵐ ω ∂P, 0 < coulombMass γ (M ω) α z αinf ∧ coulombMass γ (M ω) α z αinf ≠ ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  have hm := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (4 / γ ^ 2) := Ioo_mem_nhdsGT (by positivity)
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (2 / γ * (Q γ - αinf)) :=
    Ioo_mem_nhdsGT (mul_pos (div_pos two_pos hγ) (sub_pos.mpr hinf))
  have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, t ∈ Ioo 0 (2 / γ * (Q γ - α k)) :=
    eventually_all.mpr fun k => Ioo_mem_nhdsGT
      (mul_pos (div_pos two_pos hγ) (sub_pos.mpr (hα k)))
  obtain ⟨t, ht⟩ := (e1.and (e2.and e3)).exists
  have htfin := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf t
    ht.1.1 ht.1.2 (fun k => (ht.2.2 k).2) ht.2.1.2
  have hf : ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf ≠ ⊤ := by
    filter_upwards [ae_lt_top' (hm.pow_const t) htfin.ne] with ω hω htop
    rw [htop, ENNReal.top_rpow_of_pos ht.1.1] at hω
    exact lt_irrefl _ hω
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  have hsum : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hc : 0 < ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
      ENNReal.ofReal ((1 + 2 * ∑ j, ‖z j‖ + 2) ^ (-|γ * αinf|)) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hB := gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM
    (((1 + 2 * ∑ j, ‖z j‖ + 1 : ℝ)) : ℂ) (1 / 8) (by norm_num)
  filter_upwards [hf, hB] with ω hω hBω
  exact ⟨lt_of_lt_of_le (ENNReal.mul_pos hc.ne' hBω.ne')
    (coulombMass_ge_exterior_ball (M ω) γ α z αinf hR hzR), hω⟩

end DOZZ.Proofs
