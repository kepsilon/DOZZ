module

public import DOZZ.GMC.WeightedCutoff.BoundedFineMass
public import DOZZ.GMC.WeightedCutoff.BoundedCoarseMass
public import DOZZ.GMC.WeightedCutoff.RadiusDecomposition
public import DOZZ.GMC.WeightedCutoff.LowerOrder

/-! # Uniform weighted moments at radii bounded away from zero -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMoment_compact_gamma_large_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    (K : Set ℂ) (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ E : ℝ≥0∞, E < ⊤ ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ z ∈ K, ∀ R δ : ℝ,
      1 / 8 ≤ R → R ≤ r₀ → 0 < δ → δ ≤ R →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤ E := by
  let _ := hX.1
  classical
  rcases Set.eq_empty_or_nonempty Γ with hΓe | hΓn
  · refine ⟨0, by simp, ?_⟩
    simp [hΓe]
  rcases Set.eq_empty_or_nonempty T with hTe | hTn
  · refine ⟨0, by simp, ?_⟩
    simp [hTe]
  obtain ⟨q, hq, hqcrit, hqorders⟩ := exists_weighted_cutoff_order_cap Γ hΓ hΓn hΓ2 T hT hTn
    (fun γ hγ t ht => lt_of_lt_of_le (hTadm γ hγ t ht).2 (min_le_left _ _))
  obtain ⟨B₀, hB₀, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  let B : ℝ := B₀ + r₀ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨Dfine, hDfine, hfine⟩ := regularizedGMC_bounded_ball_moment_compact_gamma_fine
    P X hX Xc hXc Γ hΓ (fun γ hγ => (hΓ2 hγ).1) q hq hqcrit B hB
  obtain ⟨Dcoarse, hDcoarse, hcoarse⟩ := regularizedGMC_bounded_ball_moment_coarse_uniform_gamma
    P X hX Xc hXc q hq B r₀ hB.le hr₀
  obtain ⟨W, hW, hweight⟩ := exists_compact_cutoff_weight_bound Γ hΓ T hT
    (1 / 8 : ℝ) (2 * r₀) (by norm_num)
  obtain ⟨Cs, hCs, hsmall⟩ := cutoffWeightedGmcBallMoment_compact_gamma_small_bound
    P X hX Xc hXc Γ hΓ hΓ2 T hT hTadm K hK
  obtain ⟨L, U, hL, hU, hupper, hlower⟩ := exists_compact_cutoff_scale_bounds
    Γ hΓ (fun γ hγ => (hΓ2 hγ).1) T hT (1 / 8 : ℝ) r₀ (by norm_num)
  let c : ℝ≥0∞ := ENNReal.ofReal W
  have hcq : c ^ q < ⊤ := lt_top_iff_ne_top.mpr
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
  let Ef : ℝ≥0∞ := 1 + c ^ q * Dfine
  let Ec : ℝ≥0∞ := 1 + c ^ q * Dcoarse
  have hEf : Ef < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top hcq hDfine⟩
  have hEc : Ec < ⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.one_lt_top, ENNReal.mul_lt_top hcq hDcoarse⟩
  let Ei : ℝ≥0∞ := ENNReal.ofReal (Cs * U)
  let Efg : ℝ≥0∞ := (2 : ℝ≥0∞) ^ q * (Ei + Ef)
  have htwo : (2 : ℝ≥0∞) ^ q < ⊤ := lt_top_iff_ne_top.mpr
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num))
  have hEfg : Efg < ⊤ := ENNReal.mul_lt_top htwo
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, hEf⟩)
  refine ⟨Efg + Ec, ENNReal.add_lt_top.mpr ⟨hEfg, hEc⟩, ?_⟩
  intro γ hγ t ht z hz R δ hRa hR₀ hδ hδR
  have hp0 := (hTadm γ hγ t ht).1
  have hpq := hqorders t ht
  have hzB : ‖z‖ + R ≤ B := by
    have hn := hnorm z hz
    dsimp [B]
    linarith
  let f : Ω → ℝ≥0∞ := fun ω => regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball 0 B)
  have hf : AEMeasurable f P := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
    (Real.log (1 / δ)) (Metric.ball 0 B) Metric.isOpen_ball.measurableSet
  by_cases hδfine : δ ≤ 1 / 8
  · let a : Ω → ℝ≥0∞ := fun ω => cutoffWeightedGmcBallMass P Xc γ t.1 z (1 / 8) δ ω
    let b : Ω → ℝ≥0∞ := fun ω => c * f ω
    have ha : AEMeasurable (fun ω => a ω ^ t.2) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        (cutoffWeightedGmcBallMass_aemeasurable P X hX Xc hXc γ t.1 z (1 / 8) δ)
    have hinner : (∫⁻ ω, a ω ^ t.2 ∂P) ≤ Ei := by
      have h := hsmall γ hγ t ht z hz (1 / 8) δ (by norm_num) (by norm_num) hδ hδfine
      apply h.trans
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hupper γ hγ t ht) hCs.le)
    have houter : (∫⁻ ω, b ω ^ t.2 ∂P) ≤ Ef :=
      lintegral_lower_rpow_const_mul_le P f hf c Dfine t.2 q hp0.le hpq
        (hfine γ hγ δ hδ hδfine)
    have hmass : ∀ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ≤ a ω + b ω :=
      cutoffWeightedGmcBallMass_le_inner_add_outer P Xc γ t.1 (1 / 8) r₀ W B R δ z
        hRa hR₀ hδ hδR hzB (hweight γ hγ t ht)
    have hmain : (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤ Efg := by
      calc
        _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ q * (a ω ^ t.2 + b ω ^ t.2) ∂P := by
          apply lintegral_mono
          intro ω
          exact (ENNReal.rpow_le_rpow (hmass ω) hp0.le).trans
            (ennreal_rpow_add_le_uniform_order_cap _ _ t.2 q hp0.le hpq)
        _ = (2 : ℝ≥0∞) ^ q * ((∫⁻ ω, a ω ^ t.2 ∂P) + ∫⁻ ω, b ω ^ t.2 ∂P) := by
          rw [lintegral_const_mul' _ _ htwo.ne, lintegral_add_left' ha]
        _ ≤ Efg := mul_le_mul_right (add_le_add hinner houter) _
    exact hmain.trans (le_add_of_nonneg_right (by positivity))
  · have hδa : 1 / 8 ≤ δ := le_of_not_ge hδfine
    have houter : (∫⁻ ω, (c * f ω) ^ t.2 ∂P) ≤ Ec :=
      lintegral_lower_rpow_const_mul_le P f hf c Dcoarse t.2 q hp0.le hpq
        (hcoarse γ (hΓ2 hγ).1 (hΓ2 hγ).2 δ hδa (hδR.trans hR₀))
    have hmass : ∀ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ≤ c * f ω :=
      cutoffWeightedGmcBallMass_le_coarse_weight P Xc γ t.1 (1 / 8) r₀ W B R δ z
        hR₀ hδa hδR hzB (hweight γ hγ t ht)
    have hmain := (lintegral_mono (fun ω => ENNReal.rpow_le_rpow (hmass ω) hp0.le)).trans houter
    exact hmain.trans (le_add_of_nonneg_left (by positivity))

end DOZZ.Proofs
