/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.CompetitorPower

/-! Adding the noncritical mass does not change the moment residue of the three-to-two residue
bridge. -/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- A uniform higher moment gives integrability and a uniform bound for the varying powers. -/
theorem residue_integral_lower_power_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (q r : ℝ) (hq : 0 ≤ q) (hqr : q ≤ r)
    (hr : Integrable (fun ω => Y ω ^ r) P) :
    Integrable (fun ω => Y ω ^ q) P ∧
      (∫ ω, Y ω ^ q ∂P) ≤ 1 + ∫ ω, Y ω ^ r ∂P := by
  have hb : Integrable (fun ω => 1 + Y ω ^ r) P := (integrable_const _).add hr
  have hdom : ∀ᵐ ω ∂P, ‖Y ω ^ q‖ ≤ 1 + Y ω ^ r := by
    filter_upwards [hpos] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hω _)]
    exact residue_rpow_le_one_add (Y ω) q r hω hq hqr
  have hi : Integrable (fun ω => Y ω ^ q) P :=
    hb.mono' (hY.pow_const q).aestronglyMeasurable hdom
  refine ⟨hi, ?_⟩
  calc (∫ ω, Y ω ^ q ∂P) ≤ ∫ ω, 1 + Y ω ^ r ∂P :=
      integral_mono_ae hi hb (hpos.mono fun ω hω => residue_rpow_le_one_add (Y ω) q r hω hq hqr)
    _ = _ := by rw [integral_add (integrable_const _) hr]; simp

/-- A nonnegative competitor with uniformly bounded moments cannot change the critical
residue. The adjustable deterministic comparison replaces an independence assumption. -/
theorem residue_addition_preserves_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A R : ℝ → Ω → ℝ) (q : ℝ → ℝ) (β d₀ C L : ℝ)
    (hd₀ : 0 < d₀)
    (hA : ∀ d, 0 < d → d < d₀ → AEMeasurable (A d) P)
    (hR : ∀ d, 0 < d → d < d₀ → AEMeasurable (R d) P)
    (hAnn : ∀ d, 0 < d → d < d₀ → ∀ᵐ ω ∂P, 0 ≤ A d ω)
    (hRnn : ∀ d, 0 < d → d < d₀ → ∀ᵐ ω ∂P, 0 ≤ R d ω)
    (hq : ∀ d, 0 < d → d < d₀ → 0 ≤ q d ∧ q d ≤ β)
    (hiA : ∀ d, 0 < d → d < d₀ → Integrable (fun ω => A d ω ^ q d) P)
    (hiR : ∀ d, 0 < d → d < d₀ → Integrable (fun ω => R d ω ^ q d) P)
    (hC : ∀ d, 0 < d → d < d₀ → (∫ ω, R d ω ^ q d ∂P) ≤ C)
    (hlim : Tendsto (fun d => d * ∫ ω, A d ω ^ q d ∂P) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun d => d * ∫ ω, (A d ω + R d ω) ^ q d ∂P) (𝓝[>] 0) (𝓝 L) := by
  have hnear : ∀ᶠ d : ℝ in 𝓝[>] 0, 0 < d ∧ d < d₀ := by
    filter_upwards [self_mem_nhdsWithin,
      (Filter.eventually_of_mem (Iio_mem_nhds hd₀) (fun _ h => h)).filter_mono nhdsWithin_le_nhds]
      with d hd hd'
    exact ⟨hd, hd'⟩
  have hbounds (d : ℝ) (hd : 0 < d) (hd' : d < d₀) (δ : ℝ) (hδ : 0 < δ) :
      d * (∫ ω, A d ω ^ q d ∂P) ≤ d * ∫ ω, (A d ω + R d ω) ^ q d ∂P ∧
      d * (∫ ω, (A d ω + R d ω) ^ q d ∂P) ≤
        (1 + δ) ^ β * (d * ∫ ω, A d ω ^ q d ∂P) + (1 + 1 / δ) ^ β * (d * C) := by
    let U := fun ω => (1 + δ) ^ β * A d ω ^ q d + (1 + 1 / δ) ^ β * R d ω ^ q d
    have hUi : Integrable U P :=
      ((hiA d hd hd').const_mul _).add ((hiR d hd hd').const_mul _)
    have hdom : ∀ᵐ ω ∂P, (A d ω + R d ω) ^ q d ≤ U ω := by
      filter_upwards [hAnn d hd hd', hRnn d hd hd'] with ω ha hr
      exact residue_add_rpow_le_fixed _ _ _ _ _ ha hr (hq d hd hd').1 (hq d hd hd').2 hδ
    have hsumi : Integrable (fun ω => (A d ω + R d ω) ^ q d) P := by
      apply hUi.mono' (((hA d hd hd').add (hR d hd hd')).pow_const (q d)).aestronglyMeasurable
      filter_upwards [hAnn d hd hd', hRnn d hd hd', hdom] with ω ha hr hh
      dsimp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (add_nonneg ha hr) _)]
      exact hh
    constructor
    · apply mul_le_mul_of_nonneg_left _ hd.le
      apply integral_mono_ae (hiA d hd hd') hsumi
      filter_upwards [hAnn d hd hd', hRnn d hd hd'] with ω ha hr
      exact Real.rpow_le_rpow ha (le_add_of_nonneg_right hr) (hq d hd hd').1
    · have hu := integral_mono_ae hsumi hUi hdom
      have hue : (∫ ω, U ω ∂P) =
          (1 + δ) ^ β * (∫ ω, A d ω ^ q d ∂P) +
            (1 + 1 / δ) ^ β * (∫ ω, R d ω ^ q d ∂P) := by
        rw [integral_add ((hiA d hd hd').const_mul _) ((hiR d hd hd').const_mul _),
          integral_const_mul, integral_const_mul]
      rw [hue] at hu
      have hc := mul_le_mul_of_nonneg_left (hC d hd hd') (by positivity : 0 ≤ (1 + 1 / δ) ^ β)
      have hh := mul_le_mul_of_nonneg_left (hu.trans (add_le_add le_rfl hc)) hd.le
      convert hh using 1
      ring
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hnear, hlim.eventually (Ioi_mem_nhds ha)] with d hd hh
    exact hh.trans_le (hbounds d hd.1 hd.2 1 zero_lt_one).1
  · intro b hb
    have hf : Tendsto (fun δ : ℝ => (1 + δ) ^ β * L) (𝓝[>] 0) (𝓝 L) := by
      have hh : ContinuousAt (fun δ : ℝ => (1 + δ) ^ β * L) 0 :=
        ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl (by norm_num))).mul continuousAt_const
      simpa only [add_zero, Real.one_rpow, one_mul] using hh.tendsto.mono_left nhdsWithin_le_nhds
    obtain ⟨δ, hδb, hδ⟩ := ((hf.eventually (Iio_mem_nhds hb)).and self_mem_nhdsWithin).exists
    have he : Tendsto (fun d : ℝ => d) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hu := (hlim.const_mul ((1 + δ) ^ β)).add
      ((he.mul_const C).const_mul ((1 + 1 / δ) ^ β))
    have hub : ∀ᶠ d : ℝ in 𝓝[>] 0,
        (1 + δ) ^ β * (d * ∫ ω, A d ω ^ q d ∂P) + (1 + 1 / δ) ^ β * (d * C) < b := by
      have hu' : Tendsto (fun d : ℝ =>
          (1 + δ) ^ β * (d * ∫ ω, A d ω ^ q d ∂P) + (1 + 1 / δ) ^ β * (d * C))
          (𝓝[>] 0) (𝓝 ((1 + δ) ^ β * L)) := by
        simpa only [zero_mul, mul_zero, add_zero] using hu
      exact hu'.eventually (Iio_mem_nhds hδb)
    filter_upwards [hnear, hub] with d hd hh
    exact (hbounds d hd.1 hd.2 δ hδ).2.trans_lt hh

end DOZZ.Proofs
