/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.ComparisonLimit
public import DOZZ.ShiftEquations.Strip.ZeroMode
public import DOZZ.GMC.Moments.RhoCoulomb
public import DOZZ.Correlations.Symmetry.ReflectionMomentSwap

/-! The lastone Coulomb small-power limit on the supplied equator-GMC probability space. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- The critical two-root Coulomb moment tends to two. A fixed subcritical one-root mass
controls the error outside the critical half disk. -/
theorem lastone_coulomb_smallPower_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ ε : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hε : 0 < ε ∧ ε < Q γ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, coulombMass γ (M ω) ![Q γ - ν, ε] ![0, 1] (Q γ - ε) ^ (ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 2) := by
  let : IsProbabilityMeasure P := hX.1
  have hQ : 0 < Q γ := hε.1.trans hε.2
  have hb : 0 < Q γ - ε := sub_pos.mpr hε.2
  have hbulk : 0 < 4 / γ ^ 2 := by positivity
  have hins : 0 < 2 / γ * ε := mul_pos (by positivity) hε.1
  have hinf : 0 < 2 / γ * (Q γ - ε) := mul_pos (by positivity) hb
  let t : ℝ := min 1 (min (4 / γ ^ 2) (min (2 / γ * ε) (2 / γ * (Q γ - ε))))
  have ht : 0 < t := lt_min zero_lt_one (lt_min hbulk (lt_min hins hinf))
  obtain ⟨q, hq, hqt⟩ := exists_between ht
  -- A strict subcritical order leaves slack in every threshold.
  let q₀ := q / 2
  have hq₀ : 0 < q₀ := div_pos hq (by norm_num)
  have hq₀1 : q₀ ≤ 1 := by
    have ht1 : t ≤ 1 := min_le_left _ _
    dsimp [q₀]
    linarith
  have hUp : ∫⁻ ω, coulombMass γ (M ω) ![ε] ![1] (Q γ - ε) ^ (2 * q₀) ∂P < ⊤ := by
    have horder : 2 * q₀ < t := by dsimp [q₀]; linarith
    have htb : t ≤ 4 / γ ^ 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hti : t ≤ 2 / γ * ε :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have htinf : t ≤ 2 / γ * (Q γ - ε) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hf := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM
      (![1] : Fin 1 → ℂ) (fun _ _ _ => Subsingleton.elim _ _) ![ε] (Q γ - ε) (2 * q₀)
      (by positivity) (horder.trans_le htb) (fun k => by
        fin_cases k
        change 2 * q₀ < 2 / γ * (Q γ - ε)
        exact horder.trans_le htinf) (by
          simpa only [sub_sub_cancel] using horder.trans_le hti)
    simpa only [ENNReal.rpow_eq_pow] using hf
  let R : ℝ → Ω → ℝ≥0∞ := fun ν => localSingularMass M (fun _ => 1) 0 γ (Q γ - ν)
  let C : ℝ → Ω → ℝ≥0∞ := fun ν ω => coulombMass γ (M ω) ![Q γ - ν, ε] ![0, 1] (Q γ - ε)
  let U : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) ![ε] ![1] (Q γ - ε)
  have hR (ν) : AEMeasurable (R ν) P :=
    localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM
      (fun _ => 1) measurable_const 0 (Q γ - ν)
  have hU : AEMeasurable U P := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _
  have he : Tendsto (fun ν : ℝ => ν / γ) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (fun ν : ℝ => ν) (𝓝 0) (𝓝 0)).div_const γ).mono_left nhdsWithin_le_nhds
  have hepos : ∀ᶠ ν : ℝ in 𝓝[>] 0, 0 < ν / γ := by
    filter_upwards [self_mem_nhdsWithin] with ν hν
    exact div_pos hν hγ
  have hsmall : ∀ᶠ ν : ℝ in 𝓝[>] 0, 0 < ν ∧ ν < Q γ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hQ).filter_mono nhdsWithin_le_nhds] with ν hν hνQ
    exact ⟨hν, hνQ⟩
  obtain ⟨D, hD, hDb⟩ := lastone_origin_inverse_bound P X M γ hγ hγ2 hX hM
    (2 * q₀) (by positivity)
  have hRi : ∀ᶠ ν in 𝓝[>] 0, ∫⁻ ω, R ν ω ^ (-2 * q₀) ∂P ≤ D := by
    filter_upwards [hsmall] with ν hν
    simpa only [neg_mul] using hDb (Q γ - ν) (by linarith)
  let k₁ : ℝ≥0∞ := ENNReal.ofReal (1 / 2 : ℝ) ^ (γ * ε)
  let k₂ : ℝ≥0∞ := 2 ^ (γ * ε)
  let k₃ : ℝ≥0∞ := 2 ^ (γ * Q γ)
  have hk₁0 : k₁ ≠ 0 := by
    dsimp [k₁]
    simp only [ENNReal.rpow_eq_zero_iff]
    norm_num
  have hk₁T : k₁ ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.ofReal_ne_top
  have hk₂0 : k₂ ≠ 0 := by
    dsimp [k₂]
    simp only [ENNReal.rpow_eq_zero_iff]
    norm_num
  have hk₂T : k₂ ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hk₃T : k₃ ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero (by norm_num) (by norm_num)
  have hbounds : ∀ᶠ ν in 𝓝[>] 0, ∀ᵐ ω ∂P,
      k₁ * R ν ω ≤ C ν ω ∧ C ν ω ≤ k₂ * R ν ω + k₃ * U ω := by
    filter_upwards [hsmall] with ν hν
    filter_upwards [equatorGFF_GMC_origin_null_ae P X hX γ hγ hγ2 M hM] with ω hω
    exact lastone_coulombMass_bounds γ (Q γ - ν) ε (Q γ - ε)
      (mul_pos hγ (by linarith)) (mul_nonneg hγ.le hε.1.le)
      (mul_le_mul_of_nonneg_left (by linarith) hγ.le) (M ω) hω
  exact lastone_mass_comparison_limit P R C U hR hU (𝓝[>] 0) (fun ν => ν / γ)
    he hepos k₁ k₂ k₃ hk₁0 hk₁T hk₂0 hk₂T hk₃T q₀ 2 hq₀ hq₀1 D hD hRi hUp
    (lastone_origin_moment_finite P X M γ hγ hγ2 hX hM) hbounds
    (lastone_origin_smallPower_limit P X M γ hγ hγ2 hX hM)

/-- Swapping the finite roots transports the critical Coulomb limit to the rho frame. -/
theorem lastone_rho_smallPower_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ ε : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hε : 0 < ε ∧ ε < Q γ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, rho γ (M ω) ε (Q γ - ν) (Q γ - ε) ^ (ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 2) := by
  apply (lastone_coulomb_smallPower_limit P X M γ ε hγ hγ2 hε hX hM).congr
  intro ν
  have hswap := rho_moment_swap12 P X M γ ε (Q γ - ν) (Q γ - ε) hγ hγ2 hX hM
  simp only [lastone_sExp, neg_div, neg_neg] at hswap
  rw [hswap]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [gmc_rho_eq_coulombMass_ae P X hX γ hγ hγ2 M hM
    (Q γ - ν) ε (Q γ - ε)] with ω hω
  rw [hω]

end DOZZ.Proofs
