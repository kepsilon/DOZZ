/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment

/-! # Explicit moment bounds for the Coulomb mass

Positive moments of the Coulomb mass are bounded by an explicit combination of the weighted local
moments at the roots, the moment of the mass of a bounded disk, and the weighted local moment of
the inverted measure at the origin, with constants depending only on the root separation, the
exterior radius, the root sizes and the charges. Nonpositive moments are bounded through a fixed
exterior disk. These are the inputs for uniformity over compact parameter sets. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A nonnegative power of a sum of two terms is at most `2 ^ t` times the sum of the powers. -/
theorem ennreal_add_rpow_le_two_rpow_mul (a b : ℝ≥0∞) {t : ℝ} (ht : 0 ≤ t) :
    (a + b) ^ t ≤ 2 ^ t * (a ^ t + b ^ t) := by
  have hmax : a + b ≤ 2 * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left a b) (le_max_right a b)
  calc (a + b) ^ t ≤ (2 * max a b) ^ t := ENNReal.rpow_le_rpow hmax ht
    _ = 2 ^ t * max a b ^ t := ENNReal.mul_rpow_of_nonneg _ _ ht
    _ ≤ 2 ^ t * (a ^ t + b ^ t) := by
        gcongr
        rcases le_total a b with hab | hab
        · rw [max_eq_right hab]
          exact le_add_left le_rfl
        · rw [max_eq_left hab]
          exact le_add_right le_rfl

/-- Positive moments of the Coulomb mass are bounded by explicit multiples of the moments of its
pieces. -/
theorem coulombMass_moment_le_pieces
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (z : Fin N → ℂ) (α : Fin N → ℝ) (αinf : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖) {Rr : ℝ} (hRr1 : 1 ≤ Rr)
    (hzRr : ∀ j, 2 * ‖z j‖ ≤ Rr) (t : ℝ) (ht : 0 < t) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t *
          ∑ k, ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^
            (∑ j, |γ * α j| + |γ * αinf|)) ^ t * weightedGmcBallMoment P M γ (α k) (z k) δ t +
        ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) ^ t *
          gmcMassMoment P M (Metric.closedBall 0 Rr) t) +
        ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) ^ t *
          weightedGmcBallMoment P M γ αinf 0 (1 / Rr) t) := by
  let _ : IsProbabilityMeasure P := hX.1
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
  have hcard : ((Finset.univ : Finset (Fin N)).card : ℝ≥0∞) = N := by
    rw [Finset.card_univ, Fintype.card_fin]
  -- the pointwise bound
  have hatoms : ∀ᵐ ω ∂P, ∀ k, M ω {z k} = 0 :=
    ae_all_iff.mpr fun k => gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (z k)
  have hpt : ∀ᵐ ω ∂P, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, cR ^ t * W k ω ^ t + cB ^ t * MB ω ^ t) +
        cE ^ t * V ω ^ t) := by
    filter_upwards [hatoms] with ω hω
    have hdec := coulombMass_le_pieces (M ω) γ α z αinf hδ hδ1 hsep hω hRr1 hzRr
    calc ENNReal.rpow (coulombMass γ (M ω) α z αinf) t
        ≤ ((∑ k, cR * W k ω + cB * MB ω) + cE * V ω) ^ t := ENNReal.rpow_le_rpow hdec ht.le
      _ ≤ 2 ^ t * ((∑ k, cR * W k ω + cB * MB ω) ^ t + (cE * V ω) ^ t) :=
          ennreal_add_rpow_le_two_rpow_mul _ _ ht.le
      _ ≤ 2 ^ t * (2 ^ t * ((∑ k, cR * W k ω) ^ t + (cB * MB ω) ^ t) + (cE * V ω) ^ t) := by
          gcongr
          exact ennreal_add_rpow_le_two_rpow_mul _ _ ht.le
      _ ≤ 2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, (cR * W k ω) ^ t + (cB * MB ω) ^ t) +
            (cE * V ω) ^ t) := by
          gcongr
          rw [← hcard]
          exact ennreal_finset_sum_rpow_le_card_rpow_sum_of_pos _ _ ht
      _ = _ := by
          simp only [ENNReal.mul_rpow_of_nonneg _ _ ht.le]
  -- integrate the bound
  have hS : AEMeasurable (fun ω => ∑ k, cR ^ t * W k ω ^ t) P :=
    Finset.aemeasurable_fun_sum _ fun k _ => aemeasurable_const.mul ((hWm k).pow_const t)
  have hA : AEMeasurable (fun ω => (N : ℝ≥0∞) ^ t * ∑ k, cR ^ t * W k ω ^ t) P :=
    aemeasurable_const.mul hS
  have hAB : AEMeasurable (fun ω => (N : ℝ≥0∞) ^ t * ∑ k, cR ^ t * W k ω ^ t +
      cB ^ t * MB ω ^ t) P := hA.add (aemeasurable_const.mul (hMBm.pow_const t))
  have hLAB : AEMeasurable (fun ω => 2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, cR ^ t * W k ω ^ t +
      cB ^ t * MB ω ^ t)) P := aemeasurable_const.mul hAB
  have hall : AEMeasurable (fun ω => 2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, cR ^ t * W k ω ^ t +
      cB ^ t * MB ω ^ t) + cE ^ t * V ω ^ t) P :=
    hLAB.add (aemeasurable_const.mul (hVm.pow_const t))
  have hWk : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      AEMeasurable (fun ω => cR ^ t * W k ω ^ t) P := fun k _ =>
    aemeasurable_const.mul ((hWm k).pow_const t)
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_const_mul'' _ hall, lintegral_add_left' hLAB, lintegral_const_mul'' _ hAB,
    lintegral_add_left' hA, lintegral_const_mul'' _ hS, lintegral_finsetSum' _ hWk,
    lintegral_const_mul'' _ (hMBm.pow_const t), lintegral_const_mul'' _ (hVm.pow_const t)]
  gcongr with k hk
  · rw [lintegral_const_mul'' _ ((hWm k).pow_const t)]
    rfl
  · rfl
  · exact gmc_exterior_moment_le_weighted P X hX γ hγ hγ2 M hM αinf hRr0 t ht.le

/-- Nonpositive moments of the Coulomb mass, uniformly over exterior radii, charges and orders in
compact ranges. -/
theorem coulombMass_moment_uniform_nonpos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : ℕ) (Rr : ℝ) (hRr1 : 1 ≤ Rr) (A tmin : ℝ) (htmin : tmin ≤ 0) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (z : Fin N → ℂ) (α : Fin N → ℝ) (αinf t : ℝ),
      (∀ j, 2 * ‖z j‖ ≤ Rr) → (∀ j, |α j| ≤ A) → |αinf| ≤ A → tmin ≤ t → t ≤ 0 →
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P ≤ K := by
  let _ : IsProbabilityMeasure P := hX.1
  set cmin : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-(N * (γ * A)))) *
    ENNReal.ofReal ((Rr + 2) ^ (-(γ * A))) with hcmin
  set B : Set ℂ := Metric.ball (((Rr + 1 : ℝ)) : ℂ) (1 / 8) with hB
  have hBm : AEMeasurable (fun ω => M ω B) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B Metric.isOpen_ball.measurableSet
  have hc0 : cmin ≠ 0 := mul_ne_zero
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hctop : cmin ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  refine ⟨cmin ^ tmin * (1 + gmcMassMoment P M B tmin),
    ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc0 hctop).lt_top
      (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
        gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM _ (1 / 8) (by norm_num) le_rfl
          tmin (lt_of_le_of_lt htmin (by positivity))⟩), ?_⟩
  intro z α αinf t hzRr hαA hαinfA htt ht0
  -- the uniform lower constant
  by_cases hNA : 0 ≤ A
  · have hsum : ∑ j, |γ * α j| ≤ N * (γ * A) := by
      calc ∑ j, |γ * α j| ≤ ∑ _j : Fin N, γ * A := Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_of_pos hγ]
            exact mul_le_mul_of_nonneg_left (hαA j) hγ.le
        _ = N * (γ * A) := by simp
    have hinf : |γ * αinf| ≤ γ * A := by
      rw [abs_mul, abs_of_pos hγ]
      exact mul_le_mul_of_nonneg_left hαinfA hγ.le
    have hcle : cmin ≤ ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((Rr + 2) ^ (-|γ * αinf|)) := by
      rw [hcmin]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
      · exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      · exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hc1 : cmin ≤ 1 := by
      rw [hcmin, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
      refine ENNReal.ofReal_le_one.mpr ?_
      have h1 : (2 : ℝ) ^ (-(N * (γ * A))) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
          (neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg N) (mul_nonneg hγ.le hNA)))
      have h2 : (Rr + 2) ^ (-(γ * A)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
          (neg_nonpos.mpr (mul_nonneg hγ.le hNA))
      calc (2 : ℝ) ^ (-(N * (γ * A))) * (Rr + 2) ^ (-(γ * A)) ≤ 1 * 1 :=
            mul_le_mul h1 h2 (Real.rpow_nonneg (by linarith) _) zero_le_one
        _ = 1 := one_mul 1
    have hlow : ∀ ω, cmin * M ω B ≤ coulombMass γ (M ω) α z αinf := fun ω =>
      (mul_le_mul' hcle le_rfl).trans (coulombMass_ge_exterior_ball (M ω) γ α z αinf hRr1 hzRr)
    calc ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P
        ≤ ∫⁻ ω, cmin ^ tmin * (1 + M ω B ^ tmin) ∂P := by
          apply lintegral_mono
          intro ω
          calc ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ≤ (cmin * M ω B) ^ t :=
                ennreal_rpow_antitone_of_nonpos (hlow ω) ht0
            _ = cmin ^ t * M ω B ^ t := ennreal_mul_rpow_of_ne_zero_ne_top _ _ hc0 hctop t
            _ ≤ cmin ^ tmin * (1 + M ω B ^ tmin) := by
                refine mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hc1 htt) ?_
                rcases le_total 1 (M ω B) with h1 | h1
                · exact ((ennreal_rpow_antitone_of_nonpos h1 ht0).trans_eq
                    (ENNReal.one_rpow t)).trans le_self_add
                · exact (ENNReal.rpow_le_rpow_of_exponent_ge h1 htt).trans le_add_self
      _ = cmin ^ tmin * (1 + gmcMassMoment P M B tmin) := by
          have h1m : AEMeasurable (fun ω => 1 + M ω B ^ tmin) P :=
            aemeasurable_const.add (hBm.pow_const tmin)
          have hone : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P := aemeasurable_const
          rw [lintegral_const_mul'' _ h1m, lintegral_add_left' hone, lintegral_const,
            measure_univ, mul_one]
          rfl
  · -- a negative charge bound admits no parameters
    exact absurd ((abs_nonneg _).trans hαinfA) hNA

end DOZZ.Proofs
