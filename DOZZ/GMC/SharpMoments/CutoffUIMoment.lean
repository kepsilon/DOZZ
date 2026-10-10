/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIBound
public import DOZZ.GMC.SharpMoments.InverseGamma

/-! # Uniform higher moments of regularized Coulomb masses

On a compact admissible set of couplings, roots and charges, a common exponent `(1 + η) s` keeps
part of the slack below every threshold. Positive orders are raised to an order bounded away from
zero and controlled by the uniform positive bound; nonpositive orders use one fixed exterior disk,
on which the regularized weight is bounded below, together with the γ-uniform inverse moments of
cutoff disk masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Nonpositive moments of regularized Coulomb masses, uniformly over couplings in a compact
subset of `(0, 2)`, bounded roots and charges, cutoffs, and orders in `[tmin, 0]`. -/
theorem regularizedCoulombMass_moment_uniform_nonpos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (partition : GMCChartPartition)
    (N : ℕ) (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2) {Zs E tmin : ℝ}
    (hZs : 0 ≤ Zs) (htmin : tmin ≤ 0) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ γ ∈ Γ, ∀ (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf t r : ℝ),
      ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E → tmin ≤ t → t ≤ 0 → 0 ≤ r →
      ∫⁻ ω, ENNReal.rpow (regularizedCoulombMass P Xc γ partition α z αinf r ω) t ∂P ≤ K := by
  let _ : IsProbabilityMeasure P := hX.1
  set R0 : ℝ := 2 * Zs + 2 with hR0
  obtain ⟨c, hc, hcb⟩ := coulombCutoffWeight_ge_ball partition N (E := E) hZs (le_refl R0)
  set B : Set ℂ := Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8) with hB
  set q : ℝ := -tmin + 1 with hq
  have hq0 : 0 < q := by linarith
  obtain ⟨Ci, hCi, hCib⟩ := equatorGFF_regularizedGMC_inverse_moment_uniform P X hX Xc hXc Γ hΓ
    hΓ2 B Metric.isOpen_ball ⟨_, Metric.mem_ball_self (by norm_num)⟩ q hq0
  set cm : ℝ≥0∞ := ENNReal.ofReal (min c 1) with hcm
  have hcm0 : cm ≠ 0 := (ENNReal.ofReal_pos.mpr (lt_min hc one_pos)).ne'
  have hcmt : cm ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcm1 : cm ≤ 1 := ENNReal.ofReal_le_one.mpr (min_le_right _ _)
  refine ⟨cm ^ (-q) * (1 + ENNReal.ofReal Ci), ENNReal.mul_lt_top
    (ENNReal.rpow_ne_top_of_ne_zero hcm0 hcmt).lt_top
    (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩), ?_⟩
  intro γ hγ α z αinf t r hZ hEα hEinf htt ht0 hr
  have hBm : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hlow : ∀ ω, cm * regularizedGMC P Xc γ r ω B ≤
      regularizedCoulombMass P Xc γ partition α z αinf r ω := by
    intro ω
    rw [regularizedCoulombMass_eq_lintegral P X hX Xc hXc]
    calc cm * regularizedGMC P Xc γ r ω B = ∫⁻ _x in B, cm ∂regularizedGMC P Xc γ r ω :=
          (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in B, coulombCutoffWeight partition γ α z αinf r x ∂regularizedGMC P Xc γ r ω := by
          refine setLIntegral_mono' hBm fun x hx => ?_
          exact (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans
            (hcb γ α z αinf r x hr hZ hEα hEinf hx)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hMm : AEMeasurable (fun ω => regularizedGMC P Xc γ r ω B ^ (-q)) P :=
    ((Measure.measurable_coe hBm).comp
      (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable.pow_const _
  calc ∫⁻ ω, ENNReal.rpow (regularizedCoulombMass P Xc γ partition α z αinf r ω) t ∂P
      ≤ ∫⁻ ω, cm ^ (-q) * (1 + regularizedGMC P Xc γ r ω B ^ (-q)) ∂P := by
        apply lintegral_mono
        intro ω
        calc ENNReal.rpow (regularizedCoulombMass P Xc γ partition α z αinf r ω) t
            ≤ (cm * regularizedGMC P Xc γ r ω B) ^ t :=
              ennreal_rpow_antitone_of_nonpos (hlow ω) ht0
          _ = cm ^ t * regularizedGMC P Xc γ r ω B ^ t :=
              ennreal_mul_rpow_of_ne_zero_ne_top _ _ hcm0 hcmt t
          _ ≤ cm ^ (-q) * (1 + regularizedGMC P Xc γ r ω B ^ (-q)) := by
              refine mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hcm1 (by linarith)) ?_
              rcases le_total 1 (regularizedGMC P Xc γ r ω B) with h1 | h1
              · exact ((ennreal_rpow_antitone_of_nonpos h1 ht0).trans_eq
                  (ENNReal.one_rpow t)).trans le_self_add
              · exact (ENNReal.rpow_le_rpow_of_exponent_ge h1 (by linarith)).trans le_add_self
    _ = cm ^ (-q) * (1 + ∫⁻ ω, regularizedGMC P Xc γ r ω B ^ (-q) ∂P) := by
        have h1m : AEMeasurable (fun ω => 1 + regularizedGMC P Xc γ r ω B ^ (-q)) P :=
          aemeasurable_const.add hMm
        have hone : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P := aemeasurable_const
        rw [lintegral_const_mul'' _ h1m, lintegral_add_left' hone, lintegral_const,
          measure_univ, mul_one]
    _ ≤ cm ^ (-q) * (1 + ENNReal.ofReal Ci) := by
        gcongr
        exact hCib γ hγ r hr

/-- Uniform higher moments of regularized Coulomb masses on compact admissible parameter sets: the
moment half of the extended-Seiberg cutoff uniform integrability. -/
theorem regularizedCoulombMass_higher_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (partition : GMCChartPartition)
    {N : ℕ} (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S)
    (hadm : ∀ c ∈ S,
      0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 < 4 / c.1 ^ 2 ∧
      (∀ k, (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 <
        2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 <
        2 / c.1 * (Q c.1 - c.2.2.2)) :
    ∃ η : ℝ, 0 < η ∧ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ S, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, ENNReal.rpow
        (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω)
        ((1 + η) * ((2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1)) ∂P ≤ B := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  set sf : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ := fun c =>
    (2 * Q c.1 - (∑ k, c.2.2.1 k + c.2.2.2)) / c.1 with hsf
  have hne : ∀ c ∈ S, c.1 ≠ 0 := fun c hc => (hadm c hc).1.ne'
  have hconton : ∀ f : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ,
      (∀ c ∈ S, ContinuousAt f c) → ContinuousOn f S := fun f hf c hc =>
    (hf c hc).continuousWithinAt
  have hsfc : ContinuousOn sf S := hconton _ fun c hc => by
    have h := hne c hc
    simp only [hsf, Q]
    fun_prop (disch := first | exact h | exact pow_ne_zero _ h)
  -- uniform sizes
  obtain ⟨σ0, hσ0⟩ := hS.exists_bound_of_continuousOn hsfc
  obtain ⟨Zs0, hZs0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E0, hE0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
      ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|) (by fun_prop)
  set σ : ℝ := max σ0 0 with hσdef
  set Zs : ℝ := max Zs0 0 with hZsdef
  set E : ℝ := max E0 0 with hEdef
  have hσ : 0 ≤ σ := le_max_right _ _
  have hZs : 0 ≤ Zs := le_max_right _ _
  have hE : 0 ≤ E := le_max_right _ _
  have hsσ : ∀ c ∈ S, |sf c| ≤ σ := fun c hc =>
    (by simpa [Real.norm_eq_abs] using hσ0 c hc : |sf c| ≤ σ0).trans (le_max_left _ _)
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
  -- uniform slack, threshold size and root separation
  have e1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 4 / c.1 ^ 2 - sf c :=
    eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [hsf, Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc => sub_pos.mpr (hadm c hc).2.2.2.2.2.1
  have e2 : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 2 / c.1 * (Q c.1 - c.2.2.1 k) - sf c :=
    fun k => eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [hsf, Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc => sub_pos.mpr ((hadm c hc).2.2.2.2.2.2.1 k)
  have e3 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 2 / c.1 * (Q c.1 - c.2.2.2) - sf c :=
    eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [hsf, Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc => sub_pos.mpr (hadm c hc).2.2.2.2.2.2.2
  have e4 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 4 / c.1 ^ 2 :=
    eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc => by
        have := (hadm c hc).1
        positivity
  have e5 : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 2 / c.1 * (Q c.1 - c.2.2.1 k) :=
    fun k => eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc =>
        mul_pos (div_pos two_pos (hadm c hc).1) (sub_pos.mpr ((hadm c hc).2.2.2.1 k))
  have e6 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 2 / c.1 * (Q c.1 - c.2.2.2) :=
    eventually_le_of_isCompact_of_pos hS (hconton _ fun c hc => by
      have h := hne c hc
      simp only [Q]
      fun_prop (disch := first | exact h | exact pow_ne_zero _ h)) fun c hc =>
        mul_pos (div_pos two_pos (hadm c hc).1) (sub_pos.mpr (hadm c hc).2.2.2.2.1)
  have e7 : ∀ j k : Fin N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
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
  obtain ⟨ε, h1, h2, h3, h4, h5, h6, h7, hε0, hε8⟩ := (e1.and ((eventually_all.mpr e2).and
    (e3.and (e4.and ((eventually_all.mpr e5).and (e6.and ((eventually_all.mpr fun j =>
      eventually_all.mpr (e7 j)).and (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by
        norm_num))))))))).exists
  -- the common exponent and the raised order
  set η : ℝ := min 1 (ε / (2 * (σ + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hε0 (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηg : η * σ ≤ ε / 2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (ε / (2 * (σ + 1))))
      (by positivity : (0 : ℝ) ≤ σ + 1)
    rw [← hη] at h
    have h' : ε / (2 * (σ + 1)) * (σ + 1) = ε / 2 := by field_simp
    linarith only [h, h', hη0]
  set tstar : ℝ := ε / 4 with htstar
  set τ : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ := fun c => max ((1 + η) * sf c) tstar
    with hτ
  have hτc : ContinuousOn τ S := ContinuousOn.sup (continuousOn_const.mul hsfc) continuousOn_const
  -- the raised order is admissible
  have hτth : ∀ c ∈ S, ∀ th : ℝ, ε ≤ th → ε ≤ th - sf c → τ c < th := by
    intro c hc th hth hths
    rcases le_total ((1 + η) * sf c) tstar with h | h
    · rw [hτ]
      simp only [max_eq_right h]
      linarith
    · rw [hτ]
      simp only [max_eq_left h]
      have hs0 : 0 < sf c := by
        by_contra hneg
        push Not at hneg
        have : (1 + η) * sf c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hneg
        linarith
      have hηs : η * sf c ≤ ε / 2 := le_trans (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hsσ c hc)) hη0.le) hηg
      linarith only [hths, hηs, hε0]
  have hτpos : ∀ c ∈ S, 0 < τ c := fun c hc =>
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hroot : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, c.2.2.1 k, τ c) := by
    intro c hc k
    obtain ⟨hγ0, hγ2, -, hαQ, -⟩ := hadm c hc
    exact (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, hαQ k, hτpos c hc,
      lt_min (hτth c hc _ (h4 c hc) (h1 c hc)) (hτth c hc _ (h5 k c hc) (h2 k c hc))⟩
  have hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, τ c) := by
    intro c hc
    obtain ⟨hγ0, hγ2, -, -, hαinfQ, -⟩ := hadm c hc
    have hQ0 : 0 < Q c.1 := by rw [Q]; positivity
    have hb := hτth c hc _ (h4 c hc) (h1 c hc)
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, max_lt hαinfQ hQ0, hτpos c hc,
      lt_min hb ?_⟩
    rcases le_total c.2.2.2 0 with h0 | h0
    · rw [max_eq_right h0, sub_zero]
      have : 4 / c.1 ^ 2 < 2 / c.1 * Q c.1 := by
        rw [Q]
        field_simp
        linarith only [sq_pos_of_pos hγ0]
      linarith
    · rw [max_eq_left h0]
      exact hτth c hc _ (h6 c hc) (h3 c hc)
  obtain ⟨Kp, hKp, hKpb⟩ := regularizedCoulombMass_moment_uniform_pos P X hX Xc hXc partition
    N S hS τ hτc hroot hinf hε0 (hε8.le.trans (by norm_num))
    (fun c hc j k hjk => h7 j k hjk c hc)
  have hΓ : IsCompact ((fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => c.1) '' S) :=
    hS.image continuous_fst
  have hΓ2 : (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => c.1) '' S ⊆ Set.Ioo 0 2 := by
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨(hadm c hc).1, (hadm c hc).2.1⟩
  obtain ⟨Kn, hKn, hKnb⟩ := regularizedCoulombMass_moment_uniform_nonpos P X hX Xc hXc partition
    N _ hΓ hΓ2 (E := E) hZs (by linarith : -2 * σ ≤ 0)
  refine ⟨η, hη0, 1 + Kp + Kn, ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr
    ⟨ENNReal.one_lt_top, hKp⟩, hKn⟩, fun c hc r hr => ?_⟩
  rcases le_or_gt (sf c) 0 with hs | hs
  · -- nonpositive Seiberg exponent
    have ht0 : (1 + η) * sf c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hs
    have htmin : -2 * σ ≤ (1 + η) * sf c := by
      have := (abs_le.mp (hsσ c hc)).1
      linarith only [this, mul_nonneg (sub_nonneg.2 hη1) (neg_nonneg.2 hs)]
    exact (hKnb c.1 ⟨c, hc, rfl⟩ c.2.2.1 c.2.1 c.2.2.2 _ r (hZc c hc) (hEα c hc) (hEinf c hc)
      htmin ht0 hr).trans le_add_self
  · -- positive Seiberg exponent: raise the order
    have ht : 0 < (1 + η) * sf c := mul_pos (by linarith) hs
    have hle : (1 + η) * sf c ≤ τ c := le_max_left _ _
    calc ∫⁻ ω, ENNReal.rpow (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω)
          ((1 + η) * sf c) ∂P
        ≤ ∫⁻ ω, (1 + ENNReal.rpow (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2
            r ω) (τ c)) ∂P :=
          lintegral_mono fun ω => weightedGrid_ennreal_rpow_le_one_add_rpow _ ht hle
      _ = 1 + ∫⁻ ω, ENNReal.rpow (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1
            c.2.2.2 r ω) (τ c) ∂P := by
          rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 1 + Kp := by gcongr; exact hKpb c hc r hr
      _ ≤ 1 + Kp + Kn := le_self_add

end DOZZ.Proofs
