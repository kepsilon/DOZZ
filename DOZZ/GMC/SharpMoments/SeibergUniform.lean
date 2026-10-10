/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMomentBound
public import DOZZ.GMC.SharpMoments.WeightedTwoCenter
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! # Uniform higher moments of the Coulomb mass on compact parameter sets

On a compact admissible set of roots and charges, the root separation, the root sizes, the charges
and the slack below every threshold are uniformly controlled. A common exponent `(1 + η) s` keeps
half of the slack, and the explicit piece bounds, the location transfer of weighted moments to the
chart center and the finite charge grid give one bound for all parameters; nonpositive orders use
one fixed exterior disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A continuous function positive on a compact set dominates every small positive constant
there. -/
theorem eventually_le_of_isCompact_of_pos {X : Type*} [TopologicalSpace X] {S : Set X}
    (hS : IsCompact S) {f : X → ℝ} (hf : ContinuousOn f S) (hpos : ∀ x ∈ S, 0 < f x) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x ∈ S, ε ≤ f x := by
  rcases S.eq_empty_or_nonempty with hS0 | hSne
  · exact Eventually.of_forall fun ε x hx => by simp [hS0] at hx
  · obtain ⟨x0, hx0, hmin⟩ := hS.exists_isMinOn hSne hf
    filter_upwards [Ioo_mem_nhdsGT (hpos x0 hx0)] with ε hε x hx
    exact hε.2.le.trans (isMinOn_iff.mp hmin x hx)

/-- The transfer constant is monotone in the order on a bounded range of positive orders. -/
theorem transferConstant_le {γ R t tm : ℝ} (hR : 0 ≤ R) (ht : 0 < t) (htm : t ≤ tm) :
    ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
        |t ^ 2 - t|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |t| ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
        (tm ^ 2 + tm))) * ENNReal.ofReal ((1 + R) ^ 4) ^ tm := by
  have hc : 0 ≤ γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 := by
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h1 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
    positivity
  have habs : |t ^ 2 - t| ≤ tm ^ 2 + tm := by
    calc |t ^ 2 - t| ≤ |t ^ 2| + |t| := abs_sub _ _
      _ = t ^ 2 + t := by rw [abs_of_nonneg (sq_nonneg t), abs_of_pos ht]
      _ ≤ tm ^ 2 + tm := by linarith only [pow_le_pow_left₀ ht.le htm 2, htm]
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left habs hc))) ?_
  rw [abs_of_pos ht]
  refine ENNReal.rpow_le_rpow_of_exponent_le ?_ htm
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith))

/-- A real power with base at least one is monotone in both the base and the exponent. -/
theorem real_rpow_le_rpow_of_le_of_le {a b e f : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (he : 0 ≤ e)
    (hef : e ≤ f) : a ^ e ≤ b ^ f :=
  (Real.rpow_le_rpow (by linarith) hab he).trans
    (Real.rpow_le_rpow_of_exponent_le (ha.trans hab) hef)

/-- Positive moments of the Coulomb mass, uniformly over separated roots of bounded size, bounded
charges and orders with a fixed slack below every threshold. -/
theorem coulombMass_moment_uniform_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) {Rr : ℝ} (hRr1 : 1 ≤ Rr) {Zs A g : ℝ}
    (hZs : 0 ≤ Zs) (hg : 0 < g) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (z : Fin N → ℂ) (α : Fin N → ℝ) (αinf t : ℝ),
      (∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖) → ∑ j, ‖z j‖ ≤ Zs → (∀ j, 2 * ‖z j‖ ≤ Rr) →
      (∀ j, |α j| ≤ A) → |αinf| ≤ A → 0 < t → t + g ≤ 4 / γ ^ 2 →
      (∀ k, t + g ≤ 2 / γ * (Q γ - α k)) → t + g ≤ 2 / γ * (Q γ - αinf) →
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z αinf) t ∂P ≤ K := by
  let _ : IsProbabilityMeasure P := hX.1
  have hδ1 : δ ≤ 1 := hδ8.trans (by norm_num)
  have hRr0 : 0 < Rr := by linarith
  have h4 : 0 < 4 / γ ^ 2 := by positivity
  set tm : ℝ := max (4 / γ ^ 2 - g) 0 with htm
  have htm0 : 0 ≤ tm := le_max_right _ _
  have htm4 : tm < 4 / γ ^ 2 := max_lt (by linarith) h4
  obtain ⟨K1, hK1, hK1b⟩ := weightedGmcBallMoment_uniform_center P X hX γ hγ hγ2 M hM δ hδ hδ1 A
    g hg
  obtain ⟨K2, hK2, hK2b⟩ := weightedGmcBallMoment_uniform_center P X hX γ hγ hγ2 M hM (1 / Rr)
    (by positivity) ((div_le_one hRr0).mpr hRr1) A g hg
  set R : ℝ := Zs + 1 with hR
  set Tm : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) /
      2 * (tm ^ 2 + tm))) * ENNReal.ofReal ((1 + R) ^ 4) ^ tm with hTm
  set E : ℝ := (N + 1) * (γ * A) with hE
  set cRm : ℝ≥0∞ := ENNReal.ofReal (((2 + 2 * Zs) / δ) ^ E) with hcRm
  set cBm : ℝ≥0∞ := ENNReal.ofReal (((1 + Rr + Zs) / δ) ^ E) with hcBm
  set cEm : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (N * (γ * A))) with hcEm
  set MBm : ℝ≥0∞ := 1 + gmcMassMoment P M (Metric.closedBall 0 Rr) tm with hMBm
  have hMBmtop : MBm < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
    gmc_bounded_moment_lt_top P X hX γ hγ hγ2 M hM _ Metric.isBounded_closedBall tm htm0 htm4⟩
  have hfin : ∀ x : ℝ≥0∞, x ≠ ⊤ → x ^ tm < ⊤ := fun x hx =>
    ENNReal.rpow_lt_top_of_nonneg htm0 hx
  refine ⟨2 ^ tm * (2 ^ tm * (((N : ℝ≥0∞) + 1) ^ tm * (N * (cRm ^ tm * (Tm * K1))) +
      cBm ^ tm * MBm) + cEm ^ tm * K2), ?_, ?_⟩
  · have hTmtop : Tm < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (hfin _ ENNReal.ofReal_ne_top)
    refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
      · refine ENNReal.mul_lt_top (hfin _ (by simp)) (ENNReal.mul_lt_top (by simp) ?_)
        exact ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) (ENNReal.mul_lt_top hTmtop hK1)
      · exact ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) hMBmtop
    · exact ENNReal.mul_lt_top (hfin _ ENNReal.ofReal_ne_top) hK2
  intro z α αinf t hsep hZsum hzRr hαA hαinfA ht htb hti htinf
  have htle : t ≤ tm := (by linarith : t ≤ 4 / γ ^ 2 - g).trans (le_max_left _ _)
  have htlt4 : t < 4 / γ ^ 2 := by linarith
  -- size of the charges
  have hsumα : ∑ j, |γ * α j| ≤ N * (γ * A) := by
    calc ∑ j, |γ * α j| ≤ ∑ _j : Fin N, γ * A := Finset.sum_le_sum fun j _ => by
          rw [abs_mul, abs_of_pos hγ]
          exact mul_le_mul_of_nonneg_left (hαA j) hγ.le
      _ = N * (γ * A) := by simp
  have hinf : |γ * αinf| ≤ γ * A := by
    rw [abs_mul, abs_of_pos hγ]
    exact mul_le_mul_of_nonneg_left hαinfA hγ.le
  have hS : ∑ j, |γ * α j| + |γ * αinf| ≤ E := by
    rw [hE]
    linarith only [hsumα, hinf]
  have hS0 : 0 ≤ ∑ j, |γ * α j| + |γ * αinf| :=
    add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _)
  have hzsum0 : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have hδinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  -- the constants
  have hpow_le : ∀ {x y : ℝ≥0∞}, x ≤ y → 1 ≤ y → x ^ t ≤ y ^ tm := fun hxy hy =>
    (ENNReal.rpow_le_rpow hxy ht.le).trans (ENNReal.rpow_le_rpow_of_exponent_le hy htle)
  have hone_le : ∀ {r : ℝ}, 1 ≤ r → (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := fun hr => by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hr
  have hcR : ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) ^ t ≤
      cRm ^ tm := by
    refine hpow_le (ENNReal.ofReal_le_ofReal (real_rpow_le_rpow_of_le_of_le ?_ ?_ hS0 hS))
      (hone_le (Real.one_le_rpow ?_ (hS0.trans hS)))
    · rw [le_div_iff₀ hδ]
      linarith
    · exact div_le_div_of_nonneg_right (by linarith) hδ.le
    · rw [le_div_iff₀ hδ]
      linarith
  have hcB : ENNReal.ofReal (((1 + Rr + ∑ j, ‖z j‖) / δ) ^ (∑ j, |γ * α j| + |γ * αinf|)) ^ t ≤
      cBm ^ tm := by
    refine hpow_le (ENNReal.ofReal_le_ofReal (real_rpow_le_rpow_of_le_of_le ?_ ?_ hS0 hS))
      (hone_le (Real.one_le_rpow ?_ (hS0.trans hS)))
    · rw [le_div_iff₀ hδ]
      linarith
    · exact div_le_div_of_nonneg_right (by linarith) hδ.le
    · rw [le_div_iff₀ hδ]
      linarith
  have hcE : ENNReal.ofReal ((2 : ℝ) ^ (∑ j, |γ * α j|)) ^ t ≤ cEm ^ tm :=
    hpow_le (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (by norm_num) hsumα))
      (hone_le (Real.one_le_rpow (by norm_num) (hsumα.trans' (Finset.sum_nonneg fun j _ =>
        abs_nonneg _))))
  -- the root moments
  have hW : ∀ k, weightedGmcBallMoment P M γ (α k) (z k) δ t ≤ Tm * K1 := by
    intro k
    have hzk : ‖z k‖ ≤ Zs := (Finset.single_le_sum (f := fun j => ‖z j‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ k)).trans hZsum
    refine (weightedGmcBallMoment_le_transfer P X hX γ hγ hγ2 M hM (α k) (z k) 0 δ R hδ hδ8
      (by linarith) (by linarith) (by rw [norm_zero, zero_add]; linarith) t ht htlt4).trans ?_
    exact mul_le_mul' (transferConstant_le (by linarith) ht htle)
      (hK1b (α k) t (hαA k) ht htb (hti k))
  -- the bulk moment
  have hMB : gmcMassMoment P M (Metric.closedBall 0 Rr) t ≤ MBm := by
    have hm : AEMeasurable (fun ω => M ω (Metric.closedBall 0 Rr) ^ tm) P :=
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
        Metric.isClosed_closedBall.measurableSet).pow_const tm
    calc gmcMassMoment P M (Metric.closedBall 0 Rr) t
        ≤ ∫⁻ ω, (1 + M ω (Metric.closedBall 0 Rr) ^ tm) ∂P :=
          lintegral_mono fun ω => weightedGrid_ennreal_rpow_le_one_add_rpow _ ht htle
      _ = MBm := by
          rw [lintegral_add_left' aemeasurable_const, lintegral_const, measure_univ, mul_one]
          rfl
  -- assemble
  refine (coulombMass_moment_le_pieces P X hX γ hγ hγ2 M hM z α αinf hδ hδ1 hsep hRr1 hzRr t
    ht).trans ?_
  have h2 : (2 : ℝ≥0∞) ^ t ≤ 2 ^ tm := ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) htle
  have hN : (N : ℝ≥0∞) ^ t ≤ ((N : ℝ≥0∞) + 1) ^ tm :=
    hpow_le le_self_add le_add_self
  have hsumW : ∑ k, ENNReal.ofReal (((2 + 2 * ∑ j, ‖z j‖) / δ) ^
      (∑ j, |γ * α j| + |γ * αinf|)) ^ t * weightedGmcBallMoment P M γ (α k) (z k) δ t ≤
        N * (cRm ^ tm * (Tm * K1)) := by
    calc _ ≤ ∑ _k : Fin N, cRm ^ tm * (Tm * K1) :=
          Finset.sum_le_sum fun k _ => mul_le_mul' hcR (hW k)
      _ = N * (cRm ^ tm * (Tm * K1)) := by simp
  exact mul_le_mul' h2 (add_le_add (mul_le_mul' h2 (add_le_add (mul_le_mul' hN hsumW)
    (mul_le_mul' hcB hMB))) (mul_le_mul' hcE (hK2b αinf t hαinfA ht htb htinf)))

/-- Uniform higher moments on compact admissible `U_N` parameter sets. -/
theorem equatorGFF_extendedSeiberg_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {N : ℕ}
    (S : Set ((Fin N → ℂ) × (Fin N → ℝ) × ℝ)) (hS : IsCompact S)
    (hadm : ∀ c ∈ S,
      Function.Injective c.1 ∧ (∀ k, c.2.1 k < Q γ) ∧ c.2.2 < Q γ ∧
      (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ < 4 / γ ^ 2 ∧
      (∀ k, (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ <
        2 / γ * (Q γ - c.2.1 k)) ∧
      (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ < 2 / γ * (Q γ - c.2.2)) :
    ∃ η : ℝ, 0 < η ∧ ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ c ∈ S,
      ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) c.2.1 c.1 c.2.2)
        ((1 + η) * ((2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ)) ∂P ≤ B := by
  set sf : (Fin N → ℂ) × (Fin N → ℝ) × ℝ → ℝ := fun c =>
    (2 * Q γ - (∑ k, c.2.1 k + c.2.2)) / γ with hsf
  -- uniform sizes
  obtain ⟨σ, hσ⟩ := hS.exists_bound_of_continuousOn (f := sf) (by fun_prop)
  obtain ⟨Zs, hZs⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : (Fin N → ℂ) × (Fin N → ℝ) × ℝ => ∑ j, ‖c.1 j‖) (by fun_prop)
  obtain ⟨A, hA⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : (Fin N → ℂ) × (Fin N → ℝ) × ℝ => ∑ j, |c.2.1 j| + |c.2.2|) (by fun_prop)
  set σ' : ℝ := max σ 0 with hσ'
  set Zs' : ℝ := max Zs 0 with hZs'
  set A' : ℝ := max A 0 with hA'
  -- uniform slack and separation
  have e_bulk : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 4 / γ ^ 2 - sf c :=
    eventually_le_of_isCompact_of_pos hS (by fun_prop) fun c hc =>
      sub_pos.mpr (hadm c hc).2.2.2.1
  have e_ins : ∀ k, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 2 / γ * (Q γ - c.2.1 k) - sf c :=
    fun k => eventually_le_of_isCompact_of_pos hS (by fun_prop) fun c hc =>
      sub_pos.mpr ((hadm c hc).2.2.2.2.1 k)
  have e_inf : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ c ∈ S, ε ≤ 2 / γ * (Q γ - c.2.2) - sf c :=
    eventually_le_of_isCompact_of_pos hS (by fun_prop) fun c hc =>
      sub_pos.mpr (hadm c hc).2.2.2.2.2
  have e_sep : ∀ j k : Fin N, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      j ≠ k → ∀ c ∈ S, 2 * ε ≤ ‖c.1 j - c.1 k‖ := by
    intro j k
    by_cases hjk : j = k
    · exact Eventually.of_forall fun _ h => absurd hjk h
    · filter_upwards [eventually_le_of_isCompact_of_pos hS
        (f := fun c : (Fin N → ℂ) × (Fin N → ℝ) × ℝ => ‖c.1 j - c.1 k‖ / 2) (by fun_prop)
        fun c hc => half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ((hadm c hc).1.ne hjk)))]
        with ε hε _ c hc
      linarith [hε c hc]
  have e_all := e_bulk.and ((eventually_all.mpr e_ins).and (e_inf.and
    ((eventually_all.mpr fun j => eventually_all.mpr (e_sep j)).and
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 8 by norm_num)))))
  obtain ⟨g, hgb, hgi, hginf, hgsep, hg0, hg8⟩ := e_all.exists
  -- the common exponent
  have hσ0 : 0 ≤ σ' := le_max_right _ _
  set η : ℝ := min 1 (g / (2 * (σ' + 1))) with hη
  have hη0 : 0 < η := lt_min one_pos (div_pos hg0 (by positivity))
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηg : η * (σ' + 1) ≤ g / 2 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right 1 (g / (2 * (σ' + 1))))
      (by positivity : (0 : ℝ) ≤ σ' + 1)
    rw [← hη] at h
    calc η * (σ' + 1) ≤ g / (2 * (σ' + 1)) * (σ' + 1) := h
      _ = g / 2 := by field_simp
  set Rr : ℝ := 1 + 2 * Zs' with hRr
  have hRr1 : 1 ≤ Rr := by
    have : 0 ≤ Zs' := le_max_right _ _
    linarith
  obtain ⟨Kp, hKp, hKpb⟩ := coulombMass_moment_uniform_pos P X hX γ hγ hγ2 M hM N hg0 hg8.le
    hRr1 (le_max_right Zs 0) (half_pos hg0)
  obtain ⟨Kn, hKn, hKnb⟩ := coulombMass_moment_uniform_nonpos P X hX γ hγ hγ2 M hM N Rr hRr1 A'
    (-2 * σ') (by linarith)
  refine ⟨η, hη0, Kp + Kn, ENNReal.add_lt_top.mpr ⟨hKp, hKn⟩, fun c hc => ?_⟩
  -- parameters of `c`
  have hZc : ∑ j, ‖c.1 j‖ ≤ Zs' := by
    have h := hZs c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  have hzR : ∀ j, 2 * ‖c.1 j‖ ≤ Rr := fun j => by
    have := (Finset.single_le_sum (f := fun j => ‖c.1 j‖) (fun j _ => norm_nonneg _)
      (Finset.mem_univ j)).trans hZc
    linarith
  have hAc : ∑ j, |c.2.1 j| + |c.2.2| ≤ A' := by
    have h := hA c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (Finset.sum_nonneg fun j _ =>
      abs_nonneg _) (abs_nonneg _))] at h
    exact h.trans (le_max_left _ _)
  have hαA : ∀ j, |c.2.1 j| ≤ A' := fun j => by
    have := Finset.single_le_sum (f := fun j => |c.2.1 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith [abs_nonneg c.2.2]
  have hαinfA : |c.2.2| ≤ A' := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (c.2.1 j))
    linarith
  have hsσ : |sf c| ≤ σ' := (by simpa [Real.norm_eq_abs] using hσ c hc : |sf c| ≤ σ).trans
    (le_max_left _ _)
  have hsσ' := abs_le.mp hsσ
  rcases le_or_gt (sf c) 0 with hs | hs
  · -- nonpositive Seiberg exponent
    have ht0 : (1 + η) * sf c ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hs
    have htmin : -2 * σ' ≤ (1 + η) * sf c := by
      linarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hη1) hs, hsσ'.1]
    exact (hKnb c.1 c.2.1 c.2.2 _ hzR hαA hαinfA htmin ht0).trans le_add_self
  · -- positive Seiberg exponent
    have ht : 0 < (1 + η) * sf c := mul_pos (by linarith) hs
    have hηs : η * sf c ≤ g / 2 := by
      linarith only [mul_le_mul_of_nonneg_left hsσ'.2 hη0.le, hηg, hη0]
    have hsep : ∀ j k, j ≠ k → 2 * g ≤ ‖c.1 j - c.1 k‖ := fun j k hjk => hgsep j k hjk c hc
    refine (hKpb c.1 c.2.1 c.2.2 _ hsep hZc hzR hαA hαinfA ht ?_ ?_ ?_).trans le_self_add
    · have := hgb c hc
      linarith
    · intro k
      have := hgi k c hc
      linarith
    · have := hginf c hc
      linarith

end DOZZ.Proofs
