/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitConvB

/-! # Limit of the far-region term of the cutoff Ward identity

The far-region test function `x ↦ ∫ (1 − ρ(y)) k₂(y) φ(x) k₁(x) T_n'(x − y)v dM(y)` only sees
pairs at distance at least `2δ`, where the truncated kernel is the limit kernel once the cutoff is
fine enough. It is therefore a random test function, equicontinuous with modulus proportional to the
far mass `∫ (1 − ρ) k₂ dM`, converging uniformly at the same scale; its integrals against the
cutoff chaos converge in probability. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

/-- A kernel weighted by a function vanishing near the singularity is Lipschitz-continuous in
the first variable, with constants depending on the separation. -/
theorem bpz_weighted_kern_sub_le {a : ℂ → ℝ} {Ba η : ℝ} (hη : 0 < η)
    (hBa : ∀ z, |a z| ≤ Ba) (v y : ℂ) (hsep : ∀ z, a z ≠ 0 → η ≤ ‖z - y‖) (x x' : ℂ) :
    |a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y)| ≤
      |a x - a x'| * (‖v‖ / η) + Ba * (3 * ‖v‖ * ‖x - x'‖ / η ^ 2) := by
  have hBa0 : 0 ≤ Ba := (abs_nonneg _).trans (hBa 0)
  have hK : ∀ z, η ≤ ‖z - y‖ → |bpzKern v (z - y)| ≤ ‖v‖ / η := fun z hz =>
    (abs_bpzKern_le v _).trans (div_le_div_of_nonneg_left (norm_nonneg v) hη hz)
  have hR0 : 0 ≤ |a x - a x'| * (‖v‖ / η) + Ba * (3 * ‖v‖ * ‖x - x'‖ / η ^ 2) := by positivity
  by_cases hx : a x = 0
  · by_cases hx' : a x' = 0
    · have h0 : a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y) = 0 := by
        rw [hx, hx']; ring
      rw [h0, abs_zero]; exact hR0
    · have hL : |a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y)| =
          |a x - a x'| * |bpzKern v (x' - y)| := by
        have e1 : a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y) =
            -(a x' * bpzKern v (x' - y)) := by rw [hx]; ring
        have e2 : a x - a x' = -a x' := by rw [hx]; ring
        rw [e1, e2, abs_neg, abs_neg, abs_mul]
      rw [hL]
      have := mul_le_mul_of_nonneg_left (hK x' (hsep x' hx')) (abs_nonneg (a x - a x'))
      have h2 : 0 ≤ Ba * (3 * ‖v‖ * ‖x - x'‖ / η ^ 2) := by positivity
      linarith
  · by_cases hx' : a x' = 0
    · have hL : |a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y)| =
          |a x - a x'| * |bpzKern v (x - y)| := by
        have e1 : a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y) =
            a x * bpzKern v (x - y) := by rw [hx']; ring
        have e2 : a x - a x' = a x := by rw [hx']; ring
        rw [e1, e2, abs_mul]
      rw [hL]
      have := mul_le_mul_of_nonneg_left (hK x (hsep x hx)) (abs_nonneg (a x - a x'))
      have h2 : 0 ≤ Ba * (3 * ‖v‖ * ‖x - x'‖ / η ^ 2) := by positivity
      linarith
    · have hxy := hsep x hx
      have hx'y := hsep x' hx'
      have hKd : |bpzKern v (x - y) - bpzKern v (x' - y)| ≤ 3 * ‖v‖ * ‖x - x'‖ / η ^ 2 := by
        have := abs_bpzKern_sub_le v hη hxy hx'y
        rwa [show x - y - (x' - y) = x - x' by ring] at this
      exact (bpz_abs_mul_sub_mul_le (hBa x') (hK x hxy)).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hKd hBa0))

namespace BPZLimitData

/-- The far-region integrand is dominated by the far weight. -/
theorem abs_mixIntegrand_le (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {B : ℝ}
    (hB : ∀ x, |φ x| ≤ B) {c : ℝ} (hc : 0 ≤ c) (v : ℂ) {k L : ℂ → ℝ}
    (hL : ∀ w, |L w| ≤ c * ‖v‖ / ‖w‖) {Kk : ℝ} (hk : ∀ x, ρ x * |k x| ≤ Kk) (x y : ℂ) :
    |(1 - ρ y) * k₂ y * (φ x * k x * L (x - y))| ≤
      c * ‖v‖ / (2 * δ) * B * Kk * ((1 - ρ y) * k₂ y) := by
  have hδ := hd.δ_pos
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
  have hKk : 0 ≤ Kk := (mul_nonneg (hd.ρ_nonneg x) (abs_nonneg _)).trans (hk x)
  have hR0 : 0 ≤ c * ‖v‖ / (2 * δ) * B * Kk * ((1 - ρ y) * k₂ y) := by positivity
  rw [abs_mul ((1 - ρ y) * k₂ y), abs_of_nonneg hw]
  by_cases hφx : φ x = 0
  · rw [hφx]; simpa using hR0
  by_cases hρy : ρ y = 1
  · rw [hρy]; simp
  have hxt := subset_tsupport φ hφx
  have hsep := hd.sep x hxt y (lt_of_le_of_ne (hd.ρ_le_one y) hρy)
  have hLb : |L (x - y)| ≤ c * ‖v‖ / (2 * δ) :=
    (hL (x - y)).trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hsep)
  have hρx := hd.rho_eq_one hxt
  have hkx : |k x| ≤ Kk := by have := hk x; rwa [hρx, one_mul] at this
  have hφb := hB x
  rw [abs_mul, abs_mul]
  calc (1 - ρ y) * k₂ y * (|φ x| * |k x| * |L (x - y)|)
      ≤ (1 - ρ y) * k₂ y * (B * Kk * (c * ‖v‖ / (2 * δ))) := by gcongr
    _ = c * ‖v‖ / (2 * δ) * B * Kk * ((1 - ρ y) * k₂ y) := by ring

theorem integrable_mixIntegrand (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {B : ℝ}
    (hB : ∀ x, |φ x| ≤ B) {c : ℝ} (hc : 0 ≤ c) (v : ℂ) {k L : ℂ → ℝ}
    (hLm : Measurable L) (hL : ∀ w, |L w| ≤ c * ‖v‖ / ‖w‖) {Kk : ℝ}
    (hk : ∀ x, ρ x * |k x| ≤ Kk) {m : Measure ℂ}
    (hint : Integrable (fun y => (1 - ρ y) * k₂ y) m) (x : ℂ) :
    Integrable (fun y => (1 - ρ y) * k₂ y * (φ x * k x * L (x - y))) m := by
  refine (hint.const_mul (c * ‖v‖ / (2 * δ) * B * Kk)).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · exact (((measurable_const.sub hd.ρ_meas).mul hd.k₂_meas).mul
      (measurable_const.mul (hLm.comp (measurable_const.sub measurable_id)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact hd.abs_mixIntegrand_le hB hc v hL hk x y

/-- The far-region test functions converge. -/
theorem conv_mix (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (hp : BPZWardProb P X γ M Xc ρ k₂ D)
    (v : ℂ) :
    TendstoInMeasure P
      (fun (n : ℕ) ω => ∫ x, bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂
        (fun w => bpzTruncLogDeriv n w v) (M ω) x ∂bpzCutChaos P Xc γ n ω) atTop
      (fun ω => ∫ x, bpzMixTest φ ρ k₂ k₂ (bpzKern v) (M ω) x ∂M ω) := by
  have : IsProbabilityMeasure P := hp.hX.1
  have hμ := bpzWeakConv_gmc P X hp.hX hd.γ_pos hp.γ2 M hp.hM hp.hMm Xc hp.hXc
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨R, hR0, hR⟩ := hd.rho_zero_of_norm
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  have hδ := hd.δ_pos
  set I₂ : Ω → ℝ := fun ω => ∫ y, (1 - ρ y) * k₂ y ∂M ω with hI₂
  have hI₂m : Measurable I₂ :=
    (measurable_integral_measure ((measurable_const.sub hd.ρ_meas).mul hd.k₂_meas)).comp hp.hMm
  have hI₂0 : ∀ ω, 0 ≤ I₂ ω := fun ω => integral_nonneg fun y =>
    mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
  set C₀ : ℝ := ‖v‖ / (2 * δ) * B * K + 1 with hC₀
  have hC₀1 : 1 ≤ C₀ := by
    have : 0 ≤ ‖v‖ / (2 * δ) * B * K := by positivity
    linarith
  set V : Ω → ℝ := fun ω => C₀ * I₂ ω with hV
  have hTn : ∀ (n : ℕ) w, |bpzTruncLogDeriv n w v| ≤ 1 * ‖v‖ / ‖w‖ := fun n w => by
    rw [one_mul]; exact abs_bpzTruncLogDeriv_apply_le n w v
  have hKv : ∀ w, |bpzKern v w| ≤ 1 * ‖v‖ / ‖w‖ := fun w => by
    rw [one_mul]; exact abs_bpzKern_le v w
  have hk₁ : ∀ (n : ℕ) x, ρ x * |bpzWardCutWeight γ q n kt x| ≤ K := fun n x =>
    (hd.rho_abs_cutWeight_le hK hK0 n x).1
  have hk₂ : ∀ x, ρ x * |k₂ x| ≤ K := fun x => (hd.rho_abs_cutWeight_le hK hK0 0 x).2
  have hTm : ∀ n : ℕ, Measurable fun w => bpzTruncLogDeriv n w v := fun n =>
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzTruncLogDeriv n)
  -- the joint measurability of the random test functions
  have hjoint : ∀ (k L : ℂ → ℝ), Measurable k → Measurable L →
      Measurable (fun p : Ω × ℂ => bpzMixTest φ ρ k k₂ L (M p.1) p.2) := by
    intro k L hk hL
    unfold bpzMixTest
    exact measurable_integral_finite_family M hp.hMm hp.hM.1
      (fun x y => (1 - ρ y) * k₂ y * (φ x * k x * L (x - y)))
      ((((measurable_const.sub (hd.ρ_meas.comp measurable_snd)).mul
        (hd.k₂_meas.comp measurable_snd)).mul
        (((hd.phi_cont.measurable.comp measurable_fst).mul (hk.comp measurable_fst)).mul
          (hL.comp (measurable_fst.sub measurable_snd)))))
  -- bounds by the far mass
  have hbound : ∀ (k L : ℂ → ℝ), (∀ w, |L w| ≤ 1 * ‖v‖ / ‖w‖) → (∀ x, ρ x * |k x| ≤ K) →
      ∀ᵐ ω ∂P, ∀ x, |bpzMixTest φ ρ k k₂ L (M ω) x| ≤ V ω := by
    intro k L hL hk
    filter_upwards [hp.k₂_int] with ω hω x
    refine (hd.abs_mixTest_le hB zero_le_one v hL hω x).trans ?_
    have h1 : 1 * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) ≤ C₀ := by
      calc 1 * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) ≤ 1 * ‖v‖ / (2 * δ) * B * K :=
            mul_le_mul_of_nonneg_left (hk x) (by positivity)
        _ ≤ C₀ := by rw [hC₀, one_mul]; linarith
    calc 1 * ‖v‖ / (2 * δ) * B * (ρ x * |k x|) * I₂ ω ≤ C₀ * I₂ ω :=
          mul_le_mul_of_nonneg_right h1 (hI₂0 ω)
      _ = V ω := rfl
  have hsupp : ∀ (k L : ℂ → ℝ) ω x, R < ‖x‖ → bpzMixTest φ ρ k k₂ L (M ω) x = 0 := by
    intro k L ω x hx
    unfold bpzMixTest
    rw [hd.phi_zero_of_rho_zero (hR x hx)]
    simp
  refine hμ.tendstoInMeasure_random_test
    (fun n ω x => bpzMixTest φ ρ (bpzWardCutWeight γ q n kt) k₂ (fun w => bpzTruncLogDeriv n w v)
      (M ω) x)
    (fun ω x => bpzMixTest φ ρ k₂ k₂ (bpzKern v) (M ω) x)
    (fun n => hjoint _ _ (hd.measurable_cutWeight n) (hTm n))
    (hjoint _ _ hd.k₂_meas (measurable_bpzKern v)) hR0 (V := V) (hI₂m.const_mul C₀)
    (fun ω => mul_nonneg (by linarith) (hI₂0 ω))
    (fun n => hbound _ _ (hTn n) (hk₁ n)) (hbound _ _ hKv hk₂)
    (fun n ω x hx => hsupp _ _ ω x hx) (fun ω x hx => hsupp _ _ ω x hx) ?_ ?_
  · -- equicontinuity
    intro ε hε
    set a : ℂ → ℝ := fun x => φ x * k₂ x with ha
    have hac : Continuous a := by
      have h : a = fun x => (φ x * kt x) * normPlus x ^ (4 + γ ^ 2 * q) := by
        funext x; simp only [ha]; rw [hd.k₂_eq]; ring
      rw [h]
      exact hd.f_C1.continuous.mul (bpz_continuous_normPlus.rpow_const fun x => Or.inl
        (bpz_normPlus_pos x).ne')
    have has : HasCompactSupport a := bpz_hasCompactSupport_of_ball (R := R) fun x hx => by
      simp only [ha]; rw [hd.phi_zero_of_rho_zero (hR x hx), zero_mul]
    obtain ⟨Ba, hBa⟩ := hac.bounded_above_of_compact_support has
    set Ba' : ℝ := max Ba 0
    have hBa' : ∀ z, |a z| ≤ Ba' := fun z => by
      rw [← Real.norm_eq_abs]; exact (hBa z).trans (le_max_left _ _)
    have hη : 0 < 2 * δ := by positivity
    set e : ℝ := ε / 2 * (2 * δ) / (‖v‖ + 1) with he
    have hep : 0 < e := by positivity
    obtain ⟨δa, hδa, hua⟩ := bpz_unifCont_of_compact hac has e hep
    set δk : ℝ := ε / 2 * (2 * δ) ^ 2 / (3 * (Ba' + 1) * (‖v‖ + 1)) with hδk
    have hδkp : 0 < δk := by positivity
    refine ⟨min δa δk, by positivity, ?_⟩
    filter_upwards [hp.k₂_int] with ω hω x x' hxx'
    have h1 : ‖x - x'‖ ≤ δa := hxx'.trans (min_le_left _ _)
    have h2 : ‖x - x'‖ ≤ δk := hxx'.trans (min_le_right _ _)
    have hpt : ∀ y, |(1 - ρ y) * k₂ y * (φ x * k₂ x * bpzKern v (x - y)) -
        (1 - ρ y) * k₂ y * (φ x' * k₂ x' * bpzKern v (x' - y))| ≤ ε * ((1 - ρ y) * k₂ y) := by
      intro y
      have hw : 0 ≤ (1 - ρ y) * k₂ y :=
        mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
      by_cases hρy : ρ y = 1
      · rw [hρy]; simp
      have hsep : ∀ z, a z ≠ 0 → 2 * δ ≤ ‖z - y‖ := fun z hz => by
        have hφz : φ z ≠ 0 := fun h => hz (by simp only [ha]; rw [h, zero_mul])
        exact hd.sep z (subset_tsupport φ hφz) y (lt_of_le_of_ne (hd.ρ_le_one y) hρy)
      have hk := bpz_weighted_kern_sub_le hη hBa' v y hsep x x'
      have heq : (1 - ρ y) * k₂ y * (φ x * k₂ x * bpzKern v (x - y)) -
          (1 - ρ y) * k₂ y * (φ x' * k₂ x' * bpzKern v (x' - y)) =
          (1 - ρ y) * k₂ y * (a x * bpzKern v (x - y) - a x' * bpzKern v (x' - y)) := by
        simp only [ha]; ring
      rw [heq, abs_mul, abs_of_nonneg hw, mul_comm ε]
      apply mul_le_mul_of_nonneg_left _ hw
      refine hk.trans ?_
      have hA : |a x - a x'| * (‖v‖ / (2 * δ)) ≤ ε / 2 := by
        calc |a x - a x'| * (‖v‖ / (2 * δ)) ≤ e * (‖v‖ / (2 * δ)) :=
              mul_le_mul_of_nonneg_right (hua x x' h1) (by positivity)
          _ = ε / 2 * (‖v‖ / (‖v‖ + 1)) := by rw [he]; field_simp
          _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left
              ((div_le_one (by positivity)).2 (by linarith)) (by positivity)
          _ = ε / 2 := mul_one _
      have hB : Ba' * (3 * ‖v‖ * ‖x - x'‖ / (2 * δ) ^ 2) ≤ ε / 2 := by
        have hfrac := bpz_frac_mul_le_one (le_max_right Ba 0) (norm_nonneg v)
        calc Ba' * (3 * ‖v‖ * ‖x - x'‖ / (2 * δ) ^ 2) ≤ Ba' * (3 * ‖v‖ * δk / (2 * δ) ^ 2) := by
              gcongr
          _ = ε / 2 * (Ba' * ‖v‖ / ((Ba' + 1) * (‖v‖ + 1))) := by rw [hδk]; field_simp
          _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
          _ = ε / 2 := mul_one _
      linarith
    have hI1 := hd.integrable_mixIntegrand hB zero_le_one v (measurable_bpzKern v)
      hKv hk₂ hω x
    have hI2 := hd.integrable_mixIntegrand hB zero_le_one v (measurable_bpzKern v)
      hKv hk₂ hω x'
    unfold bpzMixTest
    rw [← integral_sub hI1 hI2, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hω.const_mul ε) (Eventually.of_forall fun y => ?_)).trans
      ?_
    · rw [Real.norm_eq_abs]; exact hpt y
    · rw [integral_const_mul]
      calc ε * I₂ ω ≤ ε * (C₀ * I₂ ω) := mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (hI₂0 ω) hC₀1) hε.le
        _ = ε * V ω := rfl
  · -- uniform convergence
    intro ε hε
    set ε' : ℝ := ε * (2 * δ) / ((B + 1) * (‖v‖ + 1)) with hε'
    have hε'0 : 0 < ε' := by positivity
    have htail : ∀ᶠ n : ℕ in atTop, Real.exp (-(n : ℝ)) < 2 * δ :=
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).eventually
        (gt_mem_nhds (by positivity))
    filter_upwards [hd.cutWeight_tendsto ε' hε'0, htail] with n hn htn
    filter_upwards [hp.k₂_int] with ω hω x
    have hpt : ∀ y, |(1 - ρ y) * k₂ y * (φ x * bpzWardCutWeight γ q n kt x *
        bpzTruncLogDeriv n (x - y) v) - (1 - ρ y) * k₂ y * (φ x * k₂ x * bpzKern v (x - y))| ≤
        ε * ((1 - ρ y) * k₂ y) := by
      intro y
      have hw : 0 ≤ (1 - ρ y) * k₂ y :=
        mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)
      by_cases hφx : φ x = 0
      · rw [hφx]; simp only [zero_mul, mul_zero, sub_self, abs_zero]; positivity
      by_cases hρy : ρ y = 1
      · rw [hρy]; simp
      have hxt := subset_tsupport φ hφx
      have hsep := hd.sep x hxt y (lt_of_le_of_ne (hd.ρ_le_one y) hρy)
      have hT : bpzTruncLogDeriv n (x - y) v = bpzKern v (x - y) :=
        bpzTruncLogDeriv_apply_eq_kern n (lt_of_lt_of_le htn hsep) v
      have hρx : ρ x ≠ 0 := by rw [hd.rho_eq_one hxt]; exact one_ne_zero
      have hdk := hn x hρx
      rw [← hd.k₂_eq] at hdk
      have hKb : |bpzKern v (x - y)| ≤ ‖v‖ / (2 * δ) :=
        (abs_bpzKern_le v _).trans (div_le_div_of_nonneg_left (norm_nonneg v) (by positivity)
          hsep)
      rw [hT]
      have heq : (1 - ρ y) * k₂ y * (φ x * bpzWardCutWeight γ q n kt x * bpzKern v (x - y)) -
          (1 - ρ y) * k₂ y * (φ x * k₂ x * bpzKern v (x - y)) =
          (1 - ρ y) * k₂ y * (φ x * (bpzWardCutWeight γ q n kt x - k₂ x) * bpzKern v (x - y)) := by
        ring
      rw [heq, abs_mul, abs_of_nonneg hw, mul_comm ε]
      apply mul_le_mul_of_nonneg_left _ hw
      rw [abs_mul, abs_mul]
      have hφb := hB x
      calc |φ x| * |bpzWardCutWeight γ q n kt x - k₂ x| * |bpzKern v (x - y)|
          ≤ B * ε' * (‖v‖ / (2 * δ)) := by gcongr
        _ = ε * (B * ‖v‖ / ((B + 1) * (‖v‖ + 1))) := by rw [hε']; field_simp
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (bpz_frac_mul_le_one hB0 (norm_nonneg v)) hε.le
        _ = ε := mul_one _
    have hI1 := hd.integrable_mixIntegrand hB zero_le_one v (hTm n)
      (hTn n) (hk₁ n) hω x
    have hI2 := hd.integrable_mixIntegrand hB zero_le_one v (measurable_bpzKern v)
      hKv hk₂ hω x
    unfold bpzMixTest
    rw [← integral_sub hI1 hI2, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hω.const_mul ε) (Eventually.of_forall fun y => ?_)).trans
      ?_
    · rw [Real.norm_eq_abs]; exact hpt y
    · rw [integral_const_mul]
      calc ε * I₂ ω ≤ ε * (C₀ * I₂ ω) := mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (hI₂0 ω) hC₀1) hε.le
        _ = ε * V ω := rfl

end BPZLimitData

end DOZZ.Proofs
