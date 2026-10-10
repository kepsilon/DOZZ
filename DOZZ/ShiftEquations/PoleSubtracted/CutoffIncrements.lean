/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.CutoffMoments

/-!
# Exponential decay of the cutoff increments

After the tilt, the successive differences of the cutoff family are controlled by
`E[(T_{a,n+1} - T_{a,n})(T_{a,n+1}^{-a/γ} + T_{a,n}^{-a/γ})]` ([KRV, (estF)]). The annular increment
is at most `e^{γ a⁺ (n+1)} M(B(0, e^{-n}))`. For `a ≤ 0` the powers are at most `1 + Z_ℂ(0)^{c₁}`
and Hölder with `r₁ < 4/γ²` uses the window room; for `a > 0` they are at most `1 + R₁^{-a₂/γ}` and
Hölder with `r₂` close to `1` beats `e^{γ a₂ n}` because `γ a₂ < 1`. Both give `O(e^{-κ n})`
uniformly on a compact range `a ∈ [a₁, a₂]`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The `r`-th moment exponent of a small ball, divided by `r`. -/
theorem ballExponent_div {γ r : ℝ} (hr : r ≠ 0) :
    (γ * Q γ * r - γ ^ 2 * r ^ 2 / 2) / r = γ * Q γ - γ ^ 2 * r / 2 := by
  field_simp

theorem gamma_mul_Q {γ : ℝ} (hγ : 0 < γ) : γ * Q γ = 2 + γ ^ 2 / 2 := by
  rw [Q]
  field_simp

/-- Two exponential decays combine into one. -/
theorem ofReal_add_exp_le {C₁ C₂ κ₁ κ₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (n : ℕ) :
    ENNReal.ofReal (C₁ * Real.exp (-κ₁ * n)) + ENNReal.ofReal (C₂ * Real.exp (-κ₂ * n)) ≤
      ENNReal.ofReal ((C₁ + C₂) * Real.exp (-min κ₁ κ₂ * n)) := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : Real.exp (-κ₁ * n) ≤ Real.exp (-min κ₁ κ₂ * n) :=
    Real.exp_le_exp.2 (by linarith only [mul_le_mul_of_nonneg_right (min_le_left κ₁ κ₂) hn])
  have h2 : Real.exp (-κ₂ * n) ≤ Real.exp (-min κ₁ κ₂ * n) :=
    Real.exp_le_exp.2 (by linarith only [mul_le_mul_of_nonneg_right (min_le_right κ₁ κ₂) hn])
  linarith only [mul_le_mul_of_nonneg_left h1 hC₁, mul_le_mul_of_nonneg_left h2 hC₂]

/-- **Pointwise control of the increment** on a charge range `[a₁, a₂]`. -/
theorem cutoffIncrement_le {γ η a a₁ a₂ : ℝ} (hγ : 0 < γ) (hη : 0 ≤ η) (hηγ : η ≤ 2 / γ)
    (ha : a ∈ Icc a₁ a₂) (n : ℕ) (μ : Measure ℂ) :
    (cutoffTiltedMass γ η a (n + 1) μ - cutoffTiltedMass γ η a n μ) *
        (cutoffTiltedMass γ η a (n + 1) μ ^ (-a / γ) + cutoffTiltedMass γ η a n μ ^ (-a / γ)) ≤
      2 * (μ (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
          (1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ ^ max (-a₁ / γ) 0)) +
        2 * ENNReal.ofReal (Real.exp (γ * max a₂ 0 * (n + 1))) *
          (μ (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
            (1 + poleLocalMass γ (2 / γ + η) (2 / γ - η) μ ^ (-(max a₂ 0 / γ)))) := by
  set T' := cutoffTiltedMass γ η a (n + 1) μ
  set T := cutoffTiltedMass γ η a n μ
  set T0 := poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) μ
  set L := poleLocalMass γ (2 / γ + η) (2 / γ - η) μ
  set B := μ (Metric.ball 0 (Real.exp (-(n : ℝ))))
  have hann : T' - T ≤ ENNReal.ofReal (Real.exp (γ * max a 0 * (n + 1))) * B := by
    rw [tsub_le_iff_left]
    calc T' = T + ∫⁻ x in cutoffRegion (n + 1) \ cutoffRegion n,
          zeroTilt γ a x * poleWeight γ η x ∂μ := cutoffTiltedMass_succ γ η a n μ
      _ ≤ T + ENNReal.ofReal (Real.exp (γ * max a 0 * (n + 1))) * B :=
          add_le_add le_rfl (annulusMass_le a hγ hη hηγ n μ)
  rcases le_or_gt a 0 with ha0 | ha0
  · have hs0 : 0 ≤ -a / γ := div_nonneg (by linarith) hγ.le
    have hsc : -a / γ ≤ max (-a₁ / γ) 0 :=
      le_max_of_le_left (div_le_div_of_nonneg_right (by linarith [ha.1]) hγ.le)
    have hT'0 : T' ^ (-a / γ) ≤ 1 + T0 ^ max (-a₁ / γ) 0 :=
      (ENNReal.rpow_le_rpow (cutoffTiltedMass_le_totalMass_zero hγ ha0 (n + 1) μ) hs0).trans
        (ennrpow_le_one_add_rpow hs0 hsc)
    have hT0 : T ^ (-a / γ) ≤ 1 + T0 ^ max (-a₁ / γ) 0 :=
      (ENNReal.rpow_le_rpow (cutoffTiltedMass_le_totalMass_zero hγ ha0 n μ) hs0).trans
        (ennrpow_le_one_add_rpow hs0 hsc)
    have hann' : T' - T ≤ B := by
      have := hann
      rwa [max_eq_right ha0, mul_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one,
        one_mul] at this
    calc (T' - T) * (T' ^ (-a / γ) + T ^ (-a / γ))
        ≤ B * ((1 + T0 ^ max (-a₁ / γ) 0) + (1 + T0 ^ max (-a₁ / γ) 0)) :=
          mul_le_mul' hann' (add_le_add hT'0 hT0)
      _ = 2 * (B * (1 + T0 ^ max (-a₁ / γ) 0)) := by
          rw [← two_mul]
          ring
      _ ≤ _ := le_self_add
  · have hs0 : -a / γ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hγ.le
    have hsc : -(max a₂ 0 / γ) ≤ -a / γ := by
      rw [neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right (le_max_of_le_left ha.2) hγ.le
    have hLT' : L ≤ T' := localMass_le_cutoffTiltedMass γ η a (n + 1) μ
    have hLT : L ≤ T := localMass_le_cutoffTiltedMass γ η a n μ
    have hT'0 : T' ^ (-a / γ) ≤ 1 + L ^ (-(max a₂ 0 / γ)) :=
      (ennrpow_le_of_le_of_nonpos hLT' hs0).trans (ennrpow_le_one_add_rpow_neg hs0 hsc)
    have hT0 : T ^ (-a / γ) ≤ 1 + L ^ (-(max a₂ 0 / γ)) :=
      (ennrpow_le_of_le_of_nonpos hLT hs0).trans (ennrpow_le_one_add_rpow_neg hs0 hsc)
    have hexp : ENNReal.ofReal (Real.exp (γ * max a 0 * (n + 1))) ≤
        ENNReal.ofReal (Real.exp (γ * max a₂ 0 * (n + 1))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have : max a 0 ≤ max a₂ 0 := max_le_max ha.2 le_rfl
      have hn : (0 : ℝ) ≤ n + 1 := by positivity
      have := mul_le_mul_of_nonneg_left this hγ.le
      exact mul_le_mul_of_nonneg_right this hn
    calc (T' - T) * (T' ^ (-a / γ) + T ^ (-a / γ))
        ≤ (ENNReal.ofReal (Real.exp (γ * max a₂ 0 * (n + 1))) * B) *
            ((1 + L ^ (-(max a₂ 0 / γ))) + (1 + L ^ (-(max a₂ 0 / γ)))) :=
          mul_le_mul' (hann.trans (mul_le_mul_left hexp _)) (add_le_add hT'0 hT0)
      _ = 2 * ENNReal.ofReal (Real.exp (γ * max a₂ 0 * (n + 1))) *
            (B * (1 + L ^ (-(max a₂ 0 / γ)))) := by
          rw [← two_mul]
          ring
      _ ≤ _ := le_add_self

/-- A finite conjugate moment of `1 + Y^c`. -/
theorem lintegral_one_add_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y : Ω → ℝ≥0∞} {c q : ℝ} (hq : 1 ≤ q)
    (hY : ∫⁻ ω, Y ω ^ (c * q) ∂P < ⊤) :
    ∫⁻ ω, (1 + Y ω ^ c) ^ q ∂P < ⊤ := by
  calc ∫⁻ ω, (1 + Y ω ^ c) ^ q ∂P ≤ ∫⁻ ω, 2 ^ q * (1 + Y ω ^ (c * q)) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.rpow_mul]
        exact one_add_rpow_le hq
    _ = 2 ^ q * (1 + ∫⁻ ω, Y ω ^ (c * q) ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) (by simp))
        (ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hY⟩)

/-- **Uniform exponential decay of the cutoff increments** (`estF1`). -/
theorem exists_lintegral_cutoffIncrement_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    {a₁ a₂ : ℝ} (ha₁ : -2 * η - δ < a₁) (ha₂ : a₂ < 1 / γ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ a ∈ Icc a₁ a₂, ∀ n : ℕ,
      ∫⁻ ω, (cutoffTiltedMass γ η a (n + 1) (M ω) - cutoffTiltedMass γ η a n (M ω)) *
        (cutoffTiltedMass γ η a (n + 1) (M ω) ^ (-a / γ) +
          cutoffTiltedMass γ η a n (M ω) ^ (-a / γ)) ∂P ≤
        ENNReal.ofReal (C * Real.exp (-κ * n)) := by
  have _ := hX.1
  have hη := (window_eta_pos hW).le
  have hηγ := window_eta_le_two_div hγ hγ2 hW
  have hp := window_threshold_pos hγ hW
  have hroom := window_holder_room hγ hγ2 hW
  have hκ4 : 1 < 4 / γ ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
  have hγQ := gamma_mul_Q hγ
  set c₁ : ℝ := max (-a₁ / γ) 0 with hc₁
  set b₂ : ℝ := max a₂ 0 with hb₂
  have hc₁0 : 0 ≤ c₁ := le_max_right _ _
  have hb₂0 : 0 ≤ b₂ := le_max_right _ _
  have hγb₂ : γ * b₂ < 1 := by
    rcases le_or_gt a₂ 0 with h | h
    · rw [hb₂, max_eq_right h, mul_zero]
      norm_num
    · rw [hb₂, max_eq_left h.le, mul_comm]
      exact (lt_div_iff₀ hγ).1 ha₂
  have hroom' : 0 < (1 - 2 * η / γ) * (1 - 1 / (4 / γ ^ 2)) := by
    apply mul_pos hp
    have : 1 / (4 / γ ^ 2) < 1 := by rw [div_lt_one (by linarith)]; exact hκ4
    linarith
  have hc₁p : c₁ < (1 - 2 * η / γ) * (1 - 1 / (4 / γ ^ 2)) := by
    have hγ4 : 1 / (4 / γ ^ 2) = γ ^ 2 / 4 := by field_simp
    rcases le_or_gt (-a₁ / γ) 0 with h | h
    · rw [hc₁, max_eq_right h]
      exact hroom'
    · rw [hc₁, max_eq_left h.le, hγ4]
      refine lt_of_le_of_lt ?_ hroom
      exact div_le_div_of_nonneg_right (by linarith) hγ.le
  -- the measurable pieces
  have hB : ∀ n : ℕ, AEMeasurable (fun ω => M ω (Metric.ball 0 (Real.exp (-(n : ℝ))))) P :=
    fun n => aemeasurable_measure_functional P X hX γ hγ hγ2 M hM
      (Measure.measurable_coe Metric.isOpen_ball.measurableSet)
  have hT0 : AEMeasurable (fun ω => poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω)) P :=
    aemeasurable_measure_functional P X hX γ hγ hγ2 M hM (measurable_poleTotalMass γ η 0)
  have hL : AEMeasurable (fun ω => poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)) P :=
    aemeasurable_measure_functional P X hX γ hγ hγ2 M hM (measurable_poleLocalMass γ η)
  have hV1 : AEMeasurable (fun ω =>
      1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ c₁) P :=
    aemeasurable_const.add (hT0.pow_const _)
  have hV2 : AEMeasurable (fun ω =>
      1 + poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-(b₂ / γ))) P :=
    aemeasurable_const.add (hL.pow_const _)
  -- term 1: a nonpositive charge
  obtain ⟨r₁, hr₁1, hr₁4, hr₁c⟩ := exists_holder_exponent hc₁0 hκ4 hc₁p
  obtain ⟨Cb₁, -, hCb₁⟩ := exists_lintegral_ball_rpow_le P X hX γ hγ hγ2 M hM hr₁4
  have hq₁ : 1 ≤ r₁ / (r₁ - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hV1r : ∫⁻ ω, (1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ c₁) ^
      (r₁ / (r₁ - 1)) ∂P < ⊤ := by
    refine lintegral_one_add_rpow_lt_top hq₁ ?_
    rcases eq_or_lt_of_le hc₁0 with h0 | h0
    · rw [← h0, zero_mul]
      simp
    · exact lintegral_totalMass_rpow_lt_top P X hX γ hγ hγ2 M hM hη
        (mul_pos h0 (by linarith)) hr₁c
  obtain ⟨K₁, hK₁0, hK₁⟩ := holder_decay hB hV1 hr₁1 hCb₁ hV1r
  -- term 2: a positive charge
  set r₂ : ℝ := min ((1 + 4 / γ ^ 2) / 2) (1 + (1 - γ * b₂) / γ ^ 2) with hr₂
  have hr₂1 : 1 < r₂ := by
    rw [hr₂]
    refine lt_min (by linarith) ?_
    have : 0 < (1 - γ * b₂) / γ ^ 2 := div_pos (by linarith) (by positivity)
    linarith
  have hr₂4 : r₂ < 4 / γ ^ 2 := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨Cb₂, -, hCb₂⟩ := exists_lintegral_ball_rpow_le P X hX γ hγ hγ2 M hM hr₂4
  have hq₂ : 1 ≤ r₂ / (r₂ - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hV2r : ∫⁻ ω, (1 + poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-(b₂ / γ))) ^
      (r₂ / (r₂ - 1)) ∂P < ⊤ := by
    refine lintegral_one_add_rpow_lt_top hq₂ ?_
    have hs : 0 ≤ b₂ / γ := div_nonneg hb₂0 hγ.le
    rcases eq_or_lt_of_le hs with h0 | h0
    · rw [← h0, neg_zero, zero_mul]
      simp
    · have hq : 0 < b₂ / γ * (r₂ / (r₂ - 1)) := mul_pos h0 (by linarith)
      have h := lintegral_localMass_rpow_neg_lt_top P X hX γ hγ hγ2 M hM hη hηγ hq
      rwa [neg_mul]
  obtain ⟨K₂, hK₂0, hK₂⟩ := holder_decay hB hV2 hr₂1 hCb₂ hV2r
  -- the rates
  set κ₁ : ℝ := (γ * Q γ * r₁ - γ ^ 2 * r₁ ^ 2 / 2) / r₁ with hκ₁
  set κ₂ : ℝ := (γ * Q γ * r₂ - γ ^ 2 * r₂ ^ 2 / 2) / r₂ - γ * b₂ with hκ₂
  have hκ₁0 : 0 < κ₁ := by
    rw [hκ₁, ballExponent_div (by linarith), hγQ]
    have : γ ^ 2 * r₁ < 4 := by
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)).1 hr₁4
      linarith
    linarith only [this, sq_nonneg γ]
  have hκ₂0 : 0 < κ₂ := by
    rw [hκ₂, ballExponent_div (by linarith), hγQ]
    have h1 : r₂ ≤ 1 + (1 - γ * b₂) / γ ^ 2 := min_le_right _ _
    have h2 : γ ^ 2 * r₂ ≤ γ ^ 2 + (1 - γ * b₂) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ γ ^ 2)
      rwa [mul_add, mul_one, mul_div_cancel₀ _ (by positivity)] at this
    linarith only [h2, hγb₂]
  refine ⟨2 * K₁ + 2 * K₂ * Real.exp (γ * b₂), min κ₁ κ₂, by positivity, lt_min hκ₁0 hκ₂0,
    fun a ha n => ?_⟩
  have hpt : ∀ ω, (cutoffTiltedMass γ η a (n + 1) (M ω) - cutoffTiltedMass γ η a n (M ω)) *
        (cutoffTiltedMass γ η a (n + 1) (M ω) ^ (-a / γ) +
          cutoffTiltedMass γ η a n (M ω) ^ (-a / γ)) ≤
      2 * (M ω (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
          (1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ c₁)) +
        2 * ENNReal.ofReal (Real.exp (γ * b₂ * (n + 1))) *
          (M ω (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
            (1 + poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-(b₂ / γ)))) :=
    fun ω => cutoffIncrement_le hγ hη hηγ ha n (M ω)
  have hA : AEMeasurable (fun ω => 2 * (M ω (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
      (1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ c₁))) P :=
    ((hB n).mul hV1).const_mul _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left' hA,
    lintegral_const_mul' _ _ (by simp), lintegral_const_mul' _ _
      (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)]
  have h1 := hK₁ n
  have h2 := hK₂ n
  calc 2 * ∫⁻ ω, M ω (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
          (1 + poleTotalMass γ 0 (2 / γ + η) (2 / γ - η) (M ω) ^ c₁) ∂P +
        2 * ENNReal.ofReal (Real.exp (γ * b₂ * (n + 1))) *
          ∫⁻ ω, M ω (Metric.ball 0 (Real.exp (-(n : ℝ)))) *
            (1 + poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω) ^ (-(b₂ / γ))) ∂P
      ≤ 2 * ENNReal.ofReal (K₁ * Real.exp (-κ₁ * n)) +
          2 * ENNReal.ofReal (Real.exp (γ * b₂ * (n + 1))) *
            ENNReal.ofReal (K₂ * Real.exp (-((γ * Q γ * r₂ - γ ^ 2 * r₂ ^ 2 / 2) / r₂) * n)) :=
        add_le_add (mul_le_mul_right h1 _) (mul_le_mul_right h2 _)
    _ = ENNReal.ofReal (2 * K₁ * Real.exp (-κ₁ * n)) +
          ENNReal.ofReal (2 * K₂ * Real.exp (γ * b₂) * Real.exp (-κ₂ * n)) := by
        have h2' : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        rw [h2', ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        · ring
        · rw [hκ₂, mul_assoc (2 * K₂), ← Real.exp_add]
          rw [show 2 * Real.exp (γ * b₂ * (n + 1)) *
              (K₂ * Real.exp (-((γ * Q γ * r₂ - γ ^ 2 * r₂ ^ 2 / 2) / r₂) * n)) =
              2 * K₂ * (Real.exp (γ * b₂ * (n + 1)) *
                Real.exp (-((γ * Q γ * r₂ - γ ^ 2 * r₂ ^ 2 / 2) / r₂) * n)) by ring,
            ← Real.exp_add]
          congr 2
          ring
    _ ≤ ENNReal.ofReal ((2 * K₁ + 2 * K₂ * Real.exp (γ * b₂)) * Real.exp (-min κ₁ κ₂ * n)) :=
        ofReal_add_exp_le (by positivity) (by positivity) n

end DOZZ.Proofs

end
