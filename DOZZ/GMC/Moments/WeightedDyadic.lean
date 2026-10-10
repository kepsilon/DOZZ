/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Order.Filter.AtTopBot.Ring
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Order.Monotone
public import DOZZ.Statements.GMC.WeightedGmcBallMass
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import DOZZ.GMC.Moments.SubunitSet
public import DOZZ.GMC.Moments.WeightedExponent

/-! Countable subadditivity for nonnegative powers at orders at most one. -/

@[expose] public section

open Filter
open MeasureTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Every positive radius strictly inside a reference disk lies in one dyadic shell. -/
theorem exists_dyadic_shell_index {R d : ℝ}
    (hd : 0 < d) (hdR : d < R) :
    ∃ n : ℕ, R / (2 : ℝ) ^ (n + 1) ≤ d ∧ d < R / (2 : ℝ) ^ n := by
  let q : ℝ := R / d
  have hq : 1 < q := by
    dsimp [q]
    exact (one_lt_div hd).2 hdR
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop := by
    have h := (tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    exact h.congr' (Eventually.of_forall fun n => Real.rpow_natCast 2 n)
  have hexists : ∃ n : ℕ, q ≤ (2 : ℝ) ^ n := by
    obtain ⟨n, hn⟩ := (tendsto_atTop_atTop.mp hpow) q
    exact ⟨n, hn n le_rfl⟩
  let n : ℕ := Nat.find hexists
  have hqpow : q ≤ (2 : ℝ) ^ n := Nat.find_spec hexists
  have hnpos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0, pow_zero] at hqpow
    linarith
  have hprev : (2 : ℝ) ^ (n - 1) < q := by
    apply lt_of_not_ge
    intro h
    have hmin := Nat.find_min' hexists h
    omega
  refine ⟨n - 1, ?_, ?_⟩
  · have hqmul : R ≤ (2 : ℝ) ^ n * d := by
      dsimp [q] at hqpow
      exact (div_le_iff₀ hd).mp hqpow
    have htwopow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    have hbound : R / (2 : ℝ) ^ n ≤ d := (div_le_iff₀ (by positivity)).2 (by
      rw [htwopow] at hqmul ⊢
      linarith only [hqmul])
    have hindex : (n - 1) + 1 = n := by omega
    simpa [hindex] using hbound
  · have hprev' : (2 : ℝ) ^ (n - 1) * d < R := by
      dsimp [q] at hprev
      exact (lt_div_iff₀ hd).mp hprev
    have hbound : d < R / (2 : ℝ) ^ (n - 1) :=
      (lt_div_iff₀ (by positivity)).2 (by linarith only [hprev'])
    simpa using hbound

/-- The deterministic `n`th term in the dyadic upper bound for a root insertion. -/
noncomputable def dyadicWeightedBallTerm (μ : Measure ℂ) (γ R : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2) *
    μ (Metric.ball 0 (R / (2 : ℝ) ^ n))

private theorem ennreal_ofReal_rpow_of_pos {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  have hx0 : ENNReal.ofReal x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hleft : ENNReal.rpow (ENNReal.ofReal x) p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 ENNReal.ofReal_ne_top
  have hright : ENNReal.ofReal (x ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal =
        (ENNReal.ofReal x).toReal ^ p := (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal := by
        rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)]

/-- A negative-power root insertion on a centered ball is dominated by the sum of its dyadic
ball masses. The singular value at the root is covered by the divergent sum of all dyadic
indicators, so no atomlessness assumption is needed. -/
theorem weightedGmcBallMass_root_le_dyadic
    (μ : Measure ℂ) (γ R : ℝ) (hγ : 0 < γ) (hR : 0 < R) (hR1 : R ≤ 1) :
    weightedGmcBallMass γ μ γ 0 R ≤ ∑' n : ℕ, dyadicWeightedBallTerm μ γ R n := by
  let B : Set ℂ := Metric.ball 0 R
  let density : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ ^ 2)
  let coverTerm : ℕ → ℂ → ℝ≥0∞ := fun n x =>
    (Metric.ball 0 (R / (2 : ℝ) ^ n)).indicator (fun _ => ENNReal.rpow
      (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2)) x
  have hpoint (x : ℂ) : B.indicator density x ≤ ∑' n : ℕ, coverTerm n x := by
    by_cases hx : x ∈ B
    · have hxR : ‖x‖ < R := by simpa [B, Metric.mem_ball, dist_zero_right] using hx
      by_cases hzero : x = 0
      · subst x
        have hcoef (n : ℕ) : 1 ≤ ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2) := by
          have hradpos : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
          have hradle : R / (2 : ℝ) ^ (n + 1) ≤ 1 := by
            calc
              R / (2 : ℝ) ^ (n + 1) ≤ R := by
                apply (div_le_iff₀ (by positivity)).2
                calc
                  R = R * 1 := by ring
                  _ ≤ R * (2 : ℝ) ^ (n + 1) :=
                    mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le
              _ ≤ 1 := hR1
          have hbase : ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1)) ≤ 1 :=
            ENNReal.ofReal_le_one.mpr hradle
          calc
            1 = (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) ^ 0 := by simp
            _ ≤ (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) ^ (-γ ^ 2) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hbase (neg_nonpos.mpr (sq_nonneg γ))
        have hsumLower : (∑' _n : ℕ, (1 : ℝ≥0∞)) ≤
            ∑' n : ℕ, coverTerm n 0 := ENNReal.tsum_le_tsum fun n => by
          have hball : (0 : ℂ) ∈ Metric.ball 0 (R / (2 : ℝ) ^ n) := by
            simp only [Metric.mem_ball, dist_self]
            positivity
          simpa [coverTerm, hball] using hcoef n
        have hsum : ∑' n : ℕ, coverTerm n 0 = ⊤ := by
          have hsumConst : (⊤ : ℝ≥0∞) = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero).symm
          exact top_unique (hsumConst.symm ▸ hsumLower)
        have hleft : B.indicator density 0 = ⊤ := by
          have hball : (0 : ℂ) ∈ B := by simpa [B, Metric.mem_ball] using hR
          rw [Set.indicator_of_mem hball]
          change ENNReal.rpow (ENNReal.ofReal ‖(0 : ℂ)‖) (-γ ^ 2) = ⊤
          simpa using (ENNReal.zero_rpow_of_neg (show -γ ^ 2 < 0 by linarith only [sq_pos_of_pos hγ]))
        rw [hleft, hsum]
      · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hzero
        obtain ⟨n, hlo, hhi⟩ := exists_dyadic_shell_index hnorm hxR
        have hlowpos : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
        have hpow : ‖x‖ ^ (-γ ^ 2) ≤
            (R / (2 : ℝ) ^ (n + 1)) ^ (-γ ^ 2) :=
          Real.rpow_le_rpow_of_nonpos hlowpos hlo (neg_nonpos.mpr (sq_nonneg γ))
        have hden : density x ≤ ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2) := by
          change ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ ^ 2) ≤ _
          rw [ennreal_ofReal_rpow_of_pos hnorm,
            ennreal_ofReal_rpow_of_pos hlowpos]
          exact ENNReal.ofReal_le_ofReal hpow
        have hball : x ∈ B := hx
        have hballn : x ∈ Metric.ball 0 (R / (2 : ℝ) ^ n) := by
          simpa [Metric.mem_ball, dist_zero_right] using hhi
        have hcover : coverTerm n x = ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2) := by
          simp [coverTerm, hballn]
        calc
          B.indicator density x = density x := by simp [hball]
          _ ≤ coverTerm n x := by rw [hcover]; exact hden
          _ ≤ ∑' j : ℕ, coverTerm j x :=
            ENNReal.le_tsum (f := fun j => coverTerm j x) n
    · simp [hx]
  calc
    weightedGmcBallMass γ μ γ 0 R = ∫⁻ x, B.indicator density x ∂μ := by
      rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
      simp [B, density, show -γ * γ = -γ ^ 2 by ring]
    _ ≤ ∫⁻ x, ∑' n : ℕ, coverTerm n x ∂μ := lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ x, coverTerm n x ∂μ := by
      rw [lintegral_tsum]
      intro n
      exact (measurable_const.indicator (Metric.isOpen_ball.measurableSet)).aemeasurable
    _ = ∑' n : ℕ, dyadicWeightedBallTerm μ γ R n := by
      congr 1
      funext n
      rw [show coverTerm n = (Metric.ball 0 (R / (2 : ℝ) ^ n)).indicator (fun _ =>
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2)) by rfl]
      rw [lintegral_indicator_const (Metric.isOpen_ball.measurableSet)]
      simp [dyadicWeightedBallTerm]

private theorem half_div_two_pow (n : ℕ) :
    (1 / 2 : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ (n + 1) := by
  rw [pow_succ]
  field_simp
  rw [← mul_pow]
  norm_num

private theorem half_coefficient_rpow (γ p : ℝ) (n : ℕ) :
    (ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1)))
      (-γ ^ 2)) ^ p =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p))) := by
  have hrad : 0 < (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1) := by positivity
  calc
    (ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1)))
        (-γ ^ 2)) ^ p = ENNReal.rpow (ENNReal.ofReal
          ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1))) ((-γ ^ 2) * p) :=
      (ENNReal.rpow_mul _ _ _).symm
    _ = ENNReal.ofReal (((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1)) ^ ((-γ ^ 2) * p)) :=
      ennreal_ofReal_rpow_of_pos hrad
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p))) := by
      rw [half_div_two_pow (n + 1), ← Real.rpow_natCast_mul (by norm_num :
        (0 : ℝ) ≤ 1 / 2) (n + 2) (-γ ^ 2 * p)]

theorem gmc_half_dyadic_ball_moment_scale_at
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (hz : ‖z‖ + (1 / 2 : ℝ) < 1) (p : ℝ) (n : ℕ) :
    gmcMassMoment P M (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n)) p =
      ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^
        (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        gmcMassMoment P M (Metric.ball 0 (1 / 2)) p := by
  let c : ℝ := (1 / 2 : ℝ) ^ n
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsmall : ‖z‖ + c * (1 / 2 : ℝ) < 1 := by
    have hmul := mul_le_mul_of_nonneg_right hc1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      ‖z‖ + c * (1 / 2 : ℝ) ≤ ‖z‖ + (1 / 2 : ℝ) := by linarith only [hmul]
      _ < 1 := hz
  have hscale := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (a := z) (c := c) (R := (1 / 2 : ℝ)) hc hc1 (by norm_num) (by norm_num) hsmall p
  have hhalfPow : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
    rw [div_pow, one_pow]
    simp
  have hrad : c * (1 / 2 : ℝ) = (1 / 2 : ℝ) / (2 : ℝ) ^ n := by
    dsimp [c]
    rw [hhalfPow]
    rw [div_eq_mul_inv]
    ring
  rw [← hrad]
  exact hscale

/-- Exact cutoff-free moment scaling for dyadic balls about any center whose outer ball stays in
the logarithmic chart, with a radius other than the reference half-disk. -/
theorem gmc_chart_dyadic_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hRlt : R < 1)
    (hz : ‖z‖ + R < 1) (p : ℝ) (n : ℕ) :
    gmcMassMoment P M (Metric.ball z (R / (2 : ℝ) ^ n)) p =
      ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^
        (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        gmcMassMoment P M (Metric.ball 0 R) p := by
  let c : ℝ := (1 / 2 : ℝ) ^ n
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hsmall : ‖z‖ + c * R < 1 := by
    have hmul := mul_le_mul_of_nonneg_right hc1 hR.le
    calc
      ‖z‖ + c * R ≤ ‖z‖ + R := by linarith only [hmul]
      _ < 1 := hz
  have hrad : c * R = R / (2 : ℝ) ^ n := by
    dsimp [c]
    rw [show (1 / 2 : ℝ) ^ n = 1 / (2 : ℝ) ^ n by
      rw [div_pow]
      simp]
    ring
  have hscale := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (a := z) (c := c) (R := R) hc hc1 hR hRlt hsmall p
  rw [← hrad]
  exact hscale

private theorem ennreal_rpow_finset_sum_le_tsum_rpow
    {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, a i) ^ p ≤ ∑ i ∈ s, (a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hp]
  | @insert i s his ih =>
      rw [Finset.sum_insert his, Finset.sum_insert his]
      exact ENNReal.rpow_add_le_add_rpow (a i) (∑ j ∈ s, a j) hp.le hp1 |>.trans
        (add_le_add_right ih _)

/-- For `0 < p ≤ 1`, the `p`th power of a countable sum is bounded by the sum of the `p`th
powers. -/
theorem ennreal_rpow_tsum_le_tsum_rpow
    {ι : Type*} [Countable ι] (a : ι → ℝ≥0∞) {p : ℝ}
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑' i, a i) ^ p ≤ ∑' i, (a i) ^ p := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum, ENNReal.tsum_eq_iSup_sum]
  have hmono : Monotone (fun x : ℝ≥0∞ => x ^ p) := fun _ _ h =>
    ENNReal.rpow_le_rpow h hp.le
  have hzero : (0 : ℝ≥0∞) ^ p = 0 := ENNReal.zero_rpow_of_pos hp
  have hcontinuous : Continuous (fun x : ℝ≥0∞ => x ^ p) :=
    ENNReal.continuous_rpow_const
  rw [hmono.map_iSup_of_continuousAt
    hcontinuous.continuousAt hzero]
  apply iSup_le
  intro s
  exact (ennreal_rpow_finset_sum_le_tsum_rpow s a hp hp1).trans
    (le_iSup_of_le s le_rfl)

/-- At the root, the weighted local moment is finite for subunit orders below the insertion
threshold. The proof sums dyadic ball masses and uses the exact affine scaling law. -/
theorem weightedGmcBallMoment_root_finite_subunit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - γ))) :
    weightedGmcBallMoment P M γ γ 0 (1 / 2) p < ⊤ := by
  classical
  let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let eta : ℝ := 2 * p - γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)
  let base : ℝ≥0∞ := gmcMassMoment P M (Metric.ball 0 (1 / 2)) p
  let C : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p)) * base
  let coeff (n : ℕ) : ℝ≥0∞ :=
    ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1))) (-γ ^ 2)
  have hbaseFinite : base < ⊤ := by
    have hbulk : p < 4 / γ ^ 2 := by
      have hγsq : γ ^ 2 < 4 := by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
      have hthreshold : 1 < 4 / γ ^ 2 := by
        rw [one_lt_div (sq_pos_of_pos hγ)]
        linarith only [hγsq]
      exact hp1.trans_lt hthreshold
    exact (gmc_mass_moment_finite_iff_on_subunit_interval P X hX γ hγ hγ2
      M hM (Metric.ball 0 (1 / 2)) hp hp1).2 hbulk
  have hslack := weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange
  have heta : γ * (Q γ - γ) * p - γ ^ 2 * p ^ 2 / 2 = eta := by
    dsimp [eta, Q]
    field_simp [ne_of_gt hγ]
    ring
  have hetaPos : 0 < eta := by rw [← heta]; exact hslack
  have hqReal : (1 / 2 : ℝ) ^ eta < 1 := by
    exact Real.rpow_lt_one (by norm_num) (by norm_num) hetaPos
  have hq : q < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (by simpa [q] using hqReal)
  have hmassMeas (n : ℕ) : AEMeasurable
      (fun ω => M ω (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
      (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n)) Metric.isOpen_ball.measurableSet
  have hmassPowMeas (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.rpow (M ω (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p) P := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmassMeas n)
  have htermMeas (n : ℕ) : AEMeasurable
      (fun ω => (dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p) P := by
    have hmul : AEMeasurable (fun ω => coeff n *
        M ω (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) P :=
      aemeasurable_const.mul (hmassMeas n)
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmul
  have htermInt (n : ℕ) :
    ∫⁻ ω, (dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p ∂P =
      C * q ^ n := by
    have hraw :
        ∫⁻ ω, (dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p ∂P =
          (coeff n) ^ p *
            gmcMassMoment P M (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n)) p := by
      calc
        _ = ∫⁻ ω, (coeff n) ^ p *
              ENNReal.rpow (M ω (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p ∂P := by
          apply lintegral_congr
          intro ω
          simp only [dyadicWeightedBallTerm, coeff]
          change ENNReal.rpow (_ * _) p = _
          exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
        _ = (coeff n) ^ p * ∫⁻ ω,
              ENNReal.rpow (M ω (Metric.ball 0 ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p ∂P :=
          lintegral_const_mul'' _ (hmassPowMeas n)
        _ = _ := by rfl
    have hcoeff : (coeff n) ^ p = ENNReal.ofReal
        ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p))) := by
      simpa [coeff] using half_coefficient_rpow γ p n
    have hballScale := gmc_half_dyadic_ball_moment_scale_at P X hX γ hγ hγ2 M hM
      0 (by norm_num) p n
    have hscalePower : ((1 / 2 : ℝ) ^ n) ^ xi =
        (1 / 2 : ℝ) ^ ((n : ℝ) * xi) := by
      dsimp [xi]
      exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) n _).symm
    have hreal :
        (1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p)) *
            (1 / 2 : ℝ) ^ ((n : ℝ) * xi) =
          (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) * ((1 / 2 : ℝ) ^ eta) ^ n := by
      calc
        _ = (1 / 2 : ℝ) ^ (((n + 2 : ℕ) : ℝ) * (-γ ^ 2 * p) + (n : ℝ) * xi) :=
          (Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _).symm
        _ = (1 / 2 : ℝ) ^ (((n : ℝ) + 2) * (-γ ^ 2 * p) + (n : ℝ) * xi) := by
          congr 1
          norm_cast
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p + (n : ℝ) * eta) := by
          congr 1
          dsimp [eta, xi]
          ring
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
              (1 / 2 : ℝ) ^ ((n : ℝ) * eta) :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) * ((1 / 2 : ℝ) ^ eta) ^ n := by
          congr 1
          rw [show (n : ℝ) * eta = eta * (n : ℝ) by ring,
            Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      _ = (coeff n) ^ p *
          (ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ xi) * base) := by
            rw [hraw, hballScale]
      _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p))) *
          (ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n : ℝ) * xi)) * base) := by
            rw [hcoeff, hscalePower]
      _ = C * q ^ n := by
        dsimp [C, q]
        have hrealNonneg₁ : 0 ≤ (1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p)) :=
          Real.rpow_nonneg (by norm_num) _
        have hrealNonneg₂ : 0 ≤ (1 / 2 : ℝ) ^ ((n : ℝ) * xi) :=
          Real.rpow_nonneg (by norm_num) _
        have hconv : ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p))) *
              ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n : ℝ) * xi)) =
            ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p)) *
              (ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)) ^ n := by
          calc
            _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p)) *
                  (1 / 2 : ℝ) ^ ((n : ℝ) * xi)) := by
                    rw [ENNReal.ofReal_mul hrealNonneg₁]
            _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
                  ((1 / 2 : ℝ) ^ eta) ^ n) := by rw [hreal]
            _ = _ := by
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
                ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) n]
        calc
          _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ ^ 2 * p))) *
                ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n : ℝ) * xi))) * base := by ac_rfl
          _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p)) *
                (ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)) ^ n) * base := by rw [hconv]
          _ = _ := by ac_rfl
  have hseries : ∑' n : ℕ, C * q ^ n = C * (1 - q)⁻¹ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  have hden : 1 - q ≠ 0 := by
    intro hzero
    have hle : 1 ≤ q := (tsub_eq_zero_iff_le.mp hzero)
    exact (not_le_of_gt hq) hle
  have hgeom : (1 - q)⁻¹ < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden)
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbaseFinite
  have hsumFinite : (∑' n : ℕ, C * q ^ n) < ⊤ := by
    rw [hseries]
    exact ENNReal.mul_lt_top hC hgeom
  calc
    weightedGmcBallMoment P M γ γ 0 (1 / 2) p ≤
        ∑' n : ℕ, ∫⁻ ω, (dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p ∂P := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (∑' n : ℕ, dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow
            (weightedGmcBallMass_root_le_dyadic (M ω) γ (1 / 2) hγ (by norm_num)
              (by norm_num) ) hp.le
        _ ≤ ∫⁻ ω, ∑' n : ℕ,
              (dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ennreal_rpow_tsum_le_tsum_rpow _ hp hp1
        _ = ∑' n : ℕ, ∫⁻ ω,
              (dyadicWeightedBallTerm (M ω) γ (1 / 2) n) ^ p ∂P := by
          rw [lintegral_tsum htermMeas]
    _ = ∑' n : ℕ, C * q ^ n := by
      apply tsum_congr
      intro n
      exact htermInt n
    _ < ⊤ := hsumFinite

/-- Every `0 < γ < 2` admits a positive subunit order strictly below the root insertion
threshold. -/
theorem exists_subunit_order_below_gamma_insertion {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      p < min (4 / γ ^ 2) (2 / γ * (Q γ - γ)) := by
  have hQ : 0 < Q γ - γ := by
    dsimp [Q]
    have hγsq : γ ^ 2 < 4 := by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
    field_simp [ne_of_gt hγ]
    linarith only [hγsq]
  let s : ℝ := 2 / γ * (Q γ - γ)
  have hs : 0 < s := by positivity
  let b : ℝ := min 1 s
  have hb : 0 < b := by positivity
  have hb1 : b ≤ 1 := min_le_left _ _
  have hbs : b ≤ s := min_le_right _ _
  let p : ℝ := b / 2
  have hp : 0 < p := by positivity
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hpin : p < s := by dsimp [p]; linarith
  have hbulk : 1 < 4 / γ ^ 2 := by
    have hγsq : γ ^ 2 < 4 := by linarith only [mul_lt_mul'' hγ2 hγ2 hγ.le hγ.le]
    rw [one_lt_div (sq_pos_of_pos hγ)]
    linarith only [hγsq]
  have hpbulk : p < 4 / γ ^ 2 := lt_of_le_of_lt hp1 hbulk
  refine ⟨p, hp, hp1, ?_⟩
  rw [lt_min_iff]
  exact ⟨hpbulk, by simpa [s] using hpin⟩

/-- Construction-facing form of the root weighted local estimate: for every admissible coupling,
there is a positive order at `α = γ` for which the weighted mass of the reference half-ball has a
finite moment. -/
theorem exists_finite_weightedGmcBallMoment_at_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
      p < min (4 / γ ^ 2) (2 / γ * (Q γ - γ)) ∧
      weightedGmcBallMoment P M γ γ 0 (1 / 2) p < ⊤ := by
  obtain ⟨p, hp, hp1, hpRange⟩ := exists_subunit_order_below_gamma_insertion hγ hγ2
  exact ⟨p, hp, hp1, hpRange,
    weightedGmcBallMoment_root_finite_subunit P X hX γ hγ hγ2 M hM p hp hp1 hpRange⟩

/-- A dyadic shell bound for a positive insertion charge. The coefficient is evaluated at the
inner edge of the shell, where the negative radial power is largest. -/
theorem weightedGmcBallMass_root_le_dyadic_charge
    (μ : Measure ℂ) (γ α R : ℝ) (hγ : 0 < γ) (hα : 0 < α)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    weightedGmcBallMass γ μ α 0 R ≤
      ∑' n : ℕ,
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
          μ (Metric.ball 0 (R / (2 : ℝ) ^ n)) := by
  let B : Set ℂ := Metric.ball 0 R
  let density : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * α)
  let coverTerm : ℕ → ℂ → ℝ≥0∞ := fun n x =>
    (Metric.ball 0 (R / (2 : ℝ) ^ n)).indicator (fun _ =>
      ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) x
  have hpowerNeg : -γ * α < 0 := mul_neg_of_neg_of_pos (neg_neg_of_pos hγ) hα
  have hpoint (x : ℂ) : B.indicator density x ≤ ∑' n : ℕ, coverTerm n x := by
    by_cases hx : x ∈ B
    · have hxR : ‖x‖ < R := by
        simpa [B, Metric.mem_ball, dist_zero_right] using hx
      by_cases hzero : x = 0
      · subst x
        have hcoef (n : ℕ) : 1 ≤ ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) := by
          have hradpos : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
          have hradle : R / (2 : ℝ) ^ (n + 1) ≤ 1 := by
            calc
              R / (2 : ℝ) ^ (n + 1) ≤ R := by
                apply (div_le_iff₀ (by positivity)).2
                calc
                  R = R * 1 := by ring
                  _ ≤ R * (2 : ℝ) ^ (n + 1) :=
                    mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num)) hR.le
              _ ≤ 1 := hR1
          have hbase : ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1)) ≤ 1 :=
            ENNReal.ofReal_le_one.mpr hradle
          calc
            1 = (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) ^ 0 := by simp
            _ ≤ (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) ^ (-γ * α) :=
              ENNReal.rpow_le_rpow_of_exponent_ge hbase (by linarith)
        have hsumLower : (∑' _n : ℕ, (1 : ℝ≥0∞)) ≤
            ∑' n : ℕ, coverTerm n 0 := ENNReal.tsum_le_tsum fun n => by
          have hball : (0 : ℂ) ∈ Metric.ball 0 (R / (2 : ℝ) ^ n) := by
            simp only [Metric.mem_ball, dist_self]
            positivity
          simpa [coverTerm, hball] using hcoef n
        have hsum : ∑' n : ℕ, coverTerm n 0 = ⊤ := by
          have hsumConst : (⊤ : ℝ≥0∞) = ∑' _n : ℕ, (1 : ℝ≥0∞) :=
            (ENNReal.tsum_const_eq_top_of_ne_zero (α := ℕ) one_ne_zero).symm
          exact top_unique (hsumConst.symm ▸ hsumLower)
        have hleft : B.indicator density 0 = ⊤ := by
          have hball : (0 : ℂ) ∈ B := by simpa [B, Metric.mem_ball] using hR
          rw [Set.indicator_of_mem hball]
          change ENNReal.rpow (ENNReal.ofReal ‖(0 : ℂ)‖) (-γ * α) = ⊤
          simpa using (ENNReal.zero_rpow_of_neg hpowerNeg)
        rw [hleft, hsum]
      · have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hzero
        obtain ⟨n, hlo, hhi⟩ := exists_dyadic_shell_index hnorm hxR
        have hlowpos : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
        have hpow : ‖x‖ ^ (-γ * α) ≤
            (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α) :=
          Real.rpow_le_rpow_of_nonpos hlowpos hlo (by linarith)
        have hden : density x ≤ ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) := by
          change ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * α) ≤ _
          rw [ennreal_ofReal_rpow_of_pos hnorm, ennreal_ofReal_rpow_of_pos hlowpos]
          exact ENNReal.ofReal_le_ofReal hpow
        have hball : x ∈ B := hx
        have hballn : x ∈ Metric.ball 0 (R / (2 : ℝ) ^ n) := by
          simpa [Metric.mem_ball, dist_zero_right] using hhi
        have hcover : coverTerm n x = ENNReal.rpow
            (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) := by
          simp [coverTerm, hballn]
        calc
          B.indicator density x = density x := by simp [hball]
          _ ≤ coverTerm n x := by rw [hcover]; exact hden
          _ ≤ ∑' j : ℕ, coverTerm j x :=
            ENNReal.le_tsum (f := fun j => coverTerm j x) n
    · simp [hx]
  calc
    weightedGmcBallMass γ μ α 0 R = ∫⁻ x, B.indicator density x ∂μ := by
      rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
      simp [B, density]
    _ ≤ ∫⁻ x, ∑' n : ℕ, coverTerm n x ∂μ := lintegral_mono hpoint
    _ = ∑' n : ℕ, ∫⁻ x, coverTerm n x ∂μ := by
      rw [lintegral_tsum]
      intro n
      exact (measurable_const.indicator (Metric.isOpen_ball.measurableSet)).aemeasurable
    _ = ∑' n : ℕ,
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
          μ (Metric.ball 0 (R / (2 : ℝ) ^ n)) := by
      congr 1
      funext n
      rw [show coverTerm n = (Metric.ball 0 (R / (2 : ℝ) ^ n)).indicator
        (fun _ => ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) by rfl]
      rw [lintegral_indicator_const (Metric.isOpen_ball.measurableSet)]

/-- Translation of the weighted ball integral to a centered ball for the pushforward measure. -/
theorem weightedGmcBallMass_translate
    (μ : Measure ℂ) (γ α R : ℝ) (z : ℂ) :
    weightedGmcBallMass γ μ α z R =
      weightedGmcBallMass γ (Measure.map (fun x : ℂ => x - z) μ) α 0 R := by
  classical
  let f : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x - (0 : ℂ)‖) (-γ * α)
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have htranslate : Measurable (fun x : ℂ => x - z) := measurable_sub_const z
  rw [weightedGmcBallMass, weightedGmcBallMass,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet]
  change (∫⁻ x, (Metric.ball z R).indicator
      (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - z‖) (-γ * α)) x ∂μ) =
    ∫⁻ x, (Metric.ball 0 R).indicator f x ∂Measure.map (fun x : ℂ => x - z) μ
  rw [lintegral_map' (by
    exact (hf.indicator Metric.isOpen_ball.measurableSet).aemeasurable)
    htranslate.aemeasurable]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Metric.ball z R
  · have hy : x - z ∈ Metric.ball 0 R := by
      simpa [Metric.mem_ball, dist_zero_right, dist_eq_norm] using hx
    simp [hx, hy, f]
  · have hy : x - z ∉ Metric.ball 0 R := by
      intro hy
      apply hx
      simpa [Metric.mem_ball, dist_zero_right, dist_eq_norm] using hy
    simp [hx, hy, f]

/-- Translation of a ball mass under the corresponding pushforward measure. -/
theorem measure_sub_pushforward_ball
    (μ : Measure ℂ) (z : ℂ) (R : ℝ) :
    Measure.map (fun x : ℂ => x - z) μ (Metric.ball 0 R) = μ (Metric.ball z R) := by
  have hf : Measurable (fun x : ℂ => x - z) := measurable_sub_const z
  rw [Measure.map_apply hf Metric.isOpen_ball.measurableSet]
  congr 1
  ext x
  simp [Metric.mem_ball, dist_eq_norm]

/-- Dyadic upper bound for a negative-power insertion about an arbitrary center. -/
theorem weightedGmcBallMass_le_dyadic_charge_center
    (μ : Measure ℂ) (γ α R : ℝ) (z : ℂ) (hγ : 0 < γ) (hα : 0 < α)
    (hR : 0 < R) (hR1 : R ≤ 1) :
    weightedGmcBallMass γ μ α z R ≤
      ∑' n : ℕ,
        ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
          μ (Metric.ball z (R / (2 : ℝ) ^ n)) := by
  have htranslate := weightedGmcBallMass_translate μ γ α R z
  have hroot := weightedGmcBallMass_root_le_dyadic_charge
    (Measure.map (fun x : ℂ => x - z) μ) γ α R hγ hα hR hR1
  rw [htranslate]
  simpa only [measure_sub_pushforward_ball] using hroot

/-- For nonpositive insertion charge the radial weight is bounded on the reference unit disk. -/
theorem weightedGmcBallMass_root_le_constant
    (μ : Measure ℂ) (γ α R : ℝ) (hγ : 0 < γ) (hα : α ≤ 0)
    (hR : 0 < R) :
    weightedGmcBallMass γ μ α 0 R ≤
      ENNReal.ofReal (R ^ (-γ * α)) * μ (Metric.ball 0 R) := by
  let B : Set ℂ := Metric.ball 0 R
  let density : ℂ → ℝ≥0∞ := fun x =>
    ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * α)
  have hq : 0 ≤ -γ * α := by
    have hprod : γ * α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ.le hα
    linarith only [hprod]
  have hpoint (x : ℂ) : B.indicator density x ≤
      ENNReal.ofReal (R ^ (-γ * α)) * B.indicator (fun _ => (1 : ℝ≥0∞)) x := by
    by_cases hx : x ∈ B
    · have hxR : ‖x‖ ≤ R := by
        have hx' : ‖x‖ < R := by
          simpa [B, Metric.mem_ball, dist_zero_right] using hx
        exact hx'.le
      have hpow : ENNReal.rpow (ENNReal.ofReal ‖x‖) (-γ * α) ≤
          ENNReal.rpow (ENNReal.ofReal R) (-γ * α) :=
        ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hxR) hq
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      calc
        density x ≤ ENNReal.rpow (ENNReal.ofReal R) (-γ * α) := hpow
        _ = ENNReal.ofReal (R ^ (-γ * α)) :=
          ennreal_ofReal_rpow_of_pos hR
        _ = ENNReal.ofReal (R ^ (-γ * α)) * 1 := by rw [mul_one]
    · simp [hx]
  calc
    weightedGmcBallMass γ μ α 0 R = ∫⁻ x, B.indicator density x ∂μ := by
      rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
      simp [B, density]
    _ ≤ ∫⁻ x, ENNReal.ofReal (R ^ (-γ * α)) *
          B.indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := lintegral_mono hpoint
    _ = ENNReal.ofReal (R ^ (-γ * α)) * μ B := by
      rw [lintegral_const_mul'']
      · rw [lintegral_indicator_const (Metric.isOpen_ball.measurableSet)]
        simp [B]
      · exact (measurable_const.indicator Metric.isOpen_ball.measurableSet).aemeasurable

/-- Bounded-weight comparison for a nonpositive insertion about an arbitrary center. -/
theorem weightedGmcBallMass_le_constant_center
    (μ : Measure ℂ) (γ α R : ℝ) (z : ℂ) (hγ : 0 < γ) (hα : α ≤ 0) (hR : 0 < R) :
    weightedGmcBallMass γ μ α z R ≤
      ENNReal.ofReal (R ^ (-γ * α)) * μ (Metric.ball z R) := by
  have htranslate := weightedGmcBallMass_translate μ γ α R z
  have hroot := weightedGmcBallMass_root_le_constant
    (Measure.map (fun x : ℂ => x - z) μ) γ α R hγ hα hR
  rw [htranslate]
  simpa only [measure_sub_pushforward_ball] using hroot

/-- Every subunit positive order below the full insertion range is finite on a half disk whose
closure lies in the exact logarithmic chart, for every real charge. -/
theorem weightedGmcBallMoment_chart_half_finite_subunit_all_charge
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α p : ℝ) (z : ℂ) (hz : ‖z‖ + (1 / 2 : ℝ) < 1) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    weightedGmcBallMoment P M γ α z (1 / 2) p < ⊤ := by
  by_cases hα : α ≤ 0
  · have hballFinite : gmcMassMoment P M (Metric.ball z (1 / 2)) p < ⊤ := by
      have hbulk : p < 4 / γ ^ 2 := (lt_min_iff.mp hpRange).1
      exact (gmc_mass_moment_finite_iff_on_subunit_interval P X hX γ hγ hγ2
        M hM (Metric.ball z (1 / 2)) hp hp1).2 hbulk
    have hcoefPos : ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α)) < ⊤ := ENNReal.ofReal_lt_top
    have hcoefMom : (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α))) ^ p < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg hp.le hcoefPos.ne
    have hbound : weightedGmcBallMoment P M γ α z (1 / 2) p ≤
        (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α))) ^ p *
          gmcMassMoment P M (Metric.ball z (1 / 2)) p := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α)) *
              M ω (Metric.ball z (1 / 2))) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow
            (weightedGmcBallMass_le_constant_center (M ω) γ α (1 / 2) z hγ hα
              (by norm_num)) hp.le
        _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α))) ^ p *
              gmcMassMoment P M (Metric.ball z (1 / 2)) p := by
          have hmeas : AEMeasurable (fun ω =>
              ENNReal.rpow (M ω (Metric.ball z (1 / 2))) p) P := by
            exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
                (Metric.ball z (1 / 2)) Metric.isOpen_ball.measurableSet)
          calc
            _ = ∫⁻ ω, (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-γ * α))) ^ p *
                  ENNReal.rpow (M ω (Metric.ball z (1 / 2))) p ∂P := by
              apply lintegral_congr
              intro ω
              exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
            _ = _ := by rw [lintegral_const_mul'' _ hmeas, gmcMassMoment]
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hcoefMom hballFinite)
  · have hαpos : 0 < α := lt_of_not_ge hα
    let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
    let eta : ℝ := xi - γ * α * p
    let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)
    let base : ℝ≥0∞ := gmcMassMoment P M (Metric.ball 0 (1 / 2)) p
    let C : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ * α * p)) * base
    let coeff (n : ℕ) : ℝ≥0∞ :=
      ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1))) (-γ * α)
    have hbaseFinite : base < ⊤ := by
      have hbulk : p < 4 / γ ^ 2 := (lt_min_iff.mp hpRange).1
      exact (gmc_mass_moment_finite_iff_on_subunit_interval P X hX γ hγ hγ2
        M hM (Metric.ball 0 (1 / 2)) hp hp1).2 hbulk
    have heta : γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 = eta := by
      dsimp [eta, xi, Q]
      field_simp [ne_of_gt hγ]
      ring
    have hetaPos : 0 < eta := by
      rw [← heta]
      exact weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange
    have hqReal : (1 / 2 : ℝ) ^ eta < 1 :=
      Real.rpow_lt_one (by norm_num) (by norm_num) hetaPos
    have hq : q < 1 := ENNReal.ofReal_lt_one.mpr (by simpa [q] using hqReal)
    have hmassMeas (n : ℕ) : AEMeasurable
        (fun ω => M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) P :=
      gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
        (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n)) Metric.isOpen_ball.measurableSet
    have hmassPowMeas (n : ℕ) : AEMeasurable
        (fun ω => ENNReal.rpow (M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmassMeas n)
    have htermMeas (n : ℕ) : AEMeasurable
        (fun ω => ENNReal.rpow
          (ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1))) (-γ * α) *
            M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p) P := by
      have hmul : AEMeasurable (fun ω => coeff n *
          M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) P :=
        aemeasurable_const.mul (hmassMeas n)
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmul
    have htermInt (n : ℕ) :
        ∫⁻ ω, (ENNReal.rpow (coeff n *
          M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p) ∂P = C * q ^ n := by
      have hraw :
          ∫⁻ ω, ENNReal.rpow (coeff n *
            M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p ∂P =
            coeff n ^ p * gmcMassMoment P M
              (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n)) p := by
        calc
          _ = ∫⁻ ω, coeff n ^ p *
                ENNReal.rpow (M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) p ∂P := by
            apply lintegral_congr
            intro ω
            exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
          _ = _ := by
            rw [lintegral_const_mul'' _ (hmassPowMeas n), gmcMassMoment]
      have hcoeff (n : ℕ) : coeff n ^ p =
          ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ * α * p))) := by
        have hrad : 0 < (1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1) := by positivity
        calc
          coeff n ^ p = ENNReal.rpow
              (ENNReal.ofReal ((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1))) ((-γ * α) * p) :=
            (ENNReal.rpow_mul _ _ _).symm
          _ = ENNReal.ofReal
              (((1 / 2 : ℝ) / (2 : ℝ) ^ (n + 1)) ^ ((-γ * α) * p)) :=
            ennreal_ofReal_rpow_of_pos hrad
          _ = _ := by
            rw [half_div_two_pow (n + 1), ← Real.rpow_natCast_mul
              (by norm_num : (0 : ℝ) ≤ 1 / 2) (n + 2) (-γ * α * p)]
      have hscale := gmc_half_dyadic_ball_moment_scale_at P X hX γ hγ hγ2 M hM
        z hz p n
      have hxi : ((1 / 2 : ℝ) ^ n) ^ xi =
          (1 / 2 : ℝ) ^ ((n : ℝ) * xi) := by
        dsimp [xi]
        exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) n _).symm
      have hreal :
          (1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ * α * p)) *
            (1 / 2 : ℝ) ^ ((n : ℝ) * xi) =
          (1 / 2 : ℝ) ^ (-2 * γ * α * p) * ((1 / 2 : ℝ) ^ eta) ^ n := by
        calc
          _ = (1 / 2 : ℝ) ^ (((n + 2 : ℕ) : ℝ) * (-γ * α * p) +
                (n : ℝ) * xi) := (Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _).symm
          _ = (1 / 2 : ℝ) ^ (((n : ℝ) + 2) * (-γ * α * p) + (n : ℝ) * xi) := by
            congr 1
            norm_cast
          _ = (1 / 2 : ℝ) ^ (-2 * γ * α * p + (n : ℝ) * eta) := by
            congr 1
            dsimp [eta, xi]
            ring
          _ = (1 / 2 : ℝ) ^ (-2 * γ * α * p) *
                (1 / 2 : ℝ) ^ ((n : ℝ) * eta) :=
            Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _
          _ = (1 / 2 : ℝ) ^ (-2 * γ * α * p) * ((1 / 2 : ℝ) ^ eta) ^ n := by
            congr 1
            rw [show (n : ℝ) * eta = eta * (n : ℝ) by ring,
              Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      calc
        _ = coeff n ^ p *
            (ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ xi) * base) := by
              rw [hraw, hscale]
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ * α * p))) *
            (ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n : ℝ) * xi)) * base) := by
              rw [hcoeff, hxi]
        _ = C * q ^ n := by
          dsimp [C, q]
          have hconv :
              ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ * α * p))) *
                ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n : ℝ) * xi)) =
              ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ * α * p)) *
                (ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)) ^ n := by
            calc
              _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ * α * p)) *
                    (1 / 2 : ℝ) ^ ((n : ℝ) * xi)) := by
                      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
              _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ * α * p) *
                    ((1 / 2 : ℝ) ^ eta) ^ n) := by rw [hreal]
              _ = _ := by
                rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
                  ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) n]
          calc
            _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n + 2 : ℕ) * (-γ * α * p))) *
                  ENNReal.ofReal ((1 / 2 : ℝ) ^ ((n : ℝ) * xi))) * base := by ac_rfl
            _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ * α * p)) *
                  (ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)) ^ n) * base := by rw [hconv]
            _ = _ := by ac_rfl
    have hseries : ∑' n : ℕ, C * q ^ n = C * (1 - q)⁻¹ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hden : 1 - q ≠ 0 := by
      intro hzero
      have hle : 1 ≤ q := tsub_eq_zero_iff_le.mp hzero
      exact (not_le_of_gt hq) hle
    have hgeom : (1 - q)⁻¹ < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden)
    have hC : C < ⊤ := by
      dsimp [C]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbaseFinite
    have hsumFinite : (∑' n : ℕ, C * q ^ n) < ⊤ := by
      rw [hseries]
      exact ENNReal.mul_lt_top hC hgeom
    have hbound : weightedGmcBallMoment P M γ α z (1 / 2) p ≤
        ∑' n : ℕ, ∫⁻ ω, (coeff n *
          M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) ^ p ∂P := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (∑' n : ℕ, coeff n *
              M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow
            (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α (1 / 2) z
              hγ hαpos (by norm_num) (by norm_num)) hp.le
        _ ≤ ∫⁻ ω, ∑' n : ℕ, (coeff n *
              M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ennreal_rpow_tsum_le_tsum_rpow _ hp hp1
        _ = _ := by
          rw [lintegral_tsum]
          intro n
          exact htermMeas n
    have hsumEq :
        (∑' n : ℕ, ∫⁻ ω, (coeff n *
          M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) ^ p ∂P) =
          ∑' n : ℕ, C * q ^ n := by
      apply tsum_congr
      intro n
      exact htermInt n
    calc
      weightedGmcBallMoment P M γ α z (1 / 2) p ≤
          ∑' n : ℕ, ∫⁻ ω, (coeff n *
            M ω (Metric.ball z ((1 / 2 : ℝ) / (2 : ℝ) ^ n))) ^ p ∂P := hbound
      _ = ∑' n : ℕ, C * q ^ n := hsumEq
      _ < ⊤ := hsumFinite


/-- Every subunit positive order below the sharp insertion range is finite on any centered-radius
disk whose closure lies in the exact logarithmic chart. -/
theorem weightedGmcBallMoment_chart_finite_subunit_all_charge
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α p : ℝ) (z : ℂ) (R : ℝ) (hR : 0 < R) (hRlt : R < 1)
    (hz : ‖z‖ + R < 1) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - α))) :
    weightedGmcBallMoment P M γ α z R p < ⊤ := by
  by_cases hα : α ≤ 0
  · have hballFinite : gmcMassMoment P M (Metric.ball z R) p < ⊤ := by
      have hbulk : p < 4 / γ ^ 2 := (lt_min_iff.mp hpRange).1
      exact (gmc_mass_moment_finite_iff_on_subunit_interval P X hX γ hγ hγ2
        M hM (Metric.ball z R) hp hp1).2 hbulk
    have hcoefPos : ENNReal.ofReal (R ^ (-γ * α)) < ⊤ := ENNReal.ofReal_lt_top
    have hcoefMom : (ENNReal.ofReal (R ^ (-γ * α))) ^ p < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg hp.le hcoefPos.ne
    have hbound : weightedGmcBallMoment P M γ α z R p ≤
        (ENNReal.ofReal (R ^ (-γ * α))) ^ p *
          gmcMassMoment P M (Metric.ball z R) p := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (ENNReal.ofReal (R ^ (-γ * α)) *
              M ω (Metric.ball z R)) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow
            (weightedGmcBallMass_le_constant_center (M ω) γ α R z hγ hα hR) hp.le
        _ = (ENNReal.ofReal (R ^ (-γ * α))) ^ p *
              gmcMassMoment P M (Metric.ball z R) p := by
          have hmeas : AEMeasurable (fun ω =>
              ENNReal.rpow (M ω (Metric.ball z R)) p) P := by
            exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
              (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
                (Metric.ball z R) Metric.isOpen_ball.measurableSet)
          calc
            _ = ∫⁻ ω, (ENNReal.ofReal (R ^ (-γ * α))) ^ p *
                  ENNReal.rpow (M ω (Metric.ball z R)) p ∂P := by
              apply lintegral_congr
              intro ω
              exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
            _ = _ := by rw [lintegral_const_mul'' _ hmeas, gmcMassMoment]
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top hcoefMom hballFinite)
  · have hαpos : 0 < α := lt_of_not_ge hα
    let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
    let eta : ℝ := xi - γ * α * p
    let base : ℝ≥0∞ := gmcMassMoment P M (Metric.ball 0 R) p
    let C : ℝ≥0∞ := ENNReal.ofReal ((R / 2) ^ (-γ * α * p)) * base
    let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)
    let coeff (n : ℕ) : ℝ≥0∞ :=
      ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)
    have hbaseFinite : base < ⊤ := by
      have hbulk : p < 4 / γ ^ 2 := (lt_min_iff.mp hpRange).1
      exact (gmc_mass_moment_finite_iff_on_subunit_interval P X hX γ hγ hγ2
        M hM (Metric.ball 0 R) hp hp1).2 hbulk
    have heta : γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2 = eta := by
      dsimp [eta, xi, Q]
      field_simp [ne_of_gt hγ]
      ring
    have hetaPos : 0 < eta := by
      rw [← heta]
      exact weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange
    have hqReal : (1 / 2 : ℝ) ^ eta < 1 :=
      Real.rpow_lt_one (by norm_num) (by norm_num) hetaPos
    have hq : q < 1 := ENNReal.ofReal_lt_one.mpr (by simpa [q] using hqReal)
    have hmassMeas (n : ℕ) : AEMeasurable
        (fun ω => M ω (Metric.ball z (R / (2 : ℝ) ^ n))) P :=
      gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
        (Metric.ball z (R / (2 : ℝ) ^ n)) Metric.isOpen_ball.measurableSet
    have hmassPowMeas (n : ℕ) : AEMeasurable
        (fun ω => ENNReal.rpow (M ω (Metric.ball z (R / (2 : ℝ) ^ n))) p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmassMeas n)
    have htermMeas (n : ℕ) : AEMeasurable
        (fun ω => (coeff n * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p) P := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        ((aemeasurable_const.mul (hmassMeas n)))
    have htermInt (n : ℕ) :
        ∫⁻ ω, (coeff n * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P = C * q ^ n := by
      have hraw : ∫⁻ ω, (coeff n *
          M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P = coeff n ^ p *
            gmcMassMoment P M (Metric.ball z (R / (2 : ℝ) ^ n)) p := by
        calc
          _ = ∫⁻ ω, coeff n ^ p *
                ENNReal.rpow (M ω (Metric.ball z (R / (2 : ℝ) ^ n))) p ∂P := by
            apply lintegral_congr
            intro ω
            exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
          _ = _ := by rw [lintegral_const_mul'' _ (hmassPowMeas n), gmcMassMoment]
      have hrad : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
      have hcoeff : coeff n ^ p = ENNReal.ofReal
          ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) := by
        calc
          _ = ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1)))
                ((-γ * α) * p) := (ENNReal.rpow_mul _ _ _).symm
          _ = ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ ((-γ * α) * p)) :=
            ennreal_ofReal_rpow_of_pos hrad
          _ = _ := by congr 1
      have hballScale := gmc_chart_dyadic_ball_moment_scale P X hX γ hγ hγ2 M hM
        z R hR hRlt hz p n
      have hscalePower : ((1 / 2 : ℝ) ^ n) ^ xi =
          (1 / 2 : ℝ) ^ ((n : ℝ) * xi) := by
        dsimp [xi]
        exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) n _).symm
      have hradDecomp : R / (2 : ℝ) ^ (n + 1) =
          (R / 2) * (1 / 2 : ℝ) ^ n := by
        rw [pow_succ, div_pow]
        field_simp
        ring
      have hreal : (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) *
          ((1 / 2 : ℝ) ^ n) ^ xi =
          (R / 2) ^ (-γ * α * p) * ((1 / 2 : ℝ) ^ eta) ^ n := by
        rw [hradDecomp, Real.mul_rpow (by positivity) (by positivity),
          (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) n
            (-γ * α * p)).symm, hscalePower]
        calc
          _ = (R / 2) ^ (-γ * α * p) *
                (1 / 2 : ℝ) ^ ((n : ℝ) * (-γ * α * p) + (n : ℝ) * xi) := by
            calc
              _ = (R / 2) ^ (-γ * α * p) *
                    ((1 / 2 : ℝ) ^ ((n : ℝ) * (-γ * α * p)) *
                      (1 / 2 : ℝ) ^ ((n : ℝ) * xi)) := by ring
              _ = _ := by
                rw [(Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _).symm]
          _ = (R / 2) ^ (-γ * α * p) * (1 / 2 : ℝ) ^ ((n : ℝ) * eta) := by
            congr 2
            dsimp [eta]
            ring
          _ = (R / 2) ^ (-γ * α * p) * ((1 / 2 : ℝ) ^ eta) ^ n := by
            rw [show (n : ℝ) * eta = eta * (n : ℝ) by ring,
              Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      have hfactor :
          ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) *
            ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ xi) =
          ENNReal.ofReal ((R / 2) ^ (-γ * α * p)) *
            (ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)) ^ n := by
        calc
          _ = ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) *
                ((1 / 2 : ℝ) ^ n) ^ xi) := by
              rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
          _ = ENNReal.ofReal ((R / 2) ^ (-γ * α * p) *
                ((1 / 2 : ℝ) ^ eta) ^ n) := by rw [hreal]
          _ = _ := by
            rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _),
              ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
      calc
        _ = coeff n ^ p *
            (ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ xi) * base) := by
              rw [hraw, hballScale]
        _ = C * q ^ n := by
          dsimp [C, q]
          rw [hcoeff]
          calc
            _ = (ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) *
                  ENNReal.ofReal (((1 / 2 : ℝ) ^ n) ^ xi)) * base := by ac_rfl
            _ = (ENNReal.ofReal ((R / 2) ^ (-γ * α * p)) *
                  (ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)) ^ n) * base := by rw [hfactor]
            _ = _ := by ac_rfl
    have hseries : ∑' n : ℕ, C * q ^ n = C * (1 - q)⁻¹ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    have hden : 1 - q ≠ 0 := by
      intro hzero
      have hle : 1 ≤ q := tsub_eq_zero_iff_le.mp hzero
      exact (not_le_of_gt hq) hle
    have hgeom : (1 - q)⁻¹ < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hden)
    have hC : C < ⊤ := by
      dsimp [C]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbaseFinite
    have hsumFinite : (∑' n : ℕ, C * q ^ n) < ⊤ := by
      rw [hseries]
      exact ENNReal.mul_lt_top hC hgeom
    have hbound : weightedGmcBallMoment P M γ α z R p ≤
        ∑' n : ℕ, ∫⁻ ω,
          (coeff n * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P := by
      rw [weightedGmcBallMoment]
      calc
        _ ≤ ∫⁻ ω, (∑' n : ℕ, coeff n *
              M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ENNReal.rpow_le_rpow
            (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α R z
              hγ hαpos hR hRlt.le) hp.le
        _ ≤ ∫⁻ ω, ∑' n : ℕ,
              (coeff n * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P := by
          apply lintegral_mono
          intro ω
          exact ennreal_rpow_tsum_le_tsum_rpow _ hp hp1
        _ = _ := by
          rw [lintegral_tsum]
          intro n
          exact htermMeas n
    have hsumEq :
        (∑' n : ℕ, ∫⁻ ω,
          (coeff n * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P) =
          ∑' n : ℕ, C * q ^ n := by
      apply tsum_congr
      intro n
      exact htermInt n
    calc
      weightedGmcBallMoment P M γ α z R p ≤
          ∑' n : ℕ, ∫⁻ ω,
            (coeff n * M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P := hbound
      _ = ∑' n : ℕ, C * q ^ n := hsumEq
      _ < ⊤ := hsumFinite

end DOZZ.Proofs
