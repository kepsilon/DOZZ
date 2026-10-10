/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Local weighted-mass estimates at translated roots inside the logarithmic chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Dyadic majorant term for a root translated to `z`. -/
noncomputable def dyadicWeightedBallTermAt (μ : Measure ℂ) (γ : ℝ) (z : ℂ)
    (R : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ ^ 2) *
    μ (Metric.ball z (R / (2 : ℝ) ^ n))

/-- A negative-power insertion on a ball about any center is dominated by its dyadic ball masses.
The singular value at the center is covered by the divergent sum of all dyadic indicators. -/
theorem weightedGmcBallMass_center_le_dyadic
    (μ : Measure ℂ) (γ : ℝ) (z : ℂ) (R : ℝ)
    (hγ : 0 < γ) (hR : 0 < R) (hR1 : R ≤ 1) :
    weightedGmcBallMass γ μ γ z R ≤
      ∑' n : ℕ, dyadicWeightedBallTermAt μ γ z R n := by
  let τ : ℂ → ℂ := fun x => x - z
  have hτ : MeasurableEmbedding τ := by
    simpa [τ, sub_eq_add_neg] using
      (MeasurableEquiv.addRight (-z) : ℂ ≃ᵐ ℂ).measurableEmbedding
  have hball : τ ⁻¹' Metric.ball 0 R = Metric.ball z R := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    rw [show ‖τ x‖ = dist x z by simp [τ, dist_eq_norm]]
  have hmass : weightedGmcBallMass γ μ γ z R =
      weightedGmcBallMass γ (μ.map τ) γ 0 R := by
    symm
    rw [weightedGmcBallMass, weightedGmcBallMass]
    change ∫⁻ x, ENNReal.rpow (ENNReal.ofReal ‖x - 0‖) (-γ * γ) ∂
      (μ.map τ).restrict (Metric.ball 0 R) = _
    rw [hτ.restrict_map μ (Metric.ball 0 R)]
    rw [hτ.lintegral_map]
    simp [hball, τ]
  calc
    weightedGmcBallMass γ μ γ z R =
        weightedGmcBallMass γ (μ.map τ) γ 0 R := hmass
    _ ≤ ∑' n : ℕ, dyadicWeightedBallTerm (μ.map τ) γ R n :=
      weightedGmcBallMass_root_le_dyadic (μ.map τ) γ R hγ hR hR1
    _ = ∑' n : ℕ, dyadicWeightedBallTermAt μ γ z R n := by
      apply tsum_congr
      intro n
      rw [dyadicWeightedBallTerm, dyadicWeightedBallTermAt]
      congr 1
      rw [Measure.map_apply hτ.measurable Metric.isOpen_ball.measurableSet]
      congr 1
      ext x
      simp [τ, Metric.mem_ball, dist_eq_norm]

private theorem chart_half_power_div_two_pow (N k : ℕ) :
    ((1 / 2 : ℝ) ^ (N + 1)) / (2 : ℝ) ^ k =
      (1 / 2 : ℝ) ^ (N + k + 1) := by
  rw [div_eq_mul_inv]
  have hinv : ((2 : ℝ) ^ k)⁻¹ = (1 / 2 : ℝ) ^ k := by
    rw [← inv_pow]
    norm_num
  rw [hinv, ← pow_add]
  congr 1
  omega

private theorem chart_gmc_dyadic_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (N n : ℕ) (hz : ‖z‖ + (1 / 2 : ℝ) ^ (N + 1) < 1) (p : ℝ) :
    gmcMassMoment P M
      (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1))) p =
      ENNReal.ofReal (((1 / 2 : ℝ) ^ (N + n)) ^
        (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        gmcMassMoment P M (Metric.ball 0 (1 / 2)) p := by
  let c : ℝ := (1 / 2 : ℝ) ^ (N + n)
  have hc : 0 < c := by positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hcn : c ≤ (1 / 2 : ℝ) ^ N := by
    dsimp [c]
    rw [pow_add]
    calc
      (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ n ≤
          (1 / 2 : ℝ) ^ N * 1 := by
        exact mul_le_mul_of_nonneg_left
          (show (1 / 2 : ℝ) ^ n ≤ 1 by exact pow_le_one₀ (by norm_num) (by norm_num))
          (pow_nonneg (by norm_num) _)
      _ = (1 / 2 : ℝ) ^ N := by simp
  have hsmall : ‖z‖ + c * (1 / 2 : ℝ) < 1 := by
    have hmul := mul_le_mul_of_nonneg_right hcn (by norm_num : (0 : ℝ) ≤ 1 / 2)
    calc
      ‖z‖ + c * (1 / 2 : ℝ) ≤ ‖z‖ + (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) := by linarith
      _ = ‖z‖ + (1 / 2 : ℝ) ^ (N + 1) := by rw [pow_succ]
      _ < 1 := hz
  have hscale := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (a := z) (c := c) (R := (1 / 2 : ℝ)) hc hc1 (by norm_num) (by norm_num)
    hsmall p
  have hrad : c * (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (N + n + 1) := by
    dsimp [c]
    rw [pow_succ]
  rw [hrad] at hscale
  exact hscale

private theorem chart_ennreal_ofReal_rpow_of_pos {x p : ℝ} (hx : 0 < x) :
    ENNReal.rpow (ENNReal.ofReal x) p = ENNReal.ofReal (x ^ p) := by
  have hx0 : ENNReal.ofReal x ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hx)
  have hleft : ENNReal.rpow (ENNReal.ofReal x) p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hx0 ENNReal.ofReal_ne_top
  have hright : ENNReal.ofReal (x ^ p) ≠ ⊤ := ENNReal.ofReal_ne_top
  apply (ENNReal.toReal_eq_toReal_iff' hleft hright).1
  calc
    (ENNReal.rpow (ENNReal.ofReal x) p).toReal = (ENNReal.ofReal x).toReal ^ p :=
      (ENNReal.toReal_rpow _ _).symm
    _ = x ^ p := by rw [ENNReal.toReal_ofReal hx.le]
    _ = (ENNReal.ofReal (x ^ p)).toReal :=
      (ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le p)).symm

private theorem ennreal_half_power_mul_rpow {m : ℕ} {a : ℝ} (p : ℝ) :
    (ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) a) ^ p =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (m * (a * p))) := by
  have hrad : 0 < (1 / 2 : ℝ) ^ m := by positivity
  rw [show (ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) a) ^ p =
      ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) ^ m)) (a * p) by
        exact (ENNReal.rpow_mul _ _ _).symm]
  rw [chart_ennreal_ofReal_rpow_of_pos hrad]
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) m (a * p)]

/-- At every point strictly inside the logarithmic chart, the singular insertion has a finite
positive moment on a sufficiently small dyadic ball. The proof translates the dyadic mass
majorant and scales each ball from the centered half-ball. -/
private theorem weightedGmcBallMoment_chart_finite_dyadic_aux
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (N : ℕ) (hz : ‖z‖ + (1 / 2 : ℝ) ^ (N + 1) < 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - γ))) :
    weightedGmcBallMoment P M γ γ z ((1 / 2 : ℝ) ^ (N + 1)) p < ⊤ ∧
      ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) γ z ((1 / 2 : ℝ) ^ (N + 1)) < ⊤ := by
  classical
  let xi : ℝ := 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let eta : ℝ := 2 * p - γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2
  let q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ eta)
  let base : ℝ≥0∞ := gmcMassMoment P M (Metric.ball 0 (1 / 2)) p
  let C : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p)) * q ^ N * base
  let coeff (n : ℕ) : ℝ≥0∞ :=
    ENNReal.rpow (ENNReal.ofReal ((1 / 2 : ℝ) ^ (N + n + 2))) (-γ ^ 2)
  let term (ω : Ω) (n : ℕ) : ℝ≥0∞ :=
    coeff n * M ω (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1)))
  have hbaseFinite : base < ⊤ := by
    have hbulk : p < 4 / γ ^ 2 := by
      have hγsq : γ ^ 2 < 4 := by nlinarith
      have hthreshold : 1 < 4 / γ ^ 2 := by
        rw [one_lt_div (sq_pos_of_pos hγ)]
        nlinarith
      exact hp1.trans_lt hthreshold
    exact (gmc_mass_moment_finite_iff_on_subunit_interval P X hX γ hγ hγ2
      M hM (Metric.ball 0 (1 / 2)) hp hp1).2 hbulk
  have hslack := weightedGmcMomentExponent_pos_of_sharp_range hγ hp hpRange
  have heta : γ * (Q γ - γ) * p - γ ^ 2 * p ^ 2 / 2 = eta := by
    dsimp [eta, Q]
    field_simp [ne_of_gt hγ]
    ring
  have hetaPos : 0 < eta := by rw [← heta]; exact hslack
  have hqReal : (1 / 2 : ℝ) ^ eta < 1 :=
    Real.rpow_lt_one (by norm_num) (by norm_num) hetaPos
  have hq : q < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (by simpa [q] using hqReal)
  have htermEq (ω : Ω) (n : ℕ) :
      dyadicWeightedBallTermAt (M ω) γ z ((1 / 2 : ℝ) ^ (N + 1)) n = term ω n := by
    dsimp [dyadicWeightedBallTermAt, term, coeff]
    rw [chart_half_power_div_two_pow N (n + 1), chart_half_power_div_two_pow N n]
    rw [show N + (n + 1) + 1 = N + n + 2 by omega]
  have hmassMeas (n : ℕ) : AEMeasurable
      (fun ω => M ω (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1)))) P :=
    gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
      (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1))) Metric.isOpen_ball.measurableSet
  have hmassPowMeas (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.rpow
        (M ω (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1)))) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hmassMeas n)
  have htermMeas (n : ℕ) : AEMeasurable (fun ω => term ω n ^ p) P := by
    have hmul : AEMeasurable (fun ω => coeff n *
        M ω (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1)))) P :=
      aemeasurable_const.mul (hmassMeas n)
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmul
  have htermInt (n : ℕ) :
      ∫⁻ ω, term ω n ^ p ∂P = C * q ^ n := by
    have hraw :
        ∫⁻ ω, term ω n ^ p ∂P = coeff n ^ p *
          gmcMassMoment P M (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1))) p := by
      calc
        _ = ∫⁻ ω, coeff n ^ p * ENNReal.rpow
              (M ω (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1)))) p ∂P := by
          apply lintegral_congr
          intro ω
          exact ENNReal.mul_rpow_of_nonneg _ _ hp.le
        _ = coeff n ^ p * ∫⁻ ω, ENNReal.rpow
              (M ω (Metric.ball z ((1 / 2 : ℝ) ^ (N + n + 1)))) p ∂P :=
          lintegral_const_mul'' _ (hmassPowMeas n)
        _ = _ := rfl
    have hcoeff : coeff n ^ p = ENNReal.ofReal
        ((1 / 2 : ℝ) ^ ((N + n + 2 : ℕ) * (-γ ^ 2 * p))) := by
      simpa [coeff] using
        (ennreal_half_power_mul_rpow (m := N + n + 2) (a := -γ ^ 2) p)
    have hballScale := chart_gmc_dyadic_ball_moment_scale P X hX γ hγ hγ2 M hM
      z N n hz p
    have hscalePower : ((1 / 2 : ℝ) ^ (N + n)) ^ xi =
        (1 / 2 : ℝ) ^ ((N + n : ℕ) * xi) := by
      dsimp [xi]
      exact (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 1 / 2) (N + n) _).symm
    have hreal :
        (1 / 2 : ℝ) ^ ((N + n + 2 : ℕ) * (-γ ^ 2 * p)) *
            (1 / 2 : ℝ) ^ ((N + n : ℕ) * xi) =
          (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
            ((1 / 2 : ℝ) ^ eta) ^ N * ((1 / 2 : ℝ) ^ eta) ^ n := by
      calc
        _ = (1 / 2 : ℝ) ^ (((N + n + 2 : ℕ) : ℝ) * (-γ ^ 2 * p) +
              ((N + n : ℕ) : ℝ) * xi) :=
          (Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _).symm
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p + ((N + n : ℕ) : ℝ) * eta) := by
          congr 1
          dsimp [xi, eta]
          push_cast
          ring
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
              (1 / 2 : ℝ) ^ (((N + n : ℕ) : ℝ) * eta) :=
          Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
              ((1 / 2 : ℝ) ^ eta) ^ (N + n) := by
          congr 1
          rw [show ((N + n : ℕ) : ℝ) * eta = eta * ((N + n : ℕ) : ℝ) by ring,
            Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ = (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
              ((1 / 2 : ℝ) ^ eta) ^ N * ((1 / 2 : ℝ) ^ eta) ^ n := by
          rw [pow_add]
          ring
    have hconv :
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((N + n + 2 : ℕ) * (-γ ^ 2 * p))) *
            ENNReal.ofReal (((1 / 2 : ℝ) ^ (N + n)) ^ xi) =
          ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p)) * q ^ N * q ^ n := by
      rw [hscalePower]
      have hcoefNonneg : 0 ≤ (1 / 2 : ℝ) ^ ((N + n + 2 : ℕ) * (-γ ^ 2 * p)) :=
        Real.rpow_nonneg (by norm_num) _
      calc
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ ((N + n + 2 : ℕ) * (-γ ^ 2 * p)) *
              (1 / 2 : ℝ) ^ ((N + n : ℕ) * xi)) := by
          rw [ENNReal.ofReal_mul hcoefNonneg]
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
              ((1 / 2 : ℝ) ^ eta) ^ N * ((1 / 2 : ℝ) ^ eta) ^ n) := by rw [hreal]
        _ = _ := by
          dsimp [q]
          rw [show ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
              ((1 / 2 : ℝ) ^ eta) ^ N * ((1 / 2 : ℝ) ^ eta) ^ n) =
              (1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p) *
                (((1 / 2 : ℝ) ^ eta) ^ N * ((1 / 2 : ℝ) ^ eta) ^ n) by ring]
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
            ENNReal.ofReal_mul (pow_nonneg (Real.rpow_nonneg (by norm_num) _) N),
            ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) N,
            ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _) n]
          ac_rfl
    calc
      _ = coeff n ^ p *
          (ENNReal.ofReal (((1 / 2 : ℝ) ^ (N + n)) ^ xi) * base) := by
            rw [hraw, hballScale]
      _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ ((N + n + 2 : ℕ) * (-γ ^ 2 * p))) *
          ENNReal.ofReal (((1 / 2 : ℝ) ^ (N + n)) ^ xi)) * base := by
            rw [hcoeff]
            ac_rfl
      _ = (ENNReal.ofReal ((1 / 2 : ℝ) ^ (-2 * γ ^ 2 * p)) * q ^ N * q ^ n) * base := by
            rw [hconv]
      _ = C * q ^ n := by dsimp [C]; ac_rfl
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
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (lt_trans hq ENNReal.one_lt_top))) hbaseFinite
  have hsumFinite : (∑' n : ℕ, C * q ^ n) < ⊤ := by
    rw [hseries]
    exact ENNReal.mul_lt_top hC hgeom
  have hmoment : weightedGmcBallMoment P M γ γ z ((1 / 2 : ℝ) ^ (N + 1)) p < ⊤ := by
    calc
      weightedGmcBallMoment P M γ γ z ((1 / 2 : ℝ) ^ (N + 1)) p ≤
        ∑' n : ℕ, ∫⁻ ω, term ω n ^ p ∂P := by
        rw [weightedGmcBallMoment]
        calc
          _ ≤ ∫⁻ ω, (∑' n : ℕ, term ω n) ^ p ∂P := by
            apply lintegral_mono
            intro ω
            have hcover := weightedGmcBallMass_center_le_dyadic (M ω) γ z
              ((1 / 2 : ℝ) ^ (N + 1)) hγ (by positivity)
              (pow_le_one₀ (by norm_num) (by norm_num))
            have hseriesω :
                (∑' n : ℕ, dyadicWeightedBallTermAt (M ω) γ z
                  ((1 / 2 : ℝ) ^ (N + 1)) n) = ∑' n : ℕ, term ω n := by
              exact tsum_congr fun n => htermEq ω n
            exact ENNReal.rpow_le_rpow (hcover.trans_eq hseriesω) hp.le
          _ ≤ ∫⁻ ω, ∑' n : ℕ, term ω n ^ p ∂P := by
            apply lintegral_mono
            intro ω
            exact ennreal_rpow_tsum_le_tsum_rpow (fun n => term ω n) hp hp1
          _ = ∑' n : ℕ, ∫⁻ ω, term ω n ^ p ∂P := by
            rw [lintegral_tsum htermMeas]
      _ = ∑' n : ℕ, C * q ^ n := by
        apply tsum_congr
        exact htermInt
      _ < ⊤ := hsumFinite
  have hseriesPowInt : ∫⁻ ω, ∑' n : ℕ, term ω n ^ p ∂P < ⊤ := by
    rw [lintegral_tsum htermMeas]
    calc
      _ = ∑' n : ℕ, C * q ^ n := by
        apply tsum_congr
        exact htermInt
      _ < ⊤ := hsumFinite
  have haeSeries : ∀ᵐ ω ∂P, (∑' n : ℕ, term ω n ^ p) < ⊤ :=
    ae_lt_top' (AEMeasurable.tsum htermMeas) hseriesPowInt.ne
  have haeMass : ∀ᵐ ω ∂P,
      weightedGmcBallMass γ (M ω) γ z ((1 / 2 : ℝ) ^ (N + 1)) < ⊤ := by
    filter_upwards [haeSeries] with ω hω
    have hsumPow : (∑' n : ℕ, term ω n) ^ p < ⊤ := by
      exact lt_of_le_of_lt (ennreal_rpow_tsum_le_tsum_rpow (fun n => term ω n) hp hp1) hω
    have hsum : (∑' n : ℕ, term ω n) < ⊤ := by
      by_contra hnot
      have htop : (∑' n : ℕ, term ω n) = ⊤ := top_unique (not_lt.mp hnot)
      rw [htop, ENNReal.top_rpow_of_pos hp] at hsumPow
      exact (lt_self_iff_false _).mp hsumPow
    have hcover := weightedGmcBallMass_center_le_dyadic (M ω) γ z
      ((1 / 2 : ℝ) ^ (N + 1)) hγ (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    have hseriesω :
        (∑' n : ℕ, dyadicWeightedBallTermAt (M ω) γ z
          ((1 / 2 : ℝ) ^ (N + 1)) n) = ∑' n : ℕ, term ω n :=
      tsum_congr fun n => htermEq ω n
    exact lt_of_le_of_lt (hcover.trans_eq hseriesω) hsum
  exact ⟨hmoment, haeMass⟩


/-- The local weighted mass is almost surely finite whenever the center's dyadic half-ball stays
inside the logarithmic chart. -/
theorem ae_weightedGmcBallMass_chart_finite_dyadic
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (N : ℕ) (hz : ‖z‖ + (1 / 2 : ℝ) ^ (N + 1) < 1)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpRange : p < min (4 / γ ^ 2) (2 / γ * (Q γ - γ))) :
    ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) γ z ((1 / 2 : ℝ) ^ (N + 1)) < ⊤ :=
  (weightedGmcBallMoment_chart_finite_dyadic_aux P X hX γ hγ hγ2 M hM z N hz p hp hp1
    hpRange).2

/-- Every point of the open unit chart has a dyadic neighborhood on which the rooted weighted GMC
mass is almost surely finite, using the weighted-moment bound
`exists_finite_weightedGmcBallMoment_at_gamma` at the origin. -/
theorem exists_ae_finite_weightedGmcBallMass_of_inside_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : ℂ) (hz : ‖z‖ < 1) :
    ∃ N : ℕ, ‖z‖ + (1 / 2 : ℝ) ^ (N + 1) < 1 ∧
      ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) γ z ((1 / 2 : ℝ) ^ (N + 1)) < ⊤ := by
  obtain ⟨p, hp, hp1, hpRange, _⟩ :=
    exists_finite_weightedGmcBallMoment_at_gamma P X hX γ hγ hγ2 M hM
  have hgap : 0 < 1 - ‖z‖ := by linarith
  let d : ℝ := (1 - ‖z‖) / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hd1 : d < 1 := by
    dsimp [d]
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg _
    linarith
  obtain ⟨N, hNlo, _⟩ := exists_dyadic_shell_index hd hd1
  have hhalf : (1 / 2 : ℝ) ^ (N + 1) = 1 / (2 : ℝ) ^ (N + 1) := by
    rw [div_pow]
    norm_num
  have hsmall : (1 / 2 : ℝ) ^ (N + 1) < 1 - ‖z‖ := by
    calc
      (1 / 2 : ℝ) ^ (N + 1) = 1 / (2 : ℝ) ^ (N + 1) := hhalf
      _ ≤ d := hNlo
      _ < 1 - ‖z‖ := by dsimp [d]; linarith
  refine ⟨N, ?_, ?_⟩
  · linarith
  · exact ae_weightedGmcBallMass_chart_finite_dyadic P X hX γ hγ hγ2 M hM z N
      (by linarith) p hp hp1 hpRange

private theorem gmcRooted_density_le_local_insert_plus_const
    (γ : ℝ) (hγ : 0 < γ) (u : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : ‖u‖ + r < 1) (x : ℂ) :
    ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) ≤
      (Metric.ball u r).indicator
        (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x +
      ENNReal.ofReal
        ((normPlus u * (1 + (1 + ‖u‖) / r)) ^ (γ ^ 2)) := by
  let K : ℝ := normPlus u * (1 + (1 + ‖u‖) / r)
  have huPlus : 0 < normPlus u := by
    unfold normPlus
    positivity
  have huNorm : ‖u‖ < 1 := by linarith
  have huPlusOne : normPlus u = 1 := by
    unfold normPlus
    exact max_eq_left huNorm.le
  have hK : 0 < K := by
    dsimp [K]
    positivity
  by_cases hxBall : x ∈ Metric.ball u r
  · have hxNorm : ‖x‖ < 1 := by
      have hdist : dist x u < r := by simpa [Metric.mem_ball] using hxBall
      have htriangle : ‖x‖ ≤ ‖u‖ + dist x u := by
        calc
          ‖x‖ = ‖(x - u) + u‖ := by congr 1; abel
          _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
          _ = ‖u‖ + dist x u := by rw [dist_eq_norm]; ring
      linarith
    have hxPlusOne : normPlus x = 1 := by
      unfold normPlus
      exact max_eq_left hxNorm.le
    by_cases hxu : x = u
    · subst x
      have hball : u ∈ Metric.ball u r := by simp [Metric.mem_ball, hr]
      rw [Set.indicator_of_mem hball]
      simp [ENNReal.zero_rpow_of_neg, show -γ ^ 2 < 0 by nlinarith]
    · have hdistPos : 0 < ‖x - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu)
      have hkernel : gffKernel u x = -Real.log ‖x - u‖ := by
        rw [gffKernel, huPlusOne, hxPlusOne, Real.log_one]
        rw [show ‖u - x‖ = ‖x - u‖ by simp [norm_sub_rev]]
        ring
      have hexp : Real.exp (γ ^ 2 * gffKernel u x) =
          ‖x - u‖ ^ (-γ ^ 2) := by
        rw [hkernel, Real.rpow_def_of_pos hdistPos]
        congr 1
        ring
      rw [Set.indicator_of_mem hxBall]
      calc
        ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) =
            ENNReal.rpow (ENNReal.ofReal ‖x - u‖) (-γ ^ 2) := by
          rw [hexp, chart_ennreal_ofReal_rpow_of_pos hdistPos]
        _ ≤ ENNReal.rpow (ENNReal.ofReal ‖x - u‖) (-γ ^ 2) +
            ENNReal.ofReal (K ^ (γ ^ 2)) := le_add_of_nonneg_right (by positivity)
  · have hdist : r ≤ ‖x - u‖ := by
      have hnot : ¬ dist x u < r := by simpa [Metric.mem_ball] using hxBall
      exact le_of_not_gt (by simpa [dist_eq_norm] using hnot)
    have hnormX : ‖x‖ ≤ ‖u‖ + ‖x - u‖ := by
      calc
        ‖x‖ = ‖(x - u) + u‖ := by congr 1; abel
        _ ≤ ‖x - u‖ + ‖u‖ := norm_add_le _ _
        _ = ‖u‖ + ‖x - u‖ := by ring
    have hplusX : normPlus x ≤ 1 + ‖u‖ + ‖x - u‖ := by
      unfold normPlus
      apply max_le
      · linarith [norm_nonneg u, norm_nonneg (x - u)]
      · linarith [norm_nonneg u, norm_nonneg (x - u), hnormX]
    have hratioOne : 1 ≤ ‖x - u‖ / r := (one_le_div hr).2 hdist
    have hfactor : 1 + ‖u‖ ≤ (‖x - u‖ / r) * (1 + ‖u‖) := by
      calc
        1 + ‖u‖ = 1 * (1 + ‖u‖) := by ring
        _ ≤ (‖x - u‖ / r) * (1 + ‖u‖) :=
          mul_le_mul_of_nonneg_right hratioOne (by positivity)
    have hplusBound : normPlus x ≤ ‖x - u‖ * (1 + (1 + ‖u‖) / r) := by
      calc
        normPlus x ≤ 1 + ‖u‖ + ‖x - u‖ := hplusX
        _ ≤ ‖x - u‖ + (‖x - u‖ / r) * (1 + ‖u‖) := by linarith
        _ = ‖x - u‖ * (1 + (1 + ‖u‖) / r) := by ring
    have hratio : normPlus u * normPlus x / ‖x - u‖ ≤ K := by
      have hdistPos : 0 < ‖x - u‖ := lt_of_lt_of_le hr hdist
      apply (div_le_iff₀ hdistPos).2
      calc
        normPlus u * normPlus x ≤
            normPlus u * (‖x - u‖ * (1 + (1 + ‖u‖) / r)) :=
          mul_le_mul_of_nonneg_left hplusBound huPlus.le
        _ = K * ‖x - u‖ := by dsimp [K]; ring
    have hdistPos : 0 < ‖x - u‖ := lt_of_lt_of_le hr hdist
    have hratioPos : 0 < normPlus u * normPlus x / ‖x - u‖ :=
      div_pos (mul_pos huPlus (by unfold normPlus; positivity)) hdistPos
    have hkernel : gffKernel u x =
        Real.log (normPlus u * normPlus x / ‖x - u‖) := by
      have hu0 : normPlus u ≠ 0 := huPlus.ne'
      have hx0 : normPlus x ≠ 0 := by
        unfold normPlus
        positivity
      have hd0 : ‖x - u‖ ≠ 0 := hdistPos.ne'
      rw [gffKernel, show ‖u - x‖ = ‖x - u‖ by simp [norm_sub_rev]]
      calc
        -Real.log ‖x - u‖ + Real.log (normPlus u) + Real.log (normPlus x) =
            Real.log (normPlus u) + Real.log (normPlus x) - Real.log ‖x - u‖ := by ring
        _ = Real.log (normPlus u * normPlus x) - Real.log ‖x - u‖ := by
          rw [← Real.log_mul hu0 hx0]
        _ = Real.log (normPlus u * normPlus x / ‖x - u‖) :=
          (Real.log_div (mul_ne_zero hu0 hx0) hd0).symm
    have hlog : Real.log (normPlus u * normPlus x / ‖x - u‖) ≤ Real.log K :=
      Real.log_le_log hratioPos hratio
    have hkernelBound : gffKernel u x ≤ Real.log K := by rw [hkernel]; exact hlog
    have hexpBound : Real.exp (γ ^ 2 * gffKernel u x) ≤ K ^ (γ ^ 2) := by
      calc
        Real.exp (γ ^ 2 * gffKernel u x) ≤ Real.exp (γ ^ 2 * Real.log K) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hkernelBound (sq_nonneg γ))
        _ = K ^ (γ ^ 2) := by
          rw [show γ ^ 2 * Real.log K = Real.log K * γ ^ 2 by ring,
            ← Real.rpow_def_of_pos hK]
    simpa [hxBall] using ENNReal.ofReal_le_ofReal hexpBound

/-- A local weighted-mass bound controls the singular part of the rooted density; away from the
root, the spherical kernel density is bounded by a deterministic constant. -/
theorem isFiniteMeasure_gmcRooted_of_local_weighted_mass
    (γ : ℝ) (hγ : 0 < γ) (u : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : ‖u‖ + r < 1) (μ : Measure ℂ) (hμ : IsFiniteMeasure μ)
    (hlocal : weightedGmcBallMass γ μ γ u r < ⊤) :
    IsFiniteMeasure (gmcRootedMeasure γ u μ) := by
  have hinsertionBase : Measurable (fun x : ℂ => ENNReal.ofReal ‖x - u‖) := by
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hinsertion : Measurable (fun x : ℂ =>
      ENNReal.rpow (ENNReal.ofReal ‖x - u‖) (-γ ^ 2)) :=
    ENNReal.continuous_rpow_const.measurable.comp hinsertionBase
  have hinsertionLocal : Measurable (fun x : ℂ =>
      (Metric.ball u r).indicator
        (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x) :=
    hinsertion.indicator Metric.isOpen_ball.measurableSet
  let C : ℝ≥0∞ := ENNReal.ofReal
    ((normPlus u * (1 + (1 + ‖u‖) / r)) ^ (γ ^ 2))
  have htotalBound :
      ∫⁻ x, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) ∂μ ≤
        weightedGmcBallMass γ μ γ u r + C * μ Set.univ := by
    calc
      _ ≤ ∫⁻ x, (Metric.ball u r).indicator
              (fun y => ENNReal.rpow (ENNReal.ofReal ‖y - u‖) (-γ ^ 2)) x + C ∂μ :=
        lintegral_mono fun x => by
          simpa [C] using gmcRooted_density_le_local_insert_plus_const γ hγ u r hr hu x
      _ = weightedGmcBallMass γ μ γ u r + C * μ Set.univ := by
        rw [lintegral_add_left hinsertionLocal, lintegral_indicator
          Metric.isOpen_ball.measurableSet, lintegral_const, weightedGmcBallMass]
        congr 1
        apply lintegral_congr
        intro x
        rw [show -γ ^ 2 = -γ * γ by ring]
  have hconstant : C * μ Set.univ < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ.measure_univ_lt_top
  have htotalFinite :
      (∫⁻ x, ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)) ∂μ) < ⊤ :=
    lt_of_le_of_lt htotalBound (ENNReal.add_lt_top.mpr ⟨hlocal, hconstant⟩)
  rw [gmcRootedMeasure]
  exact isFiniteMeasure_withDensity htotalFinite.ne


end DOZZ.Proofs
