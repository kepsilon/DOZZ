/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.WeightedDyadic
public import DOZZ.GMC.Moments.WeightedLpFiniteSum
public import DOZZ.Statements.GMC.WeightedGmcBallMoment

/-! Subunit weighted moments used by all-root construction.

This construction specialization uses the dyadic shell argument of
`SharpMoments/WeightedDyadicSum`, restricted to `0 < p ≤ 1`. It uses the existing subadditivity
lemma and avoids the higher-order Minkowski passage. The coefficient proof explicitly folds
`ENNReal.rpow` before applying the power multiplication rule.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- For `0 < p ≤ 1`, a series of nonnegative terms whose `p`th moments are dominated by a finite
geometric sequence has a finite `p`th moment. -/
private theorem rooted_subunit_shell_sum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) P) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {K q : ℝ≥0∞} (hK : K ≠ ⊤) (hq : q < 1)
    (hbound : ∀ n, ∫⁻ ω, f n ω ^ p ∂P ≤ K * q ^ n) :
    ∫⁻ ω, (∑' n, f n ω) ^ p ∂P < ⊤ := by
  have hfp : ∀ n, AEMeasurable (fun ω => f n ω ^ p) P := fun n =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hf n)
  calc
    ∫⁻ ω, (∑' n, f n ω) ^ p ∂P ≤ ∫⁻ ω, ∑' n, f n ω ^ p ∂P :=
      lintegral_mono fun ω => ennreal_rpow_tsum_le_tsum_rpow _ hp hp1
    _ = ∑' n, ∫⁻ ω, f n ω ^ p ∂P := lintegral_tsum hfp
    _ ≤ ∑' n : ℕ, K * q ^ n := ENNReal.tsum_le_tsum hbound
    _ = K * (1 - q)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top hK.lt_top (ENNReal.inv_lt_top.2 (tsub_pos_of_lt hq))

/-- The `p`th power of the dyadic coefficient is an explicit real power. -/
private theorem rooted_shell_coefficient_power (γ α p R : ℝ) (hR : 0 < R) (n : ℕ) :
    (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p =
      ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) := by
  have hrad : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
  change (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α)) ^ p = _
  rw [← ENNReal.rpow_mul, ENNReal.ofReal_rpow_of_pos hrad]

/-- The `p`th moment of the `n`th shell term is bounded by the sharp ball bound evaluated at the
dyadic radius, times the `p`th power of the coefficient. -/
private theorem rooted_shell_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) (z : ℂ) (hp : 0 < p) (hR : 0 < R) (n : ℕ)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
        M ω (Metric.ball z (R / (2 : ℝ) ^ n))) ^ p ∂P ≤
      ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) *
        (C * (R / (2 : ℝ) ^ n) ^ ξ)) := by
  have hrad : 0 < R / (2 : ℝ) ^ (n + 1) := by positivity
  have hρ : 0 < R / (2 : ℝ) ^ n := by positivity
  have hρR : R / (2 : ℝ) ^ n ≤ R := div_le_self hR.le (one_le_pow₀ (by norm_num))
  have hmeas : AEMeasurable
      (fun ω => ENNReal.rpow (M ω (Metric.ball z (R / (2 : ℝ) ^ n))) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (hM _ Metric.isOpen_ball.measurableSet)
  calc
    _ = ∫⁻ ω, (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p *
          ENNReal.rpow (M ω (Metric.ball z (R / (2 : ℝ) ^ n))) p ∂P :=
      lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp.le
    _ = (ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α)) ^ p *
          gmcMassMoment P M (Metric.ball z (R / (2 : ℝ) ^ n)) p :=
      lintegral_const_mul'' _ hmeas
    _ ≤ ENNReal.ofReal ((R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p)) *
          ENNReal.ofReal (C * (R / (2 : ℝ) ^ n) ^ ξ) := by
      rw [rooted_shell_coefficient_power γ α p R hR n]
      exact mul_le_mul' le_rfl (hball _ hρ hρR)
    _ = _ := (ENNReal.ofReal_mul (Real.rpow_nonneg hrad.le _)).symm

/-- Real-variable identity: the dyadic coefficient times the sharp bound at the dyadic radius is a
constant times the `n`th power of `(1/2) ^ (ξ - γ α p)`. -/
private theorem rooted_shell_geometric_factor (γ α p ξ C R : ℝ) (hR : 0 < R) (n : ℕ) :
    (R / (2 : ℝ) ^ (n + 1)) ^ (-γ * α * p) * (C * (R / (2 : ℝ) ^ n) ^ ξ) =
      (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ((1 / 2 : ℝ) ^ (ξ - γ * α * p)) ^ n := by
  have hhalf : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
    rw [div_pow, one_pow, one_div]
  have hpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have h1 : R / (2 : ℝ) ^ (n + 1) = (R / 2) * (1 / 2 : ℝ) ^ n := by
    rw [pow_succ, hhalf]
    field_simp
  have h2 : R / (2 : ℝ) ^ n = R * (1 / 2 : ℝ) ^ n := by
    rw [hhalf, div_eq_mul_inv]
  have hmerge : ((1 / 2 : ℝ) ^ n) ^ (-γ * α * p) * ((1 / 2 : ℝ) ^ n) ^ ξ =
      ((1 / 2 : ℝ) ^ (ξ - γ * α * p)) ^ n := by
    rw [← Real.rpow_add hpos, Real.rpow_pow_comm (by norm_num)]
    congr 1
    ring
  rw [h1, h2, Real.mul_rpow (by positivity) hpos.le, Real.mul_rpow hR.le hpos.le]
  calc
    _ = C * (R / 2) ^ (-γ * α * p) * R ^ ξ *
          (((1 / 2 : ℝ) ^ n) ^ (-γ * α * p) * ((1 / 2 : ℝ) ^ n) ^ ξ) := by ring
    _ = _ := by rw [hmerge]

/-- Sharp ball upper bounds with positive insertion exponent give a finite subunit weighted moment. -/
theorem rooted_local_moment_of_ball_upper
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : Ω → Measure ℂ)
    (hM : ∀ s : Set ℂ, MeasurableSet s → AEMeasurable (fun ω => M ω s) P)
    (γ α p ξ C R : ℝ) (z : ℂ) (hγ : 0 < γ) (hα : 0 < α) (hp : 0 < p) (hR : 0 < R)
    (hp1 : p ≤ 1) (hR1 : R ≤ 1) (he : 0 < ξ - γ * α * p)
    (hball : ∀ ρ : ℝ, 0 < ρ → ρ ≤ R →
      gmcMassMoment P M (Metric.ball z ρ) p ≤ ENNReal.ofReal (C * ρ ^ ξ)) :
    weightedGmcBallMoment P M γ α z R p < ⊤ := by
  let qReal : ℝ := (1 / 2 : ℝ) ^ (ξ - γ * α * p)
  let shell : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.rpow (ENNReal.ofReal (R / (2 : ℝ) ^ (n + 1))) (-γ * α) *
      M ω (Metric.ball z (R / (2 : ℝ) ^ n))
  have hqNonneg : 0 ≤ qReal := Real.rpow_nonneg (by norm_num) _
  have hqLt : qReal < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) he
  have hshellMeas (n : ℕ) : AEMeasurable (shell n) P :=
    aemeasurable_const.mul (hM _ Metric.isOpen_ball.measurableSet)
  have hshellBound (n : ℕ) : ∫⁻ ω, shell n ω ^ p ∂P ≤
      ENNReal.ofReal (C * (R / 2) ^ (-γ * α * p) * R ^ ξ) * ENNReal.ofReal qReal ^ n := by
    refine (rooted_shell_moment_bound P M hM γ α p ξ C R z hp hR n hball).trans ?_
    rw [rooted_shell_geometric_factor γ α p ξ C R hR n, ENNReal.ofReal_mul' (pow_nonneg hqNonneg n),
      ENNReal.ofReal_pow hqNonneg]
  have hsum : ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P < ⊤ :=
    rooted_subunit_shell_sum shell hshellMeas hp hp1 ENNReal.ofReal_ne_top
      (ENNReal.ofReal_lt_one.2 hqLt) hshellBound
  calc
    weightedGmcBallMoment P M γ α z R p
        ≤ ∫⁻ ω, (∑' n, shell n ω) ^ p ∂P :=
      lintegral_mono fun ω => ENNReal.rpow_le_rpow
        (weightedGmcBallMass_le_dyadic_charge_center (M ω) γ α R z hγ hα hR hR1) hp.le
    _ < ⊤ := hsum

end DOZZ.Proofs
