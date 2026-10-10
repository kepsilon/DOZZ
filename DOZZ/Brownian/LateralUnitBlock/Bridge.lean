/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.LateralUnitBlockMass
public import DOZZ.Brownian.Barrier.GaussianTilting
public import DOZZ.Brownian.Lateral.BrownianWindowExponential

/-!
# The unit Brownian bridge used in the conditional unit-block estimate

The literal capped bridge is independent of its terminal value. Its absolute window norm
is bounded by twice the Brownian window norm, which gives every exponential moment.
These bounds retain endpoint conditioning rather than replacing it by an unconditional
inverse-moment estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Nonnegative-time evaluation agrees with the original path evaluation. -/
theorem lateralUnitBlock_brownianPathValue_nnreal {Ω : Type*} (B : Ω → BrownianPath)
    (ω : Ω) (t : ℝ≥0) : brownianPathValue B ω (t : ℝ) = B ω t := by
  rw [brownianPathValue, dite_eq_left t.coe_nonneg]
  congr 1

/-- A path evaluation in the unit window is bounded by its compact-window norm. -/
theorem lateralUnitBlock_abs_eval_le_unitNorm (p : BrownianPath) (t : ℝ≥0) (ht : t ≤ 1) :
    |p t| ≤ brownianUnitNorm p := by
  exact (p.restrict (Icc 0 (1 : ℝ≥0))).norm_coe_le_norm ⟨t, bot_le, ht⟩

/-- On the unit window the capped bridge has the usual linear regression formula. -/
theorem lateralUnitBlock_bridge_eval (p : BrownianPath) (t : ℝ≥0) (ht : t ≤ 1) :
    brownianBridgePath 1 p t = p t - (t : ℝ) * p 1 := by
  change p (min t 1) - ((min t 1 : ℝ≥0) : ℝ) / (1 : ℝ) * p 1 = _
  rw [min_eq_left ht, div_one]

/-- The absolute unit-bridge norm is at most twice the Brownian norm, pathwise. -/
theorem lateralUnitBlock_bridge_unitNorm_le (p : BrownianPath) :
    brownianUnitNorm (brownianBridgePath 1 p) ≤ 2 * brownianUnitNorm p := by
  change ‖(brownianBridgePath 1 p).restrict (Icc 0 (1 : ℝ≥0))‖ ≤ _
  apply (ContinuousMap.norm_le _ (mul_nonneg (by norm_num) (brownianUnitNorm_nonneg p))).mpr
  intro t
  change |brownianBridgePath 1 p t.1| ≤ _
  rw [lateralUnitBlock_bridge_eval p t.1 t.2.2]
  have hterminal := lateralUnitBlock_abs_eval_le_unitNorm p 1 le_rfl
  have htime : (t.1 : ℝ) ≤ 1 := by exact_mod_cast t.2.2
  calc
    |p t.1 - (t.1 : ℝ) * p 1| ≤ |p t.1| + |(t.1 : ℝ) * p 1| := abs_sub _ _
    _ = |p t.1| + (t.1 : ℝ) * |p 1| := by
      rw [abs_mul, abs_of_nonneg t.1.coe_nonneg]
    _ ≤ brownianUnitNorm p + brownianUnitNorm p := add_le_add
      (lateralUnitBlock_abs_eval_le_unitNorm p t.1 t.2.2)
      ((mul_le_mul_of_nonneg_left hterminal t.1.coe_nonneg).trans
        (mul_le_of_le_one_left (brownianUnitNorm_nonneg p) htime))
    _ = 2 * brownianUnitNorm p := by ring

/-- The unit bridge has every nonnegative exponential supremum moment. -/
theorem lateralUnitBlock_bridge_exponential_moment_lt_top (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫⁻ p, ENNReal.ofReal
      (Real.exp (θ * brownianUnitNorm (brownianBridgePath 1 p))) ∂P) < ⊤ := by
  have hbound : (∫⁻ p, ENNReal.ofReal
      (Real.exp (θ * brownianUnitNorm (brownianBridgePath 1 p))) ∂P) ≤
      ∫⁻ p, ENNReal.ofReal (Real.exp ((2 * θ) * brownianUnitNorm p)) ∂P := by
    apply lintegral_mono
    intro p
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ θ * (2 * brownianUnitNorm p) :=
        mul_le_mul_of_nonneg_left (lateralUnitBlock_bridge_unitNorm_le p) hθ
      _ = _ := by ring
  exact lt_of_le_of_lt hbound (brownianUnitNorm_exponential_moment_lt_top_all P hB (2 * θ))

/-- The norm exponential of the entire bridge is independent of the terminal scalar. -/
theorem lateralUnitBlock_bridge_exponential_indep_terminal (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (θ : ℝ) :
    IndepFun (fun p => ENNReal.ofReal
      (Real.exp (θ * brownianUnitNorm (brownianBridgePath 1 p))))
      (fun p => p 1) P := by
  exact (brownianBridgePath_indep_terminal P hB 1).comp
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul continuous_brownianUnitNorm.measurable))) measurable_id

/-- Linear interpolation of any real endpoint stays above its negative part. -/
theorem lateralUnitBlock_endpoint_interpolation_lower (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    min 0 v ≤ u * v := by
  by_cases hv : 0 ≤ v
  · rw [min_eq_left hv]
    exact mul_nonneg hu0 hv
  · rw [min_eq_right (le_of_not_ge hv)]
    nlinarith only [le_of_not_ge hv, hu1]

/-- A c-Lipschitz drift differs from its endpoint interpolation by at most 2c. -/
theorem lateralUnitBlock_drift_remainder_abs_le (F : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hF : LipschitzWith (Real.toNNReal c) F) (a u : ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |F (a + u) - F a - u * (F (a + 1) - F a)| ≤ 2 * c := by
  have hlocal := hF.dist_le_mul (a + u) a
  have hend := hF.dist_le_mul (a + 1) a
  simp only [Real.dist_eq, Real.coe_toNNReal _ hc, add_sub_cancel_left,
    abs_of_nonneg hu0] at hlocal
  simp only [Real.dist_eq, Real.coe_toNNReal _ hc, add_sub_cancel_left,
    abs_one, mul_one] at hend
  calc
    _ ≤ |F (a + u) - F a| + |u * (F (a + 1) - F a)| := abs_sub _ _
    _ = |F (a + u) - F a| + u * |F (a + 1) - F a| := by
      rw [abs_mul, abs_of_nonneg hu0]
    _ ≤ c * u + u * c := add_le_add hlocal
      (mul_le_mul_of_nonneg_left hend hu0)
    _ ≤ 2 * c := by nlinarith only [hc, hu1]

/-- The normalized path-plus-drift increment has the bridge lower bound at every time. -/
theorem lateralUnitBlock_path_increment_lower (p : BrownianPath) (F : ℝ → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hF : LipschitzWith (Real.toNNReal c) F)
    (a u : ℝ≥0) (hu : u ≤ 1) :
    min 0 (p (a + 1) - p a + F ((a : ℝ) + 1) - F a) - 2 * c -
        brownianUnitNorm (brownianBridgePath 1 (brownianShiftPath a p)) ≤
      p (a + u) + F ((a : ℝ) + u) - (p a + F a) := by
  have huR : (u : ℝ) ≤ 1 := by exact_mod_cast hu
  have hr := lateralUnitBlock_drift_remainder_abs_le F c hc hF a u u.coe_nonneg huR
  have hb := lateralUnitBlock_abs_eval_le_unitNorm (brownianBridgePath 1 (brownianShiftPath a p)) u hu
  have he := lateralUnitBlock_endpoint_interpolation_lower (u : ℝ)
    (p (a + 1) - p a + F ((a : ℝ) + 1) - F a) u.coe_nonneg huR
  rw [lateralUnitBlock_bridge_eval _ u hu] at hb
  change |p (a + u) - p a - (u : ℝ) * (p (a + 1) - p a)| ≤ _ at hb
  have hlr := (abs_le.mp hr).1
  have hlb := (abs_le.mp hb).1
  linarith only [he, hlr, hlb]

/-- The unit-block mass lower bound is pathwise, retaining the actual interval mass. -/
theorem lateralUnitBlock_unitBlockMass_lower {Ω : Type*} (γ c : ℝ) (hγ : 0 ≤ γ)
    (hc : 0 ≤ c) (B : Ω → BrownianPath) (F : ℝ → ℝ)
    (hF : LipschitzWith (Real.toNNReal c) F) (Z : Ω → Measure ℝ)
    (a : ℝ≥0) (ω : Ω) :
    ENNReal.ofReal (Real.exp (γ *
      (min 0 (lateralUnitBlockEndpointIncrement B F a ω) - 2 * c -
        brownianUnitNorm (brownianBridgePath 1 (brownianShiftPath a (B ω)))))) *
      Z ω (Icc (a : ℝ) ((a : ℝ) + 1)) ≤ lateralUnitBlockMass γ B F Z a ω := by
  classical
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ *
    (min 0 (lateralUnitBlockEndpointIncrement B F a ω) - 2 * c -
      brownianUnitNorm (brownianBridgePath 1 (brownianShiftPath a (B ω))))))
  have hconstant : K * Z ω (Icc (a : ℝ) ((a : ℝ) + 1)) =
      ∫⁻ s, (Icc (a : ℝ) ((a : ℝ) + 1)).indicator (fun _ => K) s ∂Z ω := by
    rw [lintegral_indicator measurableSet_Icc, lintegral_const,
      Measure.restrict_apply_univ]
  rw [hconstant]
  apply lintegral_mono
  intro s
  by_cases hs : s ∈ Icc (a : ℝ) ((a : ℝ) + 1)
  · rw [Set.indicator_of_mem hs]
    change K ≤ if s ∈ Icc (a : ℝ) ((a : ℝ) + 1) then _ else 0
    rw [ite_eq_left hs]
    have hs0 : 0 ≤ s := a.coe_nonneg.trans hs.1
    let u : ℝ≥0 := ⟨s - a, sub_nonneg.mpr hs.1⟩
    have hu : u ≤ 1 := by change s - a ≤ 1; linarith only [hs.2]
    have hsum : a + u = (⟨s, hs0⟩ : ℝ≥0) := by
      apply NNReal.eq
      change (a : ℝ) + (s - a) = s
      ring
    have hsumR : (a : ℝ) + u = s := congrArg NNReal.toReal hsum
    have hb := lateralUnitBlock_path_increment_lower (B ω) F c hc hF a u hu
    rw [hsum, hsumR] at hb
    have hvaluea : brownianPathValue B ω (a : ℝ) = B ω a := by
      exact lateralUnitBlock_brownianPathValue_nnreal B ω a
    have hvalues : brownianPathValue B ω s = B ω ⟨s, hs0⟩ := by
      simp only [brownianPathValue, dite_eq_left hs0]
    have hendpoint : lateralUnitBlockEndpointIncrement B F a ω =
        (B ω) (a + 1) - (B ω) a + F ((a : ℝ) + 1) - F a := by
      unfold lateralUnitBlockEndpointIncrement
      rw [show (a : ℝ) + 1 = ((a + 1 : ℝ≥0) : ℝ) by simp,
        lateralUnitBlock_brownianPathValue_nnreal, lateralUnitBlock_brownianPathValue_nnreal]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    rw [hvalues, hvaluea]
    rw [hendpoint]
    exact mul_le_mul_of_nonneg_left hb hγ
  · rw [Set.indicator_of_notMem hs]
    exact bot_le

/-- The negative-part endpoint exponential is bounded by the two literal endpoint terms. -/
theorem lateralUnitBlock_exp_min_le (k v : ℝ) :
    Real.exp (-k * min 0 v) ≤ 1 + Real.exp (-k * v) := by
  by_cases hv : 0 ≤ v
  · rw [min_eq_left hv, mul_zero, Real.exp_zero]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [min_eq_right (le_of_not_ge hv)]
    exact le_add_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)

/-- Taking a negative power gives a bridge exponential and the literal lateral inverse mass.
Zero interval masses are retained with their extended negative-power value. -/
theorem lateralUnitBlock_unitBlockMass_inverse_le {Ω : Type*} (γ q c : ℝ)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) (hc : 0 ≤ c)
    (B : Ω → BrownianPath) (F : ℝ → ℝ)
    (hF : LipschitzWith (Real.toNNReal c) F) (Z : Ω → Measure ℝ)
    (a : ℝ≥0) (ω : Ω) (hfinite : Z ω (Icc (a : ℝ) ((a : ℝ) + 1)) ≠ ⊤) :
    (lateralUnitBlockMass γ B F Z a ω) ^ (-q) ≤
      ENNReal.ofReal (Real.exp (2 * q * γ * c)) *
        ENNReal.ofReal (Real.exp (q * γ *
          brownianUnitNorm (brownianBridgePath 1 (brownianShiftPath a (B ω))))) *
        ENNReal.ofReal (1 + Real.exp (-q * γ * lateralUnitBlockEndpointIncrement B F a ω)) *
        (Z ω (Icc (a : ℝ) ((a : ℝ) + 1))) ^ (-q) := by
  let v := lateralUnitBlockEndpointIncrement B F a ω
  let W := brownianUnitNorm (brownianBridgePath 1 (brownianShiftPath a (B ω)))
  have hl := lateralUnitBlock_unitBlockMass_lower γ c hγ hc B F hF Z a ω
  have hp := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hl hq)
  rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg,
    ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hfinite,
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul] at hp
  have hexponent : γ * (min 0 v - 2 * c - W) * (-q) =
      2 * q * γ * c + q * γ * W + (-(q * γ) * min 0 v) := by ring
  change _ ≤ ENNReal.ofReal (Real.exp (γ * (min 0 v - 2 * c - W) * (-q))) * _ at hp
  rw [hexponent, Real.exp_add, Real.exp_add,
    ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)),
    ENNReal.ofReal_mul (Real.exp_nonneg _)] at hp
  have hendpoint := ENNReal.ofReal_le_ofReal (lateralUnitBlock_exp_min_le (q * γ) v)
  simpa only [neg_mul] using hp.trans (mul_le_mul' (mul_le_mul' le_rfl hendpoint) le_rfl)

end DOZZ.Proofs

end
