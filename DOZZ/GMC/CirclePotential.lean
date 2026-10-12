/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog

/-! Circle potentials for the GMC admissibility estimates. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def circleKernel (x : ℂ) (r : ℝ) (y : ℂ) (s : ℝ) : ℝ :=
  ∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r

namespace CirclePotential

/-! ### Circle measures as circle averages -/

/-- Integrals against `circleMeasure x r` are circle averages over the circle of radius
`e^{-r}`. -/
theorem integral_circleMeasure_eq_circleAverage {f : ℂ → ℝ} (hf : Measurable f) (x : ℂ)
    (r : ℝ) : ∫ u, f u ∂circleMeasure x r = circleAverage f x (Real.exp (-r)) := by
  unfold circleMeasure
  rw [integral_smul_measure, integral_map (continuous_circleMap x _).measurable.aemeasurable
    hf.aestronglyMeasurable, ← intervalIntegral.integral_of_le (by positivity),
    ENNReal.toReal_ofReal (by positivity)]
  rfl

/-! ### Elementary real inequalities -/

/-- `log b + log⁺ (b⁻¹ * t) = log (max t b)` for `b > 0` and `t ≥ 0`. -/
theorem log_add_posLog_eq {b t : ℝ} (hb : 0 < b) (ht : 0 ≤ t) :
    Real.log b + Real.posLog (b⁻¹ * t) = Real.log (max t b) := by
  rw [Real.posLog_eq_log_max_one (by positivity), ← Real.log_mul hb.ne' (by positivity),
    mul_max_of_nonneg _ _ hb.le, mul_one, mul_inv_cancel_left₀ hb.ne', max_comm]

/-- `log` is `1/b`-Lipschitz on `[b, ∞)`. -/
theorem abs_log_sub_log_le {p q b : ℝ} (hb : 0 < b) (hp : b ≤ p) (hq : b ≤ q) :
    |Real.log p - Real.log q| ≤ |p - q| / b := by
  wlog hpq : q ≤ p generalizing p q
  · rw [abs_sub_comm, abs_sub_comm p q]
    exact this hq hp (le_of_not_ge hpq)
  have hq0 : 0 < q := lt_of_lt_of_le hb hq
  have hp0 : 0 < p := lt_of_lt_of_le hb hp
  have h1 : 0 ≤ Real.log p - Real.log q := sub_nonneg.2 (Real.log_le_log hq0 hpq)
  rw [abs_of_nonneg h1, abs_of_nonneg (sub_nonneg.2 hpq), ← Real.log_div hp0.ne' hq0.ne']
  calc Real.log (p / q) ≤ p / q - 1 := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
    _ = (p - q) / q := by field_simp
    _ ≤ (p - q) / b := div_le_div_of_nonneg_left (sub_nonneg.2 hpq) hb hq

/-! ### The regular part `h(u) = log |u|_+` -/

theorem continuous_log_normPlus : Continuous (fun u : ℂ => Real.log (normPlus u)) := by
  unfold normPlus
  exact Continuous.log (continuous_const.max continuous_norm)
    (fun u => (lt_of_lt_of_le one_pos (le_max_left 1 ‖u‖)).ne')

theorem log_normPlus_nonneg (u : ℂ) : 0 ≤ Real.log (normPlus u) :=
  Real.log_nonneg (le_max_left _ _)

/-- `h = log |·|_+` is `1`-Lipschitz. -/
theorem abs_log_normPlus_sub_le (u x : ℂ) :
    |Real.log (normPlus u) - Real.log (normPlus x)| ≤ ‖u - x‖ := by
  have := abs_log_sub_log_le one_pos (le_max_left 1 ‖u‖) (le_max_left 1 ‖x‖)
  calc |Real.log (normPlus u) - Real.log (normPlus x)| ≤ |max 1 ‖u‖ - max 1 ‖x‖| / 1 := this
    _ = |max ‖u‖ 1 - max ‖x‖ 1| := by rw [div_one, max_comm 1, max_comm 1]
    _ ≤ |‖u‖ - ‖x‖| := abs_max_sub_max_le_abs _ _ _
    _ ≤ ‖u - x‖ := abs_norm_sub_norm_le u x

/-! ### The truncated logarithm `u ↦ log (max ‖u - y‖ b)` -/

theorem continuous_log_max {y : ℂ} {b : ℝ} (hb : 0 < b) :
    Continuous (fun u : ℂ => Real.log (max ‖u - y‖ b)) :=
  Continuous.log (((continuous_id.sub continuous_const).norm).max continuous_const)
    (fun _ => (lt_of_lt_of_le hb (le_max_right _ _)).ne')

theorem abs_log_max_sub_le (u x y : ℂ) {b : ℝ} (hb : 0 < b) :
    |Real.log (max ‖u - y‖ b) - Real.log (max ‖x - y‖ b)| ≤ ‖u - x‖ / b := by
  calc |Real.log (max ‖u - y‖ b) - Real.log (max ‖x - y‖ b)|
      ≤ |max ‖u - y‖ b - max ‖x - y‖ b| / b :=
        abs_log_sub_log_le hb (le_max_right _ _) (le_max_right _ _)
    _ ≤ |‖u - y‖ - ‖x - y‖| / b :=
        div_le_div_of_nonneg_right (abs_max_sub_max_le_abs _ _ _) hb.le
    _ ≤ ‖u - x‖ / b := by
        gcongr
        calc |‖u - y‖ - ‖x - y‖| ≤ ‖(u - y) - (x - y)‖ := abs_norm_sub_norm_le _ _
          _ = ‖u - x‖ := by rw [sub_sub_sub_cancel_right]

/-- Mathlib's circle average of `log ‖· - w‖`, in `max` form. -/
theorem circleAverage_log_norm_sub {c w : ℂ} {R : ℝ} (hR : 0 < R) :
    circleAverage (fun v => Real.log ‖v - w‖) c R = Real.log (max ‖w - c‖ R) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hR.ne',
    log_add_posLog_eq hR (norm_nonneg _), norm_sub_rev]

/-- The circle average of `log ‖· - y‖` is at most that of `log (max ‖· - y‖ b)`
(the two integrands are ordered off the single point `y`). -/
theorem circleAverage_log_norm_sub_le (x y : ℂ) {a b : ℝ} (ha : a ≠ 0) (hb : 0 < b) :
    circleAverage (fun u => Real.log ‖u - y‖) x a ≤
      circleAverage (fun u => Real.log (max ‖u - y‖ b)) x a := by
  have hsub : circleAverage (fun u => Real.log (max ‖u - y‖ b) - Real.log ‖u - y‖) x a =
      circleAverage (fun u => Real.log (max ‖u - y‖ b)) x a -
        circleAverage (fun u => Real.log ‖u - y‖) x a :=
    circleAverage_fun_sub (continuous_log_max hb).continuousOn.circleIntegrable'
      (circleIntegrable_log_norm_sub_const a)
  have hcongr : circleAverage (fun u => Real.log (max ‖u - y‖ b) - Real.log ‖u - y‖) x a =
      circleAverage (fun u => max (Real.log (max ‖u - y‖ b) - Real.log ‖u - y‖) 0) x a := by
    apply circleAverage_congr_codiscreteWithin _ ha
    filter_upwards [compl_singleton_mem_codiscreteWithin y] with u hu
    have hpos : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 (Set.mem_compl_singleton_iff.1 hu))
    exact (max_eq_left (sub_nonneg.2 (Real.log_le_log hpos (le_max_left _ _)))).symm
  have hnn : 0 ≤ circleAverage
      (fun u => max (Real.log (max ‖u - y‖ b) - Real.log ‖u - y‖) 0) x a :=
    circleAverage_nonneg_of_nonneg (fun u _ => le_max_right _ _)
  linarith

/-! ### The inner potential -/

/-- The circle average `C_y = ∫ h dσ_{y,s}` of the regular part. -/
noncomputable def regAvg (y : ℂ) (s : ℝ) : ℝ :=
  circleAverage (fun v => Real.log (normPlus v)) y (Real.exp (-s))

/-- The inner potential `φ(u) = ∫ G(u, v) dσ_{y,s}(v)`. -/
noncomputable def innerPot (y : ℂ) (s : ℝ) (u : ℂ) : ℝ :=
  -Real.log (max ‖u - y‖ (Real.exp (-s))) + Real.log (normPlus u) + regAvg y s

theorem continuous_innerPot (y : ℂ) (s : ℝ) : Continuous (innerPot y s) := by
  unfold innerPot
  exact ((continuous_log_max (Real.exp_pos (-s))).neg.add continuous_log_normPlus).add
    continuous_const

theorem measurable_gffKernel (u : ℂ) : Measurable (gffKernel u) := by
  unfold gffKernel
  exact ((Real.measurable_log.comp (continuous_const.sub continuous_id).norm.measurable).neg.add
    measurable_const).add continuous_log_normPlus.measurable

theorem integral_gffKernel_circleMeasure (u y : ℂ) (s : ℝ) :
    ∫ v, gffKernel u v ∂circleMeasure y s = innerPot y s u := by
  rw [integral_circleMeasure_eq_circleAverage (measurable_gffKernel u)]
  have hb := Real.exp_pos (-s)
  have hfun : gffKernel u = ((fun _ => Real.log (normPlus u)) + fun v => Real.log (normPlus v)) -
      fun v => Real.log ‖v - u‖ := by
    funext v
    simp only [gffKernel, Pi.add_apply, Pi.sub_apply, norm_sub_rev u v]
    ring
  have hI1 : CircleIntegrable ((fun _ => Real.log (normPlus u)) + fun v => Real.log (normPlus v))
      y (Real.exp (-s)) :=
    (circleIntegrable_const _ _ _).add continuous_log_normPlus.continuousOn.circleIntegrable'
  rw [hfun, circleAverage_sub hI1 (circleIntegrable_log_norm_sub_const _),
    circleAverage_add (circleIntegrable_const _ _ _)
      continuous_log_normPlus.continuousOn.circleIntegrable',
    circleAverage_const, circleAverage_log_norm_sub hb]
  unfold innerPot regAvg
  ring

theorem circleKernel_eq (x y : ℂ) (r s : ℝ) :
    circleKernel x r y s = circleAverage (innerPot y s) x (Real.exp (-r)) := by
  have h : (fun u => ∫ v, gffKernel u v ∂circleMeasure y s) = innerPot y s :=
    funext fun u => integral_gffKernel_circleMeasure u y s
  unfold circleKernel
  rw [h, integral_circleMeasure_eq_circleAverage (continuous_innerPot y s).measurable]

theorem circleAverage_innerPot (x y : ℂ) (r s : ℝ) :
    circleAverage (innerPot y s) x (Real.exp (-r)) =
      -circleAverage (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x (Real.exp (-r)) +
        circleAverage (fun u => Real.log (normPlus u)) x (Real.exp (-r)) + regAvg y s := by
  have hfun : innerPot y s = ((fun u => Real.log (normPlus u)) + fun _ => regAvg y s) -
      fun u => Real.log (max ‖u - y‖ (Real.exp (-s))) := by
    funext u
    simp only [innerPot, Pi.add_apply, Pi.sub_apply]
    ring
  have hI1 : CircleIntegrable ((fun u => Real.log (normPlus u)) + fun _ => regAvg y s)
      x (Real.exp (-r)) :=
    continuous_log_normPlus.continuousOn.circleIntegrable'.add (circleIntegrable_const _ _ _)
  rw [hfun, circleAverage_sub hI1
      (continuous_log_max (Real.exp_pos (-s))).continuousOn.circleIntegrable',
    circleAverage_add continuous_log_normPlus.continuousOn.circleIntegrable'
      (circleIntegrable_const _ _ _), circleAverage_const]
  ring

/-! ### Averages against a center value -/

theorem abs_circleAverage_sub_le {g : ℂ → ℝ} {c : ℂ} {R K : ℝ} (hg : CircleIntegrable g c R)
    (hK : ∀ u ∈ Metric.sphere c |R|, |g u - g c| ≤ K) : |circleAverage g c R - g c| ≤ K := by
  rw [abs_sub_le_iff]
  constructor
  · have := circleAverage_mono_on_of_le_circle (a := g c + K) hg
      (fun u hu => by linarith [(abs_le.1 (hK u hu)).2])
    linarith
  · have := circleAverage_mono (circleIntegrable_const (g c - K) c R) hg
      (fun u hu => by linarith [(abs_le.1 (hK u hu)).1])
    rw [circleAverage_const] at this
    linarith

theorem abs_circleAverage_log_normPlus_sub_le (c : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    |circleAverage (fun u => Real.log (normPlus u)) c ρ - Real.log (normPlus c)| ≤ ρ := by
  refine abs_circleAverage_sub_le continuous_log_normPlus.continuousOn.circleIntegrable'
    (fun u hu => ?_)
  rw [mem_sphere_iff_norm, abs_of_pos hρ] at hu
  rw [← hu]
  exact abs_log_normPlus_sub_le u c

theorem circleAverage_log_normPlus_bounds {c : ℂ} {R ρ : ℝ} (hR : 0 ≤ R) (hc : ‖c‖ ≤ R)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 ≤ circleAverage (fun u => Real.log (normPlus u)) c ρ ∧
      circleAverage (fun u => Real.log (normPlus u)) c ρ ≤ Real.log (1 + R) := by
  constructor
  · exact circleAverage_nonneg_of_nonneg (fun u _ => log_normPlus_nonneg u)
  · apply circleAverage_mono_on_of_le_circle continuous_log_normPlus.continuousOn.circleIntegrable'
    intro u hu
    rw [mem_sphere_iff_norm, abs_of_pos hρ0] at hu
    apply Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _))
    have := norm_sub_norm_le u c
    exact max_le (by linarith) (by linarith)

end CirclePotential

open CirclePotential

theorem abs_circleKernel_sub_log_le : ∀ R : ℝ, 0 ≤ R → ∀ x y : ℂ, ‖x‖ ≤ R → ‖y‖ ≤ R → ∀ r s : ℝ, 0 ≤ r → 0 ≤ s →
    |circleKernel x r y s -
        Real.log (1 / max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))))| ≤
      Real.log 3 + 2 * Real.log (1 + R) := by
  intro R hR x y hx hy r s hr hs
  have ha : 0 < Real.exp (-r) := Real.exp_pos _
  have hb : 0 < Real.exp (-s) := Real.exp_pos _
  have ha1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hb1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hMa : Real.exp (-r) ≤ max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hMb : Real.exp (-s) ≤ max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hMxy : ‖x - y‖ ≤ max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))) := le_max_left _ _
  have hMpos : 0 < max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))) := lt_of_lt_of_le ha hMa
  have hgI : CircleIntegrable (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x
      (Real.exp (-r)) := (continuous_log_max hb).continuousOn.circleIntegrable'
  -- upper bound on the average of the truncated logarithm
  have hg_upper : circleAverage (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x
      (Real.exp (-r)) ≤
        Real.log 3 + Real.log (max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s)))) := by
    rw [← Real.log_mul (by norm_num) hMpos.ne']
    apply circleAverage_mono_on_of_le_circle hgI
    intro u hu
    rw [mem_sphere_iff_norm, abs_of_pos ha] at hu
    apply Real.log_le_log (lt_of_lt_of_le hb (le_max_right _ _))
    have := norm_sub_le_norm_sub_add_norm_sub u x y
    exact max_le (by linarith) (by linarith)
  -- lower bound on the average of the truncated logarithm
  have hg_lower : Real.log (max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s)))) ≤
      circleAverage (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x (Real.exp (-r)) := by
    have hb_le : Real.log (Real.exp (-s)) ≤
        circleAverage (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x (Real.exp (-r)) := by
      have := circleAverage_mono (circleIntegrable_const (Real.log (Real.exp (-s))) x
        (Real.exp (-r))) hgI (fun u _ => Real.log_le_log hb (le_max_right _ _))
      rwa [circleAverage_const] at this
    have hxy_le : Real.log (max ‖x - y‖ (Real.exp (-r))) ≤
        circleAverage (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x (Real.exp (-r)) := by
      have h1 := circleAverage_log_norm_sub_le x y ha.ne' hb
      rw [circleAverage_log_norm_sub ha, norm_sub_rev] at h1
      exact h1
    rw [← max_assoc]
    rcases le_total (max ‖x - y‖ (Real.exp (-r))) (Real.exp (-s)) with h | h
    · rw [max_eq_right h]
      exact hb_le
    · rw [max_eq_left h]
      exact hxy_le
  -- the regular parts
  have hhx := circleAverage_log_normPlus_bounds hR hx ha ha1
  have hhy := circleAverage_log_normPlus_bounds hR hy hb hb1
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hlogR : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  rw [circleKernel_eq, circleAverage_innerPot, one_div, Real.log_inv]
  unfold regAvg
  rw [abs_le]
  constructor <;> linarith [hhx.1, hhx.2, hhy.1, hhy.2]

theorem abs_circleKernel_sub_gffKernel_le : ∀ x y : ℂ, ∀ r s : ℝ, Real.exp (-r) + Real.exp (-s) ≤ ‖x - y‖ →
    |circleKernel x r y s - gffKernel x y| ≤ Real.exp (-r) + Real.exp (-s) := by
  intro x y r s hxy
  have ha : 0 < Real.exp (-r) := Real.exp_pos _
  have hb : 0 < Real.exp (-s) := Real.exp_pos _
  have hsphere : Set.EqOn (fun u => Real.log (max ‖u - y‖ (Real.exp (-s))))
      (fun u => Real.log ‖u - y‖) (Metric.sphere x |Real.exp (-r)|) := by
    intro u hu
    rw [mem_sphere_iff_norm, abs_of_pos ha] at hu
    have := norm_sub_le_norm_sub_add_norm_sub x u y
    rw [norm_sub_rev x u, hu] at this
    simp only [max_eq_left (show Real.exp (-s) ≤ ‖u - y‖ by linarith)]
  have hlog : circleAverage (fun u => Real.log (max ‖u - y‖ (Real.exp (-s)))) x
      (Real.exp (-r)) = Real.log ‖x - y‖ := by
    rw [circleAverage_congr_sphere hsphere, circleAverage_log_norm_sub ha, norm_sub_rev,
      max_eq_left (by linarith)]
  have hX := abs_circleAverage_log_normPlus_sub_le x ha
  have hY := abs_circleAverage_log_normPlus_sub_le y hb
  rw [circleKernel_eq, circleAverage_innerPot, hlog]
  unfold gffKernel regAvg
  calc |-Real.log ‖x - y‖ + circleAverage (fun u => Real.log (normPlus u)) x (Real.exp (-r)) +
          circleAverage (fun v => Real.log (normPlus v)) y (Real.exp (-s)) -
        (-Real.log ‖x - y‖ + Real.log (normPlus x) + Real.log (normPlus y))|
      = |(circleAverage (fun u => Real.log (normPlus u)) x (Real.exp (-r)) -
            Real.log (normPlus x)) +
          (circleAverage (fun v => Real.log (normPlus v)) y (Real.exp (-s)) -
            Real.log (normPlus y))| := by ring_nf
    _ ≤ |circleAverage (fun u => Real.log (normPlus u)) x (Real.exp (-r)) -
            Real.log (normPlus x)| +
          |circleAverage (fun v => Real.log (normPlus v)) y (Real.exp (-s)) -
            Real.log (normPlus y)| := abs_add_le _ _
    _ ≤ Real.exp (-r) + Real.exp (-s) := add_le_add hX hY

theorem abs_circleKernel_sub_integral_gffKernel_le : ∀ x y : ℂ, ∀ r s : ℝ,
    |circleKernel x r y s - ∫ v, gffKernel x v ∂circleMeasure y s| ≤
      (Real.exp s + 1) * Real.exp (-r) := by
  intro x y r s
  rw [circleKernel_eq, integral_gffKernel_circleMeasure]
  have ha : 0 < Real.exp (-r) := Real.exp_pos _
  have hb : 0 < Real.exp (-s) := Real.exp_pos _
  refine abs_circleAverage_sub_le (continuous_innerPot y s).continuousOn.circleIntegrable'
    (fun u hu => ?_)
  rw [mem_sphere_iff_norm, abs_of_pos ha] at hu
  have h1 := abs_log_max_sub_le u x y hb
  have h2 := abs_log_normPlus_sub_le u x
  have heq : innerPot y s u - innerPot y s x =
      -(Real.log (max ‖u - y‖ (Real.exp (-s))) - Real.log (max ‖x - y‖ (Real.exp (-s)))) +
        (Real.log (normPlus u) - Real.log (normPlus x)) := by
    unfold innerPot
    ring
  have h3 : ‖u - x‖ / Real.exp (-s) = Real.exp s * Real.exp (-r) := by
    rw [hu, Real.exp_neg s, div_inv_eq_mul, mul_comm]
  rw [heq]
  calc |-(Real.log (max ‖u - y‖ (Real.exp (-s))) - Real.log (max ‖x - y‖ (Real.exp (-s)))) +
        (Real.log (normPlus u) - Real.log (normPlus x))|
      ≤ |-(Real.log (max ‖u - y‖ (Real.exp (-s))) - Real.log (max ‖x - y‖ (Real.exp (-s))))| +
        |Real.log (normPlus u) - Real.log (normPlus x)| := abs_add_le _ _
    _ = |Real.log (max ‖u - y‖ (Real.exp (-s))) - Real.log (max ‖x - y‖ (Real.exp (-s)))| +
        |Real.log (normPlus u) - Real.log (normPlus x)| := by rw [abs_neg]
    _ ≤ ‖u - x‖ / Real.exp (-s) + ‖u - x‖ := add_le_add h1 h2
    _ = (Real.exp s + 1) * Real.exp (-r) := by rw [h3, hu]; ring

end DOZZ.Proofs
