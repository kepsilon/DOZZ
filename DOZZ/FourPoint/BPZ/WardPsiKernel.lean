/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardDeroot

/-! # Kernel estimates for the rooted mixed mass

The cutoff-region kernel `e^{γ²(Λ_r(x - y) + h_r(y))}` is differentiable in `x` off the diagonal
and log-Lipschitz in `x` uniformly in `y`. The limit-region kernel
`e^{γ²(Λ¹_r(x - y) + log|y|₊)}` equals `(|y|₊ / |x - y|)^{γ²}` once `|x - y| ≥ e^{-r}`; on a ball
kept at distance `δ` from the limit region it is differentiable and Lipschitz in `x` with a
constant independent of `y`. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem norm_bpzLamDeriv_le_exp (r : ℝ) (w : ℂ) : ‖bpzLamDeriv r w‖ ≤ Real.exp r := by
  have hpt : ∀ θ : ℝ, ‖bpzTruncLogDeriv r (w + Real.exp (-r) * Complex.exp (θ * Complex.I))‖ ≤
      Real.exp r := fun θ => (norm_bpzTruncLogDeriv_le r _).1
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * Real.pi) (fun θ (_ : θ ∈ Set.uIoc 0 (2 * Real.pi)) => hpt θ)
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hint
  unfold bpzLamDeriv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity :
    (0 : ℝ) < 2 * Real.pi))]
  calc (2 * Real.pi)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * Real.pi, _‖
      ≤ (2 * Real.pi)⁻¹ * (Real.exp r * (2 * Real.pi)) := by gcongr
    _ = Real.exp r := by field_simp

theorem bpzLam_le (r : ℝ) (w : ℂ) : bpzLam r w ≤ r := by
  rw [bpzLam_eq_interval]
  have hpi : 0 < 2 * Real.pi := by positivity
  have hcont : Continuous fun θ : ℝ =>
      bpzTruncLog r (w + Real.exp (-r) * Complex.exp (θ * Complex.I)) :=
    (continuous_bpzTruncLog r).comp (continuous_const.add (continuous_const.mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const))))
  have hle : ∫ θ in (0 : ℝ)..2 * Real.pi,
      bpzTruncLog r (w + Real.exp (-r) * Complex.exp (θ * Complex.I)) ≤
        ∫ _θ in (0 : ℝ)..2 * Real.pi, r :=
    intervalIntegral.integral_mono_on hpi.le (hcont.intervalIntegrable _ _)
      intervalIntegrable_const fun θ _ => bpzTruncLog_le r _
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  calc (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, _ ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * r) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = r := by field_simp

theorem bpz_abs_exp_sub_exp_le (a b : ℝ) :
    |Real.exp a - Real.exp b| ≤ Real.exp (max a b) * |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, max_comm, abs_sub_comm a b]
    exact this b a (le_of_not_ge hab)
  rw [max_eq_right hab, abs_of_nonpos (by linarith [Real.exp_le_exp.mpr hab]),
    abs_of_nonpos (by linarith)]
  have h := Real.add_one_le_exp (a - b)
  have hexp : Real.exp a = Real.exp b * Real.exp (a - b) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have hb := Real.exp_pos b
  nlinarith

/-- The cutoff-region kernel is differentiable off the diagonal. -/
theorem hasFDerivAt_bpzCutRootKernel (γ r : ℝ) {x y : ℂ} (hxy : x ≠ y) :
    HasFDerivAt (fun x' => bpzCutRootKernel γ r x' y)
      ((bpzCutRootKernel γ r x y * γ ^ 2) • bpzLamDeriv r (x - y)) x := by
  have hΛ : HasFDerivAt (fun x' => bpzLam r (x' - y)) (bpzLamDeriv r (x - y)) x := by
    have h1 := hasFDerivAt_bpzLam r (sub_ne_zero.mpr hxy)
    have h2 : HasFDerivAt (fun x' : ℂ => x' - y) (ContinuousLinearMap.id ℝ ℂ) x :=
      (hasFDerivAt_id x).sub_const y
    simpa [Function.comp_def] using h1.comp x h2
  have hin : HasFDerivAt (fun x' => γ ^ 2 * (bpzLam r (x' - y) + bpzPin r y))
      (γ ^ 2 • bpzLamDeriv r (x - y)) x := by
    have := (hΛ.add_const (bpzPin r y)).const_mul (γ ^ 2)
    simpa using this
  have hexp := hin.exp
  unfold bpzCutRootKernel
  convert hexp using 1
  rw [smul_smul]


/-- The Lipschitz bound of the cutoff-region kernel in the root. -/
theorem abs_bpzCutRootKernel_sub_le (γ r : ℝ) (x x' y : ℂ) :
    |bpzCutRootKernel γ r x y - bpzCutRootKernel γ r x' y| ≤
      γ ^ 2 * Real.exp (γ ^ 2 * r) * Real.exp (γ ^ 2 * bpzPin r y) * Real.exp r * ‖x - x'‖ := by
  unfold bpzCutRootKernel
  have hγ : 0 ≤ γ ^ 2 := sq_nonneg γ
  set a := γ ^ 2 * (bpzLam r (x - y) + bpzPin r y)
  set b := γ ^ 2 * (bpzLam r (x' - y) + bpzPin r y)
  have hmax : max a b ≤ γ ^ 2 * r + γ ^ 2 * bpzPin r y := by
    have h1 := bpzLam_le r (x - y)
    have h2 := bpzLam_le r (x' - y)
    apply max_le <;> nlinarith
  have hab : |a - b| ≤ γ ^ 2 * (Real.exp r * ‖x - x'‖) := by
    have h := abs_bpzLam_sub_le r (x - y) (x' - y)
    rw [show x - y - (x' - y) = x - x' by ring] at h
    have : a - b = γ ^ 2 * (bpzLam r (x - y) - bpzLam r (x' - y)) := by ring
    rw [this, abs_mul, abs_of_nonneg hγ]
    exact mul_le_mul_of_nonneg_left h hγ
  have hexp := bpz_abs_exp_sub_exp_le a b
  calc |Real.exp a - Real.exp b| ≤ Real.exp (max a b) * |a - b| := hexp
    _ ≤ Real.exp (γ ^ 2 * r + γ ^ 2 * bpzPin r y) * (γ ^ 2 * (Real.exp r * ‖x - x'‖)) := by
        gcongr
    _ = _ := by rw [Real.exp_add]; ring

theorem bpzTruncLog_eq_of_le (r : ℝ) {w : ℂ} (hw : Real.exp (-r) ≤ ‖w‖) :
    bpzTruncLog r w = -Real.log ‖w‖ := by
  simp only [bpzTruncLog, max_eq_right hw]

/-- Away from the truncation radius the limit-region kernel is an explicit power. -/
theorem bpzLimRootKernel_eq (γ r : ℝ) {x y : ℂ} (hxy : Real.exp (-r) ≤ ‖x - y‖) :
    bpzLimRootKernel γ r x y = (normPlus y / ‖x - y‖) ^ (γ ^ 2) := by
  have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le (Real.exp_pos _) hxy
  unfold bpzLimRootKernel
  rw [bpzTruncLog_eq_of_le r hxy, Real.rpow_def_of_pos (div_pos (bpz_normPlus_pos y) hpos),
    Real.log_div (bpz_normPlus_pos y).ne' hpos.ne']
  congr 1
  ring

/-- The limit-region kernel is differentiable off the truncation circle. -/
theorem hasFDerivAt_bpzLimRootKernel (γ r : ℝ) {x y : ℂ} (hxy : ‖x - y‖ ≠ Real.exp (-r)) :
    HasFDerivAt (fun x' => bpzLimRootKernel γ r x' y)
      ((bpzLimRootKernel γ r x y * γ ^ 2) • bpzTruncLogDeriv r (x - y)) x := by
  have hT : HasFDerivAt (fun x' => bpzTruncLog r (x' - y)) (bpzTruncLogDeriv r (x - y)) x := by
    have h1 := hasFDerivAt_bpzTruncLog r hxy
    have h2 : HasFDerivAt (fun x' : ℂ => x' - y) (ContinuousLinearMap.id ℝ ℂ) x :=
      (hasFDerivAt_id x).sub_const y
    simpa [Function.comp_def] using h1.comp x h2
  have hin : HasFDerivAt (fun x' => γ ^ 2 * (bpzTruncLog r (x' - y) + Real.log (normPlus y)))
      (γ ^ 2 • bpzTruncLogDeriv r (x - y)) x := by
    have := (hT.add_const (Real.log (normPlus y))).const_mul (γ ^ 2)
    simpa using this
  have hexp := hin.exp
  unfold bpzLimRootKernel
  convert hexp using 1
  rw [smul_smul]

/-- Upper bound of the limit-region kernel on a separated bounded region. -/
theorem bpzLimRootKernel_le (γ r : ℝ) {δ R : ℝ} (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ)
    {x y : ℂ} (hx : ‖x‖ ≤ R) (hxy : δ ≤ ‖x - y‖) :
    bpzLimRootKernel γ r x y ≤ (1 + (1 + R) / δ) ^ (γ ^ 2) := by
  have hpos : 0 < ‖x - y‖ := lt_of_lt_of_le hδ hxy
  rw [bpzLimRootKernel_eq γ r (le_trans hδr hxy)]
  have hR : 0 ≤ R := le_trans (norm_nonneg x) hx
  have hny : normPlus y ≤ 1 + R + ‖x - y‖ := by
    unfold normPlus
    have := norm_le_norm_add_norm_sub' y x
    rw [norm_sub_rev] at this
    apply max_le <;> linarith [norm_nonneg (x - y)]
  have hratio : normPlus y / ‖x - y‖ ≤ 1 + (1 + R) / δ := by
    rw [div_le_iff₀ hpos]
    have h1 : (1 + R) ≤ (1 + R) / δ * ‖x - y‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left hxy (by linarith)
    nlinarith
  exact Real.rpow_le_rpow (div_nonneg (bpz_normPlus_pos y).le hpos.le) hratio (sq_nonneg γ)

/-- Lipschitz bound of the limit-region kernel in the root on a separated bounded region. -/
theorem abs_bpzLimRootKernel_sub_le (γ r : ℝ) {δ R : ℝ} (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ)
    {x x' y : ℂ} (hx : ‖x‖ ≤ R) (hx' : ‖x'‖ ≤ R) (hxy : δ ≤ ‖x - y‖) (hxy' : δ ≤ ‖x' - y‖) :
    |bpzLimRootKernel γ r x y - bpzLimRootKernel γ r x' y| ≤
      (1 + (1 + R) / δ) ^ (γ ^ 2) * (γ ^ 2 / δ) * ‖x - x'‖ := by
  set a := γ ^ 2 * (bpzTruncLog r (x - y) + Real.log (normPlus y))
  set b := γ ^ 2 * (bpzTruncLog r (x' - y) + Real.log (normPlus y))
  have hka : Real.exp a = bpzLimRootKernel γ r x y := rfl
  have hkb : Real.exp b = bpzLimRootKernel γ r x' y := rfl
  have hmax : Real.exp (max a b) ≤ (1 + (1 + R) / δ) ^ (γ ^ 2) := by
    rcases le_total a b with h | h
    · rw [max_eq_right h, hkb]; exact bpzLimRootKernel_le γ r hδ hδr hx' hxy'
    · rw [max_eq_left h, hka]; exact bpzLimRootKernel_le γ r hδ hδr hx hxy
  have hab : |a - b| ≤ γ ^ 2 / δ * ‖x - x'‖ := by
    have hl := CirclePotential.abs_log_sub_log_le hδ hxy hxy'
    have hd : |‖x - y‖ - ‖x' - y‖| ≤ ‖x - x'‖ := by
      have := abs_norm_sub_norm_le (x - y) (x' - y)
      rwa [show x - y - (x' - y) = x - x' by ring] at this
    have : a - b = γ ^ 2 * (Real.log ‖x' - y‖ - Real.log ‖x - y‖) := by
      simp only [a, b, bpzTruncLog_eq_of_le r (le_trans hδr hxy),
        bpzTruncLog_eq_of_le r (le_trans hδr hxy')]
      ring
    rw [this, abs_mul, abs_of_nonneg (sq_nonneg γ), abs_sub_comm]
    calc γ ^ 2 * |Real.log ‖x - y‖ - Real.log ‖x' - y‖| ≤ γ ^ 2 * (‖x - x'‖ / δ) := by
          gcongr
          exact hl.trans (div_le_div_of_nonneg_right hd hδ.le)
      _ = γ ^ 2 / δ * ‖x - x'‖ := by ring
  calc |bpzLimRootKernel γ r x y - bpzLimRootKernel γ r x' y| = |Real.exp a - Real.exp b| := by
        rw [hka, hkb]
    _ ≤ Real.exp (max a b) * |a - b| := bpz_abs_exp_sub_exp_le a b
    _ ≤ (1 + (1 + R) / δ) ^ (γ ^ 2) * (γ ^ 2 / δ * ‖x - x'‖) :=
        mul_le_mul hmax hab (abs_nonneg _) (Real.rpow_nonneg (by
          have hR : 0 ≤ R := le_trans (norm_nonneg x) hx
          positivity) _)
    _ = _ := by ring




theorem bpzCutRootKernel_pos (γ r : ℝ) (x y : ℂ) : 0 < bpzCutRootKernel γ r x y :=
  Real.exp_pos _

theorem bpzLimRootKernel_pos (γ r : ℝ) (x y : ℂ) : 0 < bpzLimRootKernel γ r x y :=
  Real.exp_pos _

/-- The cutoff-region kernel is log-Lipschitz in the root. -/
theorem abs_log_bpzCutRootKernel_sub_le (γ r : ℝ) (y x x' : ℂ) :
    |Real.log (bpzCutRootKernel γ r x y) - Real.log (bpzCutRootKernel γ r x' y)| ≤
      γ ^ 2 * Real.exp r * ‖x - x'‖ := by
  unfold bpzCutRootKernel
  rw [Real.log_exp, Real.log_exp]
  have h := abs_bpzLam_sub_le r (x - y) (x' - y)
  rw [show x - y - (x' - y) = x - x' by ring] at h
  rw [show γ ^ 2 * (bpzLam r (x - y) + bpzPin r y) - γ ^ 2 * (bpzLam r (x' - y) + bpzPin r y) =
    γ ^ 2 * (bpzLam r (x - y) - bpzLam r (x' - y)) by ring, abs_mul,
    abs_of_nonneg (sq_nonneg γ), mul_assoc]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg γ)

/-- The limit-region kernel is log-Lipschitz in the root on a separated region. -/
theorem abs_log_bpzLimRootKernel_sub_le (γ r : ℝ) {δ : ℝ} (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ)
    {x x' y : ℂ} (hxy : δ ≤ ‖x - y‖) (hxy' : δ ≤ ‖x' - y‖) :
    |Real.log (bpzLimRootKernel γ r x y) - Real.log (bpzLimRootKernel γ r x' y)| ≤
      γ ^ 2 / δ * ‖x - x'‖ := by
  unfold bpzLimRootKernel
  rw [Real.log_exp, Real.log_exp, bpzTruncLog_eq_of_le r (le_trans hδr hxy),
    bpzTruncLog_eq_of_le r (le_trans hδr hxy')]
  have hl := CirclePotential.abs_log_sub_log_le hδ hxy hxy'
  have hd : |‖x - y‖ - ‖x' - y‖| ≤ ‖x - x'‖ := by
    have := abs_norm_sub_norm_le (x - y) (x' - y)
    rwa [show x - y - (x' - y) = x - x' by ring] at this
  rw [show γ ^ 2 * (-Real.log ‖x - y‖ + Real.log (normPlus y)) -
      γ ^ 2 * (-Real.log ‖x' - y‖ + Real.log (normPlus y)) =
      -(γ ^ 2 * (Real.log ‖x - y‖ - Real.log ‖x' - y‖)) by ring, abs_neg, abs_mul,
    abs_of_nonneg (sq_nonneg γ)]
  calc γ ^ 2 * |Real.log ‖x - y‖ - Real.log ‖x' - y‖| ≤ γ ^ 2 * (‖x - x'‖ / δ) := by
        gcongr
        exact hl.trans (div_le_div_of_nonneg_right hd hδ.le)
    _ = γ ^ 2 / δ * ‖x - x'‖ := by ring

end DOZZ.Proofs
