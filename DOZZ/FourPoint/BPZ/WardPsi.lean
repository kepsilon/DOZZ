/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardPsiPath

/-! # Ratio bounds and the root derivative of the rooted moment

On a ball kept at distance `δ` from the limit region the rooted mixed mass is comparable to its
value at the center and Lipschitz with a constant proportional to that value. This bounds the
difference quotients of its negative powers by an integrable multiple of the negative power at
the center, which differentiates the rooted moment `E[J_x^{-q}]` in every direction. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem bpz_ratio_lipschitz' {a b c L δ ε ε' η : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (h1 : |Real.log a - Real.log c| ≤ L * ε) (h2 : |Real.log b - Real.log c| ≤ L * ε')
    (h3 : |Real.log a - Real.log b| ≤ L * η) (hε : ε ≤ δ) (hε' : ε' ≤ δ) :
    |a - b| ≤ L * Real.exp (L * δ) * c * η := by
  have h := bpz_abs_exp_sub_exp_le (Real.log a) (Real.log b)
  rw [Real.exp_log ha, Real.exp_log hb] at h
  have hmax : Real.exp (max (Real.log a) (Real.log b)) ≤ Real.exp (L * δ) * c := by
    rw [← Real.exp_log hc, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    apply max_le
    · have := le_abs_self (Real.log a - Real.log c)
      linarith only [this, h1, mul_le_mul_of_nonneg_left hε hL]
    · have := le_abs_self (Real.log b - Real.log c)
      linarith only [this, h2, mul_le_mul_of_nonneg_left hε' hL]
  calc |a - b| ≤ Real.exp (max (Real.log a) (Real.log b)) * |Real.log a - Real.log b| := h
    _ ≤ (Real.exp (L * δ) * c) * (L * η) :=
        mul_le_mul hmax h3 (abs_nonneg _) (mul_nonneg (Real.exp_pos _).le hc.le)
    _ = _ := by ring

theorem bpz_ratio_lower' {a c L δ ε : ℝ} (hL : 0 ≤ L) (ha : 0 < a) (hc : 0 < c)
    (h1 : |Real.log a - Real.log c| ≤ L * ε) (hε : ε ≤ δ) : Real.exp (-(L * δ)) * c ≤ a := by
  rw [← Real.exp_log ha, ← Real.exp_log hc, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := neg_abs_le (Real.log a - Real.log c)
  linarith only [this, h1, mul_le_mul_of_nonneg_left hε hL]

section Ratio

variable {γ r δ : ℝ} {ρ k₁ k₂ : ℂ → ℝ} {x₀ : ℂ}

/-- The common log-Lipschitz constant of the two kernels on a separated ball. -/
noncomputable def bpzKernelLip (γ r δ : ℝ) : ℝ := max (γ ^ 2 * Real.exp r) (γ ^ 2 / δ)

theorem bpzKernelLip_nonneg : 0 ≤ bpzKernelLip γ r δ :=
  le_max_of_le_left (by positivity)

theorem bpz_sep_ball (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖) {x : ℂ}
    (hx : x ∈ Metric.ball x₀ δ) {y : ℂ} (hy : ρ y < 1) : δ ≤ ‖x - y‖ := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 := hsep y hy
  have h2 := norm_sub_norm_le (x₀ - y) (x₀ - x)
  rw [show x₀ - y - (x₀ - x) = x - y by ring, norm_sub_rev x₀ x] at h2
  linarith

/-- The cutoff kernel's log-Lipschitz bound with the common constant. -/
theorem bpz_cut_log_le (x x' y : ℂ) :
    |Real.log (bpzCutRootKernel γ r x y) - Real.log (bpzCutRootKernel γ r x' y)| ≤
      bpzKernelLip γ r δ * ‖x - x'‖ :=
  (abs_log_bpzCutRootKernel_sub_le γ r y x x').trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

/-- The limit kernel's log-Lipschitz bound with the common constant on a separated ball. -/
theorem bpz_lim_log_le (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) {x x' y : ℂ}
    (hxy : δ ≤ ‖x - y‖) (hxy' : δ ≤ ‖x' - y‖) :
    |Real.log (bpzLimRootKernel γ r x y) - Real.log (bpzLimRootKernel γ r x' y)| ≤
      bpzKernelLip γ r δ * ‖x - x'‖ :=
  (abs_log_bpzLimRootKernel_sub_le γ r hδ hδr hxy hxy').trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end Ratio

section Integrated

variable {γ r δ : ℝ} {ρ k₁ k₂ : ℂ → ℝ} {m₁ m₂ : Measure ℂ} {x₀ : ℂ}

theorem integrable_bpz_cut_part (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hk₁0 : ∀ y, 0 ≤ k₁ y)
    (hI₁ : Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) m₁) (x : ℂ) :
    Integrable (fun y => ρ y * k₁ y * bpzCutRootKernel γ r x y) m₁ := by
  refine (hI₁.mul_const (Real.exp (γ ^ 2 * r))).mono'
    ((hρm.mul hk₁).mul (continuous_bpzCutRootKernel_snd γ r x).measurable).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hw : 0 ≤ ρ y * k₁ y := mul_nonneg (hρ0 y) (hk₁0 y)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (bpzCutRootKernel_pos γ r x y).le)]
  calc ρ y * k₁ y * bpzCutRootKernel γ r x y
      ≤ ρ y * k₁ y * (Real.exp (γ ^ 2 * r) * Real.exp (γ ^ 2 * bpzPin r y)) :=
        mul_le_mul_of_nonneg_left (bpzCutRootKernel_le γ r x y) hw
    _ = _ := by ring

theorem integrable_bpz_lim_part (hρm : Measurable ρ) (hk₂ : Measurable k₂) (hρ1 : ∀ y, ρ y ≤ 1)
    (hk₂0 : ∀ y, 0 ≤ k₂ y) (hI₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖)
    {x : ℂ} (hx : x ∈ Metric.ball x₀ δ) :
    Integrable (fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) m₂ := by
  have hxR : ‖x‖ ≤ ‖x₀‖ + δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have := norm_le_norm_add_norm_sub' x x₀
    linarith
  refine (hI₂.mul_const ((1 + (1 + (‖x₀‖ + δ)) / δ) ^ (γ ^ 2))).mono'
    (((measurable_const.sub hρm).mul hk₂).mul
      (continuous_bpzLimRootKernel_snd γ r x).measurable).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (bpzLimRootKernel_pos γ r x y).le)]
  rcases lt_or_eq_of_le (hρ1 y) with hy | hy
  · exact mul_le_mul_of_nonneg_left (bpzLimRootKernel_le γ r hδ hδr hxR
      (bpz_sep_ball hsep hx hy)) hw
  · rw [hy]; simp

/-- Two-sided comparison and Lipschitz bound of the rooted mixed mass on a separated ball. -/
theorem bpzRootedMixedReal_ratio (hρm : Measurable ρ) (hk₁ : Measurable k₁)
    (hk₂ : Measurable k₂) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y)
    (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (hI₁ : Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) m₁)
    (hI₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖)
    {x x' : ℂ} (hx : x ∈ Metric.ball x₀ δ) (hx' : x' ∈ Metric.ball x₀ δ) :
    Real.exp (-(bpzKernelLip γ r δ * δ)) * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ m₁ m₂ ≤
        bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ ∧
      |bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ - bpzRootedMixedReal γ r ρ k₁ k₂ x' m₁ m₂| ≤
        bpzKernelLip γ r δ * Real.exp (bpzKernelLip γ r δ * δ) *
          bpzRootedMixedReal γ r ρ k₁ k₂ x₀ m₁ m₂ * ‖x - x'‖ := by
  set L := bpzKernelLip γ r δ with hLdef
  have hL : 0 ≤ L := bpzKernelLip_nonneg
  have hx0 : x₀ ∈ Metric.ball x₀ δ := Metric.mem_ball_self hδ
  have hdx : ‖x - x₀‖ ≤ δ := by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hx).le
  have hdx' : ‖x' - x₀‖ ≤ δ := by rw [← dist_eq_norm]; exact (Metric.mem_ball.mp hx').le
  have hc := fun w => integrable_bpz_cut_part hρm hk₁ hρ0 hk₁0 hI₁ (r := r) (γ := γ) w
  have hl := fun w (hw : w ∈ Metric.ball x₀ δ) =>
    integrable_bpz_lim_part (γ := γ) hρm hk₂ hρ1 hk₂0 hI₂ hδ hδr hsep hw
  -- pointwise bounds
  have hcut_low : ∀ y, Real.exp (-(L * δ)) * (ρ y * k₁ y * bpzCutRootKernel γ r x₀ y) ≤
      ρ y * k₁ y * bpzCutRootKernel γ r x y := by
    intro y
    have h := bpz_ratio_lower' hL (bpzCutRootKernel_pos γ r x y) (bpzCutRootKernel_pos γ r x₀ y)
      (bpz_cut_log_le (δ := δ) x x₀ y) hdx
    have hw : 0 ≤ ρ y * k₁ y := mul_nonneg (hρ0 y) (hk₁0 y)
    linarith only [mul_le_mul_of_nonneg_left h hw]
  have hlim_low : ∀ y, Real.exp (-(L * δ)) * ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x₀ y) ≤
      (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y := by
    intro y
    rcases lt_or_eq_of_le (hρ1 y) with hy | hy
    · have h := bpz_ratio_lower' hL (bpzLimRootKernel_pos γ r x y)
        (bpzLimRootKernel_pos γ r x₀ y)
        (bpz_lim_log_le hδ hδr (bpz_sep_ball hsep hx hy) (bpz_sep_ball hsep hx0 hy)) hdx
      have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (by linarith) (hk₂0 y)
      linarith only [mul_le_mul_of_nonneg_left h hw]
    · rw [hy]; simp
  have hcut_lip : ∀ y, |ρ y * k₁ y * bpzCutRootKernel γ r x y -
      ρ y * k₁ y * bpzCutRootKernel γ r x' y| ≤
        L * Real.exp (L * δ) * (ρ y * k₁ y * bpzCutRootKernel γ r x₀ y) * ‖x - x'‖ := by
    intro y
    have h := bpz_ratio_lipschitz' hL (bpzCutRootKernel_pos γ r x y)
      (bpzCutRootKernel_pos γ r x' y) (bpzCutRootKernel_pos γ r x₀ y)
      (bpz_cut_log_le (δ := δ) x x₀ y) (bpz_cut_log_le (δ := δ) x' x₀ y)
      (bpz_cut_log_le (δ := δ) x x' y) hdx hdx'
    have hw : 0 ≤ ρ y * k₁ y := mul_nonneg (hρ0 y) (hk₁0 y)
    rw [← mul_sub, abs_mul, abs_of_nonneg hw]
    calc ρ y * k₁ y * |bpzCutRootKernel γ r x y - bpzCutRootKernel γ r x' y|
        ≤ ρ y * k₁ y * (L * Real.exp (L * δ) * bpzCutRootKernel γ r x₀ y * ‖x - x'‖) :=
          mul_le_mul_of_nonneg_left h hw
      _ = _ := by ring
  have hlim_lip : ∀ y, |(1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y -
      (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x' y| ≤
        L * Real.exp (L * δ) * ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x₀ y) * ‖x - x'‖ := by
    intro y
    rcases lt_or_eq_of_le (hρ1 y) with hy | hy
    · have h := bpz_ratio_lipschitz' hL (bpzLimRootKernel_pos γ r x y)
        (bpzLimRootKernel_pos γ r x' y) (bpzLimRootKernel_pos γ r x₀ y)
        (bpz_lim_log_le hδ hδr (bpz_sep_ball hsep hx hy) (bpz_sep_ball hsep hx0 hy))
        (bpz_lim_log_le hδ hδr (bpz_sep_ball hsep hx' hy) (bpz_sep_ball hsep hx0 hy))
        (bpz_lim_log_le hδ hδr (bpz_sep_ball hsep hx hy) (bpz_sep_ball hsep hx' hy)) hdx hdx'
      have hw : 0 ≤ (1 - ρ y) * k₂ y := mul_nonneg (by linarith) (hk₂0 y)
      rw [← mul_sub, abs_mul, abs_of_nonneg hw]
      calc (1 - ρ y) * k₂ y * |bpzLimRootKernel γ r x y - bpzLimRootKernel γ r x' y|
          ≤ (1 - ρ y) * k₂ y * (L * Real.exp (L * δ) * bpzLimRootKernel γ r x₀ y * ‖x - x'‖) :=
            mul_le_mul_of_nonneg_left h hw
        _ = _ := by ring
    · rw [hy]; simp
  constructor
  · unfold bpzRootedMixedReal
    rw [mul_add, ← integral_const_mul, ← integral_const_mul]
    exact add_le_add (integral_mono ((hc x₀).const_mul _) (hc x) hcut_low)
      (integral_mono ((hl x₀ hx0).const_mul _) (hl x hx) hlim_low)
  · unfold bpzRootedMixedReal
    rw [show ∀ a b c d : ℝ, a + b - (c + d) = (a - c) + (b - d) by intros; ring,
      ← integral_sub (hc x) (hc x'), ← integral_sub (hl x hx) (hl x' hx')]
    calc |∫ y, (ρ y * k₁ y * bpzCutRootKernel γ r x y - ρ y * k₁ y * bpzCutRootKernel γ r x' y)
          ∂m₁ + ∫ y, ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y -
            (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x' y) ∂m₂|
        ≤ |∫ y, (ρ y * k₁ y * bpzCutRootKernel γ r x y -
            ρ y * k₁ y * bpzCutRootKernel γ r x' y) ∂m₁| +
          |∫ y, ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y -
            (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x' y) ∂m₂| := abs_add_le _ _
      _ ≤ ∫ y, L * Real.exp (L * δ) * (ρ y * k₁ y * bpzCutRootKernel γ r x₀ y) * ‖x - x'‖ ∂m₁ +
          ∫ y, L * Real.exp (L * δ) * ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x₀ y) *
            ‖x - x'‖ ∂m₂ := by
          gcongr
          · exact (abs_integral_le_integral_abs).trans (integral_mono ((hc x).sub (hc x')).abs
              (((hc x₀).const_mul _).mul_const _) hcut_lip)
          · exact (abs_integral_le_integral_abs).trans (integral_mono
              ((hl x hx).sub (hl x' hx')).abs (((hl x₀ hx0).const_mul _).mul_const _) hlim_lip)
      _ = _ := by
          rw [integral_mul_const, integral_mul_const, integral_const_mul, integral_const_mul]
          ring

end Integrated

/-- Mean value bound for negative powers. -/
theorem bpz_abs_rpow_neg_sub_le {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 ≤ q) :
    |a ^ (-q) - b ^ (-q)| ≤ q * (min a b) ^ (-q - 1) * |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · rw [abs_sub_comm, min_comm, abs_sub_comm a b]
    exact this hb ha (le_of_not_ge hab)
  rw [min_eq_left hab]
  rcases hab.eq_or_lt with h | h
  · subst h; simp
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-q)) (Set.Icc a b) :=
    fun t ht => (Real.continuousAt_rpow_const t (-q) (Or.inl (lt_of_lt_of_le ha ht.1).ne')
      ).continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt (fun t : ℝ => t ^ (-q)) (-q * t ^ (-q - 1)) t :=
    fun t ht => Real.hasDerivAt_rpow_const (Or.inl (lt_trans ha ht.1).ne')
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => t ^ (-q))
    (fun t => -q * t ^ (-q - 1)) h hcont hderiv
  have hc0 : 0 < c := lt_trans ha hc.1
  have hdiff : a ^ (-q) - b ^ (-q) = q * c ^ (-q - 1) * (b - a) := by
    have hba : b - a ≠ 0 := (sub_pos.mpr h).ne'
    field_simp at hcd
    linarith
  rw [hdiff, abs_of_nonneg (mul_nonneg (mul_nonneg hq (Real.rpow_nonneg hc0.le _))
    (sub_pos.mpr h).le), abs_sub_comm, abs_of_pos (sub_pos.mpr h)]
  apply mul_le_mul_of_nonneg_right _ (sub_pos.mpr h).le
  apply mul_le_mul_of_nonneg_left _ hq
  exact Real.rpow_le_rpow_of_nonpos ha hc.1.le (by linarith)

/-- The line derivative of the rooted moment, for abstract random measures. -/
theorem hasDerivAt_bpz_rooted_moment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ r δ q : ℝ} {ρ k₁ k₂ : ℂ → ℝ} {m₁ m₂ : Ω → Measure ℂ} {x₀ v : ℂ}
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (hq : 0 ≤ q) (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ)
    (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖)
    (hI₁ : ∀ᵐ ω ∂P, Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) (m₁ ω))
    (hI₂ : ∀ᵐ ω ∂P, Integrable (fun y => (1 - ρ y) * k₂ y) (m₂ ω))
    (hatom : ∀ᵐ ω ∂P, m₁ ω {x₀} = 0)
    (hpos : ∀ᵐ ω ∂P, 0 < bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω))
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun ω => bpzRootedMixedReal γ r ρ k₁ k₂ (x₀ + t • v) (m₁ ω) (m₂ ω)) P)
    (hmeasD : AEStronglyMeasurable
      (fun ω => bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω) v) P)
    (hint : Integrable (fun ω => bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω) ^ (-q)) P) :
    HasDerivAt
      (fun t : ℝ => ∫ ω, bpzRootedMixedReal γ r ρ k₁ k₂ (x₀ + t • v) (m₁ ω) (m₂ ω) ^ (-q) ∂P)
      (∫ ω, -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω) ^ (-q - 1) *
        bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω) v ∂P) 0 := by
  set L := bpzKernelLip γ r δ with hLdef
  have hL : 0 ≤ L := bpzKernelLip_nonneg
  set J : ℂ → Ω → ℝ := fun x ω => bpzRootedMixedReal γ r ρ k₁ k₂ x (m₁ ω) (m₂ ω) with hJ
  set ε : ℝ := δ / (‖v‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  have hball : ∀ t : ℝ, t ∈ Metric.ball (0 : ℝ) ε → x₀ + t • v ∈ Metric.ball x₀ δ := by
    intro t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |t| * ‖v‖ < ε * (‖v‖ + 1) := by
          rcases eq_or_ne (‖v‖) 0 with hv | hv
          · rw [hv, mul_zero]; positivity
          · linarith only [mul_le_mul_of_nonneg_right ht.le (norm_nonneg v), hε0]
      _ = δ := by rw [hε]; field_simp
  set C : ℝ := q * Real.exp (L * δ * (q + 1)) * (L * Real.exp (L * δ)) * ‖v‖ with hC
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (mul_nonneg hq (Real.exp_pos _).le)
    (mul_nonneg hL (Real.exp_pos _).le)) (norm_nonneg v)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (x₀ := (0 : ℝ))
    (s := Metric.ball (0 : ℝ) ε)
    (F := fun t ω => J (x₀ + t • v) ω ^ (-q))
    (F' := fun ω => -q * J x₀ ω ^ (-q - 1) * bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω) v)
    (bound := fun ω => C * J x₀ ω ^ (-q)) (Metric.ball_mem_nhds 0 hε0)
    (Eventually.of_forall fun t => by
      have := hmeas t
      exact (this.aemeasurable.pow_const (-q)).aestronglyMeasurable)
    (by simpa [zero_smul, add_zero] using hint)
    (by
      have h1 : AEStronglyMeasurable (fun ω => J x₀ ω ^ (-q - 1)) P := by
        have := hmeas 0
        simp only [zero_smul, add_zero] at this
        exact (this.aemeasurable.pow_const _).aestronglyMeasurable
      exact (h1.const_mul (-q)).mul hmeasD)
    (by
      filter_upwards [hI₁, hI₂, hpos] with ω hω₁ hω₂ hω₀
      refine LipschitzOnWith.of_dist_le_mul fun t ht t' ht' => ?_
      have hx := hball t ht
      have hx' := hball t' ht'
      obtain ⟨hlow, -⟩ := bpzRootedMixedReal_ratio hρm hk₁ hk₂ hρ0 hρ1 hk₁0 hk₂0 hω₁ hω₂
        hδ hδr hsep hx hx
      obtain ⟨hlow', -⟩ := bpzRootedMixedReal_ratio hρm hk₁ hk₂ hρ0 hρ1 hk₁0 hk₂0 hω₁ hω₂
        hδ hδr hsep hx' hx'
      obtain ⟨-, hlip⟩ := bpzRootedMixedReal_ratio hρm hk₁ hk₂ hρ0 hρ1 hk₁0 hk₂0 hω₁ hω₂
        hδ hδr hsep hx hx'
      have hJ0 : 0 < J x₀ ω := hω₀
      have ha : 0 < J (x₀ + t • v) ω := lt_of_lt_of_le (by positivity) hlow
      have hb : 0 < J (x₀ + t' • v) ω := lt_of_lt_of_le (by positivity) hlow'
      have hmin : Real.exp (-(L * δ)) * J x₀ ω ≤ min (J (x₀ + t • v) ω) (J (x₀ + t' • v) ω) :=
        le_min hlow hlow'
      rw [Real.dist_eq, Real.dist_eq, Real.coe_nnabs,
        abs_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hJ0.le _))]
      have hmv := bpz_abs_rpow_neg_sub_le ha hb hq
      have hpow : (min (J (x₀ + t • v) ω) (J (x₀ + t' • v) ω)) ^ (-q - 1) ≤
          (Real.exp (-(L * δ)) * J x₀ ω) ^ (-q - 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hmin (by linarith)
      have hsplit : (Real.exp (-(L * δ)) * J x₀ ω) ^ (-q - 1) =
          Real.exp (L * δ * (q + 1)) * J x₀ ω ^ (-q - 1) := by
        rw [Real.mul_rpow (Real.exp_pos _).le hJ0.le, ← Real.exp_mul]
        congr 2
        ring
      have hdist : ‖x₀ + t • v - (x₀ + t' • v)‖ = |t - t'| * ‖v‖ := by
        rw [show x₀ + t • v - (x₀ + t' • v) = (t - t') • v by rw [sub_smul]; ring, norm_smul,
          Real.norm_eq_abs]
      rw [hdist] at hlip
      have hJq : J x₀ ω ^ (-q - 1) * J x₀ ω = J x₀ ω ^ (-q) := by
        rw [← Real.rpow_add_one hJ0.ne']
        ring_nf
      calc |J (x₀ + t • v) ω ^ (-q) - J (x₀ + t' • v) ω ^ (-q)|
          ≤ q * (min (J (x₀ + t • v) ω) (J (x₀ + t' • v) ω)) ^ (-q - 1) *
              |J (x₀ + t • v) ω - J (x₀ + t' • v) ω| := hmv
        _ ≤ q * (Real.exp (L * δ * (q + 1)) * J x₀ ω ^ (-q - 1)) *
              (L * Real.exp (L * δ) * J x₀ ω * (|t - t'| * ‖v‖)) := by
            rw [← hsplit]
            gcongr
        _ = C * J x₀ ω ^ (-q) * |t - t'| := by
            rw [hC, ← hJq]
            ring)
    (hint.const_mul C)
    (by
      filter_upwards [hI₁, hI₂, hatom, hpos] with ω hω₁ hω₂ hωa hω₀
      have hJd := hasFDerivAt_bpzRootedMixedReal hρm hk₁ hk₂ hρ0 hρ1 hk₁0 hk₂0 hω₁ hω₂ hωa hδ
        hδr hsep
      have hline : HasDerivAt (fun t : ℝ => x₀ + t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀
      have hcomp := hJd.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
      have hne : ((fun x => bpzRootedMixedReal γ r ρ k₁ k₂ x (m₁ ω) (m₂ ω)) ∘
          fun t : ℝ => x₀ + t • v) 0 ≠ 0 := by
        simpa [Function.comp_def] using hω₀.ne'
      have hrpow := hcomp.rpow_const (p := -q) (Or.inl hne)
      refine hrpow.congr_deriv ?_
      show (bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω)) v * -q *
          bpzRootedMixedReal γ r ρ k₁ k₂ (x₀ + (0 : ℝ) • v) (m₁ ω) (m₂ ω) ^ (-q - 1) =
        -q * bpzRootedMixedReal γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω) ^ (-q - 1) *
          (bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ (m₁ ω) (m₂ ω)) v
      rw [zero_smul, add_zero]
      ring)
  exact hmain.2

end DOZZ.Proofs
