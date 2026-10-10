/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardPsiKernel

/-! # The pathwise root derivative of the rooted mixed mass

For fixed measures, the rooted mixed mass is differentiable in its root at every point kept at
distance `2δ` from the limit region, provided the cutoff measure has no atom at the root. The
derivative is the integral of the kernel derivatives. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The rooted mixed mass as a real number. -/
noncomputable def bpzRootedMixedReal (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x : ℂ)
    (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y * bpzCutRootKernel γ r x y ∂m₁ +
    ∫ y, (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y ∂m₂

/-- The root derivative of the rooted mixed mass. -/
noncomputable def bpzRootedMixedDeriv (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x : ℂ)
    (m₁ m₂ : Measure ℂ) : ℂ →L[ℝ] ℝ :=
  ∫ y, (ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2)) • bpzLamDeriv r (x - y) ∂m₁ +
    ∫ y, ((1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2)) •
      bpzTruncLogDeriv r (x - y) ∂m₂

theorem measurable_bpzLamDeriv (r : ℝ) : Measurable (bpzLamDeriv r) := by
  have hjoint : Measurable (fun p : ℂ × ℝ =>
      bpzTruncLogDeriv r (p.1 + Real.exp (-r) * Complex.exp (p.2 * Complex.I))) :=
    (measurable_bpzTruncLogDeriv r).comp (measurable_fst.add (measurable_const.mul
      (Complex.measurable_exp.comp (Complex.measurable_ofReal.comp measurable_snd |>.mul
        measurable_const))))
  have hint : StronglyMeasurable (fun w : ℂ => ∫ θ in Set.Ioc 0 (2 * Real.pi),
      bpzTruncLogDeriv r (w + Real.exp (-r) * Complex.exp (θ * Complex.I))) :=
    StronglyMeasurable.integral_prod_right' (ν := (volume.restrict (Set.Ioc 0 (2 * Real.pi))))
      hjoint.stronglyMeasurable
  have heq : bpzLamDeriv r = fun w => (2 * Real.pi)⁻¹ • ∫ θ in Set.Ioc 0 (2 * Real.pi),
      bpzTruncLogDeriv r (w + Real.exp (-r) * Complex.exp (θ * Complex.I)) := by
    funext w
    rw [bpzLamDeriv, intervalIntegral.integral_of_le (by positivity)]
  rw [heq]
  exact hint.measurable.const_smul ((2 * Real.pi)⁻¹ : ℝ)

theorem continuous_bpzCutRootKernel_snd (γ r : ℝ) (x : ℂ) :
    Continuous (bpzCutRootKernel γ r x) := by
  unfold bpzCutRootKernel
  exact Real.continuous_exp.comp (continuous_const.mul
    (((continuous_bpzLam r).comp (continuous_const.sub continuous_id)).add
      (continuous_bpzPin r)))

theorem continuous_bpzLimRootKernel_snd (γ r : ℝ) (x : ℂ) :
    Continuous (bpzLimRootKernel γ r x) := by
  unfold bpzLimRootKernel
  refine Real.continuous_exp.comp (continuous_const.mul
    (((continuous_bpzTruncLog r).comp (continuous_const.sub continuous_id)).add ?_))
  exact Real.continuousOn_log.comp_continuous bpz_continuous_normPlus
    fun y => (bpz_normPlus_pos y).ne'

theorem bpzCutRootKernel_le (γ r : ℝ) (x y : ℂ) :
    bpzCutRootKernel γ r x y ≤ Real.exp (γ ^ 2 * r) * Real.exp (γ ^ 2 * bpzPin r y) := by
  unfold bpzCutRootKernel
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := bpzLam_le r (x - y)
  have hγ := sq_nonneg γ
  nlinarith

/-- The cutoff part of the rooted mixed mass is differentiable at a non-atom. -/
theorem hasFDerivAt_bpz_cut_part {γ r : ℝ} {ρ k₁ : ℂ → ℝ} {m₁ : Measure ℂ} {x₀ : ℂ}
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hρ0 : ∀ y, 0 ≤ ρ y) (hk₁0 : ∀ y, 0 ≤ k₁ y)
    (hI₁ : Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) m₁)
    (hatom : m₁ {x₀} = 0) :
    HasFDerivAt (fun x => ∫ y, ρ y * k₁ y * bpzCutRootKernel γ r x y ∂m₁)
      (∫ y, (ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2)) • bpzLamDeriv r (x₀ - y) ∂m₁)
      x₀ := by
  set C : ℝ := γ ^ 2 * Real.exp (γ ^ 2 * r) * Real.exp r with hC
  have hC0 : 0 ≤ C := by positivity
  have hw : ∀ y, 0 ≤ ρ y * k₁ y := fun y => mul_nonneg (hρ0 y) (hk₁0 y)
  have hmeasF : ∀ x, Measurable fun y => ρ y * k₁ y * bpzCutRootKernel γ r x y :=
    fun x => (hρm.mul hk₁).mul (continuous_bpzCutRootKernel_snd γ r x).measurable
  have hmeasF' : Measurable fun y =>
      (ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2)) • bpzLamDeriv r (x₀ - y) :=
    ((hρm.mul hk₁).mul ((continuous_bpzCutRootKernel_snd γ r x₀).measurable.mul_const _)).smul
      ((measurable_bpzLamDeriv r).comp (measurable_const.sub measurable_id))
  have hint₀ : Integrable (fun y => ρ y * k₁ y * bpzCutRootKernel γ r x₀ y) m₁ := by
    refine (hI₁.mul_const (Real.exp (γ ^ 2 * r))).mono' (hmeasF x₀).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw y) (bpzCutRootKernel_pos γ r x₀ y).le)]
    calc ρ y * k₁ y * bpzCutRootKernel γ r x₀ y
        ≤ ρ y * k₁ y * (Real.exp (γ ^ 2 * r) * Real.exp (γ ^ 2 * bpzPin r y)) :=
          mul_le_mul_of_nonneg_left (bpzCutRootKernel_le γ r x₀ y) (hw y)
      _ = _ := by ring
  have hnot : ∀ᵐ y ∂m₁, y ≠ x₀ := by
    apply ae_iff.mpr; simpa using hatom
  have hmain := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := m₁) (s := Set.univ)
    (x₀ := x₀) (F := fun x y => ρ y * k₁ y * bpzCutRootKernel γ r x y)
    (F' := fun y => (ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2)) •
      bpzLamDeriv r (x₀ - y))
    (bound := fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y) * C) Filter.univ_mem
    (Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable) hint₀
    hmeasF'.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      refine LipschitzOnWith.of_dist_le_mul fun x _ x' _ => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_nnabs,
        abs_of_nonneg (mul_nonneg (mul_nonneg (hw y) (Real.exp_pos _).le) hC0)]
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw y)]
      calc ρ y * k₁ y * |bpzCutRootKernel γ r x y - bpzCutRootKernel γ r x' y|
          ≤ ρ y * k₁ y * (γ ^ 2 * Real.exp (γ ^ 2 * r) * Real.exp (γ ^ 2 * bpzPin r y) *
            Real.exp r * ‖x - x'‖) :=
            mul_le_mul_of_nonneg_left (abs_bpzCutRootKernel_sub_le γ r x x' y) (hw y)
        _ = ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y) * C * ‖x - x'‖ := by rw [hC]; ring)
    (hI₁.mul_const C)
    (by
      filter_upwards [hnot] with y hy
      have h := (hasFDerivAt_bpzCutRootKernel γ r hy.symm).const_mul (ρ y * k₁ y)
      simpa [smul_smul, mul_assoc] using h)
  exact hmain.2

/-- The limit part of the rooted mixed mass is differentiable at a root separated from the
limit region. -/
theorem hasFDerivAt_bpz_lim_part {γ r δ : ℝ} {ρ k₂ : ℂ → ℝ} {m₂ : Measure ℂ} {x₀ : ℂ}
    (hρm : Measurable ρ) (hk₂ : Measurable k₂) (hρ1 : ∀ y, ρ y ≤ 1) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (hI₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖) :
    HasFDerivAt (fun x => ∫ y, (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y ∂m₂)
      (∫ y, ((1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2)) •
        bpzTruncLogDeriv r (x₀ - y) ∂m₂) x₀ := by
  set R : ℝ := ‖x₀‖ + δ with hR
  set B : ℝ := (1 + (1 + R) / δ) ^ (γ ^ 2) with hB
  have hR0 : 0 ≤ R := by positivity
  have hB0 : 0 ≤ B := Real.rpow_nonneg (by positivity) _
  have hw : ∀ y, 0 ≤ (1 - ρ y) * k₂ y := fun y => mul_nonneg (by linarith [hρ1 y]) (hk₂0 y)
  have hball : ∀ x ∈ Metric.ball x₀ δ, ∀ y, ρ y < 1 → ‖x‖ ≤ R ∧ δ ≤ ‖x - y‖ := by
    intro x hx y hy
    rw [Metric.mem_ball, dist_eq_norm] at hx
    refine ⟨?_, ?_⟩
    · have := norm_le_norm_add_norm_sub' x x₀
      rw [hR]; linarith
    · have h1 := hsep y hy
      have h2 := norm_sub_norm_le (x₀ - y) (x₀ - x)
      rw [show x₀ - y - (x₀ - x) = x - y by ring, norm_sub_rev x₀ x] at h2
      linarith
  have hmeasF : ∀ x, Measurable fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y :=
    fun x => ((measurable_const.sub hρm).mul hk₂).mul
      (continuous_bpzLimRootKernel_snd γ r x).measurable
  have hmeasF' : Measurable fun y => ((1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2)) •
      bpzTruncLogDeriv r (x₀ - y) :=
    (((measurable_const.sub hρm).mul hk₂).mul
      ((continuous_bpzLimRootKernel_snd γ r x₀).measurable.mul_const _)).smul
      ((measurable_bpzTruncLogDeriv r).comp (measurable_const.sub measurable_id))
  have hint₀ : Integrable (fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x₀ y) m₂ := by
    refine (hI₂.mul_const B).mono' (hmeasF x₀).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw y) (bpzLimRootKernel_pos γ r x₀ y).le)]
    rcases lt_or_eq_of_le (hρ1 y) with hy | hy
    · have hb := hball x₀ (Metric.mem_ball_self hδ) y hy
      exact mul_le_mul_of_nonneg_left (bpzLimRootKernel_le γ r hδ hδr hb.1 hb.2) (hw y)
    · rw [hy]; simp
  have hmain := hasFDerivAt_integral_of_dominated_loc_of_lip (μ := m₂)
    (s := Metric.ball x₀ δ) (x₀ := x₀)
    (F := fun x y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y)
    (F' := fun y => ((1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2)) •
      bpzTruncLogDeriv r (x₀ - y))
    (bound := fun y => (1 - ρ y) * k₂ y * (B * (γ ^ 2 / δ))) (Metric.ball_mem_nhds x₀ hδ)
    (Eventually.of_forall fun x => (hmeasF x).aestronglyMeasurable) hint₀
    hmeasF'.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      refine LipschitzOnWith.of_dist_le_mul fun x hx x' hx' => ?_
      rw [Real.dist_eq, dist_eq_norm, Real.coe_nnabs,
        abs_of_nonneg (mul_nonneg (hw y) (by positivity))]
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw y)]
      rcases lt_or_eq_of_le (hρ1 y) with hy | hy
      · obtain ⟨hxR, hxy⟩ := hball x hx y hy
        obtain ⟨hx'R, hx'y⟩ := hball x' hx' y hy
        calc (1 - ρ y) * k₂ y * |bpzLimRootKernel γ r x y - bpzLimRootKernel γ r x' y|
            ≤ (1 - ρ y) * k₂ y * (B * (γ ^ 2 / δ) * ‖x - x'‖) :=
              mul_le_mul_of_nonneg_left
                (abs_bpzLimRootKernel_sub_le γ r hδ hδr hxR hx'R hxy hx'y) (hw y)
          _ = (1 - ρ y) * k₂ y * (B * (γ ^ 2 / δ)) * ‖x - x'‖ := by ring
      · rw [hy]; simp)
    (hI₂.mul_const _)
    (Eventually.of_forall fun y => by
      rcases lt_or_eq_of_le (hρ1 y) with hy | hy
      · have hne : ‖x₀ - y‖ ≠ Real.exp (-r) := by
          have := hsep y hy
          linarith
        have h := (hasFDerivAt_bpzLimRootKernel γ r hne).const_mul ((1 - ρ y) * k₂ y)
        simpa [smul_smul, mul_assoc] using h
      · simp only [hy, sub_self, zero_mul, zero_smul]
        exact hasFDerivAt_const 0 x₀)
  exact hmain.2

/-- The rooted mixed mass is differentiable at a root that is not an atom of the cutoff measure
and is separated from the limit region. -/
theorem hasFDerivAt_bpzRootedMixedReal {γ r δ : ℝ} {ρ k₁ k₂ : ℂ → ℝ} {m₁ m₂ : Measure ℂ}
    {x₀ : ℂ} (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂)
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (hI₁ : Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) m₁)
    (hI₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂) (hatom : m₁ {x₀} = 0)
    (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖) :
    HasFDerivAt (fun x => bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂)
      (bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ m₁ m₂) x₀ :=
  (hasFDerivAt_bpz_cut_part hρm hk₁ hρ0 hk₁0 hI₁ hatom).add
    (hasFDerivAt_bpz_lim_part hρm hk₂ hρ1 hk₂0 hI₂ hδ hδr hsep)

end DOZZ.Proofs
