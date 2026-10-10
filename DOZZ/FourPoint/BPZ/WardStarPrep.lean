/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardPsi

/-! # Real mixed masses and their tilts

The real mixed mass and the untilted root-derivative functional, their measurability as functions
of the two measures, and the factorization of their tilts at a root. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The real mixed mass `∫ ρ k₁ dm₁ + ∫ (1 - ρ) k₂ dm₂`. -/
noncomputable def bpzMixedReal (ρ k₁ k₂ : ℂ → ℝ) (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y ∂m₁ + ∫ y, (1 - ρ y) * k₂ y ∂m₂

/-- The untilted root-derivative functional in a real direction `v`. -/
noncomputable def bpzMixedDerivReal (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x v : ℂ)
    (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y * (γ ^ 2 * bpzLamDeriv r (x - y) v) ∂m₁ +
    ∫ y, (1 - ρ y) * k₂ y * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v) ∂m₂

/-- The Bochner integral of a fixed measurable function is measurable in the measure. -/
theorem measurable_integral_measure {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable (fun m : Measure ℂ => ∫ y, g y ∂m) := by
  set A : Set (Measure ℂ) := {m | ∫⁻ y, ENNReal.ofReal |g y| ∂m < ⊤} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp hg))) measurable_const
  have heq : (fun m : Measure ℂ => ∫ y, g y ∂m) = A.indicator (fun m =>
      (∫⁻ y, ENNReal.ofReal (g y) ∂m).toReal - (∫⁻ y, ENNReal.ofReal (-g y) ∂m).toReal) := by
    funext m
    by_cases hm : m ∈ A
    · rw [Set.indicator_of_mem hm]
      have hI : Integrable g m := by
        refine ⟨hg.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_norm]
        have hm' : ∫⁻ y, ENNReal.ofReal |g y| ∂m < ⊤ := hm
        simpa only [Real.norm_eq_abs] using hm'
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI
    · rw [Set.indicator_of_notMem hm]
      apply integral_undef
      intro hI
      apply hm
      have := hI.2
      rw [hasFiniteIntegral_iff_norm] at this
      show ∫⁻ y, ENNReal.ofReal |g y| ∂m < ⊤
      simpa only [Real.norm_eq_abs] using this
  rw [heq]
  refine Measurable.indicator ?_ hAm
  exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg)).ennreal_toReal).sub
    ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg.neg)).ennreal_toReal)

theorem measurable_bpzMixedReal {ρ k₁ k₂ : ℂ → ℝ} (hρm : Measurable ρ) (hk₁ : Measurable k₁)
    (hk₂ : Measurable k₂) :
    Measurable (fun q : Measure ℂ × Measure ℂ => bpzMixedReal ρ k₁ k₂ q.1 q.2) :=
  ((measurable_integral_measure (hρm.mul hk₁)).comp measurable_fst).add
    ((measurable_integral_measure ((measurable_const.sub hρm).mul hk₂)).comp measurable_snd)

theorem measurable_bpzMixedDerivReal {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρm : Measurable ρ)
    (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) (x v : ℂ) :
    Measurable (fun q : Measure ℂ × Measure ℂ => bpzMixedDerivReal γ r ρ k₁ k₂ x v q.1 q.2) := by
  have h1 : Measurable fun y => ρ y * k₁ y * (γ ^ 2 * bpzLamDeriv r (x - y) v) :=
    (hρm.mul hk₁).mul (measurable_const.mul ((ContinuousLinearMap.apply ℝ ℝ v).continuous
      |>.measurable.comp ((measurable_bpzLamDeriv r).comp (measurable_const.sub measurable_id))))
  have h2 : Measurable fun y => (1 - ρ y) * k₂ y * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v) :=
    ((measurable_const.sub hρm).mul hk₂).mul (measurable_const.mul
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp
        ((measurable_bpzTruncLogDeriv r).comp (measurable_const.sub measurable_id))))
  exact ((measurable_integral_measure h1).comp measurable_fst).add
    ((measurable_integral_measure h2).comp measurable_snd)

/-- Tilting the real mixed mass at a root factors out the root pinning. -/
theorem bpzMixedReal_tilt (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x : ℂ) (m₁ m₂ : Measure ℂ) :
    bpzMixedReal ρ k₁ k₂ (m₁.withDensity (bpzCutRootDensity γ r x))
        (m₂.withDensity (bpzLimRootDensity γ r x)) =
      Real.exp (γ ^ 2 * bpzPin r x) * bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ := by
  unfold bpzMixedReal bpzRootedMixedReal
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_bpzCutRootDensity γ r x)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (measurable_bpzLimRootDensity γ r x)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top), mul_add,
    ← integral_const_mul, ← integral_const_mul]
  congr 1
  · congr 1
    funext y
    simp only [bpzCutRootDensity, bpzCutRootKernel, smul_eq_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [show γ ^ 2 * (bpzLam r (x - y) + bpzPin r x + bpzPin r y) =
      γ ^ 2 * bpzPin r x + γ ^ 2 * (bpzLam r (x - y) + bpzPin r y) by ring, Real.exp_add]
    ring
  · congr 1
    funext y
    simp only [bpzLimRootDensity, bpzLimRootKernel, smul_eq_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [show γ ^ 2 * (bpzTruncLog r (x - y) + bpzPin r x + Real.log (normPlus y)) =
      γ ^ 2 * bpzPin r x + γ ^ 2 * (bpzTruncLog r (x - y) + Real.log (normPlus y)) by ring,
      Real.exp_add]
    ring

/-- The scalar root derivative of the rooted mixed mass in a direction `v`. -/
noncomputable def bpzRootedMixedDerivApply (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x v : ℂ)
    (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) * bpzLamDeriv r (x - y) v ∂m₁ +
    ∫ y, (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) *
      bpzTruncLogDeriv r (x - y) v ∂m₂

/-- Tilting the untilted root-derivative functional factors out the root pinning. -/
theorem bpzMixedDerivReal_tilt (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x v : ℂ) (m₁ m₂ : Measure ℂ) :
    bpzMixedDerivReal γ r ρ k₁ k₂ x v (m₁.withDensity (bpzCutRootDensity γ r x))
        (m₂.withDensity (bpzLimRootDensity γ r x)) =
      Real.exp (γ ^ 2 * bpzPin r x) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v m₁ m₂ := by
  unfold bpzMixedDerivReal bpzRootedMixedDerivApply
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_bpzCutRootDensity γ r x)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul (measurable_bpzLimRootDensity γ r x)
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top), mul_add,
    ← integral_const_mul, ← integral_const_mul]
  congr 1
  · congr 1
    funext y
    simp only [bpzCutRootDensity, bpzCutRootKernel, smul_eq_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [show γ ^ 2 * (bpzLam r (x - y) + bpzPin r x + bpzPin r y) =
      γ ^ 2 * bpzPin r x + γ ^ 2 * (bpzLam r (x - y) + bpzPin r y) by ring, Real.exp_add]
    ring
  · congr 1
    funext y
    simp only [bpzLimRootDensity, bpzLimRootKernel, smul_eq_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
    rw [show γ ^ 2 * (bpzTruncLog r (x - y) + bpzPin r x + Real.log (normPlus y)) =
      γ ^ 2 * bpzPin r x + γ ^ 2 * (bpzTruncLog r (x - y) + Real.log (normPlus y)) by ring,
      Real.exp_add]
    ring

/-- The operator derivative applied to a direction is the scalar derivative. -/
theorem bpzRootedMixedDeriv_apply {γ r δ : ℝ} {ρ k₁ k₂ : ℂ → ℝ} {m₁ m₂ : Measure ℂ} {x₀ : ℂ}
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (hI₁ : Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) m₁)
    (hI₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖) (v : ℂ) :
    bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ m₁ m₂ v =
      bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v m₁ m₂ := by
  have hc := integrable_bpz_cut_part (γ := γ) hρm hk₁ hρ0 hk₁0 hI₁ x₀
  have hl := integrable_bpz_lim_part (γ := γ) hρm hk₂ hρ1 hk₂0 hI₂ hδ hδr hsep
    (Metric.mem_ball_self hδ)
  have hcI : Integrable (fun y => (ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2)) •
      bpzLamDeriv r (x₀ - y)) m₁ := by
    refine ((hc.mul_const (γ ^ 2 * Real.exp r))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact (((hρm.mul hk₁).mul ((continuous_bpzCutRootKernel_snd γ r x₀).measurable.mul_const
        _)).smul ((measurable_bpzLamDeriv r).comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
    · have hw : 0 ≤ ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2) :=
        mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y))
          (mul_nonneg (bpzCutRootKernel_pos γ r x₀ y).le (sq_nonneg γ))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      calc ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2) * ‖bpzLamDeriv r (x₀ - y)‖
          ≤ ρ y * k₁ y * (bpzCutRootKernel γ r x₀ y * γ ^ 2) * Real.exp r :=
            mul_le_mul_of_nonneg_left (norm_bpzLamDeriv_le_exp r _) hw
        _ = _ := by ring
  have hlI : Integrable (fun y => ((1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2)) •
      bpzTruncLogDeriv r (x₀ - y)) m₂ := by
    refine ((hl.mul_const (γ ^ 2 * Real.exp r))).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((((measurable_const.sub hρm).mul hk₂).mul
        ((continuous_bpzLimRootKernel_snd γ r x₀).measurable.mul_const _)).smul
          ((measurable_bpzTruncLogDeriv r).comp
            (measurable_const.sub measurable_id))).aestronglyMeasurable
    · have hw : 0 ≤ (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2) :=
        mul_nonneg (mul_nonneg (by linarith [hρ1 y]) (hk₂0 y))
          (mul_nonneg (bpzLimRootKernel_pos γ r x₀ y).le (sq_nonneg γ))
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      calc (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2) *
            ‖bpzTruncLogDeriv r (x₀ - y)‖
          ≤ (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x₀ y * γ ^ 2) * Real.exp r :=
            mul_le_mul_of_nonneg_left (norm_bpzTruncLogDeriv_le r _).1 hw
        _ = _ := by ring
  unfold bpzRootedMixedDeriv bpzRootedMixedDerivApply
  rw [add_apply, ContinuousLinearMap.integral_apply hcI,
    ContinuousLinearMap.integral_apply hlI]
  simp only [smul_apply, smul_eq_mul]

/-- Parametric integrals against a measurable family of finite measures are jointly
measurable. -/
theorem measurable_integral_finite_family {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : α → Measure ℂ) (hm : Measurable m) (hfin : ∀ a, IsFiniteMeasure (m a))
    (g : β → ℂ → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : α × β => ∫ y, g p.2 y ∂m p.1) := by
  set c : α → ℝ≥0∞ := fun a => m a Set.univ + 1 with hc
  have hcm : Measurable c :=
    (Measure.measurable_coe MeasurableSet.univ |>.comp hm).add measurable_const
  have hc0 : ∀ a, c a ≠ 0 := fun a => by simp [hc]
  have hctop : ∀ a, c a ≠ ⊤ := fun a => by
    simp only [hc, ne_eq, ENNReal.add_eq_top, ENNReal.one_ne_top, or_false]
    exact measure_ne_top _ _
  have hnm : Measurable (fun p : α × β => (c p.1)⁻¹ • m p.1) := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ((hcm.comp measurable_fst).inv).mul
      ((Measure.measurable_coe hs).comp (hm.comp measurable_fst))
  let κ : ProbabilityTheory.Kernel (α × β) ℂ := ⟨fun p => (c p.1)⁻¹ • m p.1, hnm⟩
  have hκfin : ProbabilityTheory.IsFiniteKernel κ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun p => ?_⟩⟩
    change ((c p.1)⁻¹ • m p.1) Set.univ ≤ 1
    rw [Measure.smul_apply, smul_eq_mul]
    calc (c p.1)⁻¹ * m p.1 Set.univ ≤ (c p.1)⁻¹ * c p.1 := by
          gcongr
          simp [hc]
      _ = 1 := ENNReal.inv_mul_cancel (hc0 _) (hctop _)
  have hint : StronglyMeasurable fun p : α × β => ∫ y, g p.2 y ∂κ p :=
    StronglyMeasurable.integral_kernel_prod_right (κ := κ) (f := fun p y => g p.2 y)
      ((hg.comp (measurable_fst.snd.prodMk measurable_snd)).stronglyMeasurable)
  have heq : (fun p : α × β => ∫ y, g p.2 y ∂m p.1) =
      fun p => (c p.1).toReal * ∫ y, g p.2 y ∂κ p := by
    funext p
    change _ = (c p.1).toReal * ∫ y, g p.2 y ∂((c p.1)⁻¹ • m p.1)
    rw [integral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.toReal_mul,
      ENNReal.mul_inv_cancel (hc0 _) (hctop _), ENNReal.toReal_one, one_mul]
  rw [heq]
  exact (hcm.comp measurable_fst).ennreal_toReal.mul hint.measurable

end DOZZ.Proofs
