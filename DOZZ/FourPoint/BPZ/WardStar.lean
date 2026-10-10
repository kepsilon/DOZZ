/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardStarPrep
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # The screening Ward identity at a circle cutoff

Fix a cutoff function `ρ`, a test function `φ` whose support is kept at distance `2δ` from the
region `{ρ < 1}`, and a real direction `v`. With the cutoff chaos on `{ρ > 0}` and the limit
chaos elsewhere, and the `|x|₊` factors of the weight replaced by the circle-averaged pinning,

  `E[Î^{-q} ∫ ∂_v(φ k̃) |x|₊⁴ e^{γ² q h_r} dM_r] = q E[Î^{-q-1} ∫ φ k₁ Ŷ_v dM_r]`,

where `Ŷ_v` integrates the `v`-derivatives of the two root kernels. The proof roots both sides at
the integration point, which turns them into `∫ ∂_v(φ k̃) Ψ` and `-∫ φ k̃ ∂_v Ψ` for the rooted
moment `Ψ = E[J^{-q}]`, and integrates by parts. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The deterministic data of the cutoff Ward identity. -/
structure BPZWardData (γ q r δ : ℝ) (ρ kt k₂ φ : ℂ → ℝ) (D : Set ℂ) : Prop where
  γ_pos : 0 < γ
  q_ge : 1 ≤ q
  r_nonneg : 0 ≤ r
  δ_pos : 0 < δ
  δ_r : Real.exp (-r) ≤ δ
  ρ_meas : Measurable ρ
  ρ_nonneg : ∀ y, 0 ≤ ρ y
  ρ_le_one : ∀ y, ρ y ≤ 1
  ρ_bdd : ∃ R : ℝ, ∀ y, R < ‖y‖ → ρ y = 0
  kt_meas : Measurable kt
  kt_nonneg : ∀ y, 0 ≤ kt y
  kt_bdd : ∃ B : ℝ, ∀ y, ρ y ≠ 0 → kt y ≤ B
  k₂_meas : Measurable k₂
  k₂_nonneg : ∀ y, 0 ≤ k₂ y
  f_C1 : ContDiff ℝ 1 (fun x => φ x * kt x)
  φ_compact : HasCompactSupport φ
  kt_pos : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ tsupport φ, c ≤ kt x
  sep : ∀ x ∈ tsupport φ, ∀ y, ρ y < 1 → 2 * δ ≤ ‖x - y‖
  D_meas : MeasurableSet D
  D_rho : ∀ y ∈ D, ρ y = 0
  D_low : ∃ c : ℝ, 0 < c ∧ ∀ y ∈ D, c ≤ k₂ y
  D_bdd : ∃ R : ℝ, ∀ y ∈ D, ‖y‖ ≤ R

/-- The cutoff-region weight with the pinning exponent `q`. -/
noncomputable def bpzWardCutWeight (γ q r : ℝ) (kt : ℂ → ℝ) (y : ℂ) : ℝ :=
  kt y * normPlus y ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r y)

/-- The left weight of the cutoff Ward identity. -/
noncomputable def bpzWardLeftWeight (γ q r : ℝ) (kt φ : ℂ → ℝ) (v x : ℂ) : ℝ :=
  fderiv ℝ (fun x => φ x * kt x) x v * normPlus x ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r x)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probabilistic setup of the cutoff Ward identity. -/
structure BPZWardProb (P : Measure Ω) (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ)
    (Xc : Ω → ℂ → ℝ → ℝ) (ρ k₂ : ℂ → ℝ) (D : Set ℂ) : Prop where
  hX : IsEquatorGFF P X
  γ2 : γ < 2
  hM : IsGMCOf P X γ M
  hMm : Measurable M
  hXc : IsCircleAverage P X Xc
  k₂_int : ∀ᵐ ω ∂P, Integrable (fun y => (1 - ρ y) * k₂ y) (M ω)
  D_neg : ∀ p : ℝ, 0 ≤ p → ∫⁻ ω, M ω D ^ (-p) ∂P < ⊤

section Bounds

variable {γ q r δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}

theorem bpzPin_le_log_normPlus_add (r : ℝ) (y : ℂ) :
    bpzPin r y ≤ Real.log (normPlus y) + Real.exp (-r) := by
  have := abs_bpzPin_sub_le r y
  have := le_abs_self (bpzPin r y - Real.log (normPlus y))
  linarith

theorem measurable_bpzWardCutWeight (hd : BPZWardData γ q r δ ρ kt k₂ φ D) :
    Measurable (bpzWardCutWeight γ q r kt) := by
  unfold bpzWardCutWeight
  exact (hd.kt_meas.mul (bpz_measurable_normPlus.pow_const _)).mul
    (Real.measurable_exp.comp ((continuous_bpzPin r).measurable.const_mul _))

theorem bpzWardCutWeight_nonneg (hd : BPZWardData γ q r δ ρ kt k₂ φ D) (y : ℂ) :
    0 ≤ bpzWardCutWeight γ q r kt y := by
  unfold bpzWardCutWeight
  have := hd.kt_nonneg y
  have := Real.rpow_nonneg (bpz_normPlus_pos y).le (4 : ℝ)
  positivity

/-- The cutoff weight is bounded on the cutoff region. -/
theorem bpzWardCutWeight_bdd (hd : BPZWardData γ q r δ ρ kt k₂ φ D) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ρ y ≠ 0 →
      bpzWardCutWeight γ q r kt y * Real.exp (γ ^ 2 * bpzPin r y) ≤ B := by
  obtain ⟨R, hR⟩ := hd.ρ_bdd
  obtain ⟨Bk, hBk⟩ := hd.kt_bdd
  have hq0 : 0 ≤ q := le_trans zero_le_one hd.q_ge
  refine ⟨max Bk 0 * (max R 0 + 1) ^ (4 : ℝ) *
      Real.exp (γ ^ 2 * (q + 1) * (Real.log (max R 0 + 1) + 1)), by positivity, ?_⟩
  intro y hy
  have hyR : ‖y‖ ≤ R := by
    by_contra h
    exact hy (hR y (lt_of_not_ge h))
  have hnp : normPlus y ≤ max R 0 + 1 := by
    unfold normPlus
    apply max_le
    · have := le_max_right R 0; linarith
    · have := le_max_left R 0; linarith
  have hpin : bpzPin r y ≤ Real.log (max R 0 + 1) + 1 := by
    have h1 := bpzPin_le_log_normPlus_add r y
    have h2 := Real.log_le_log (bpz_normPlus_pos y) hnp
    have h3 : Real.exp (-r) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith [hd.r_nonneg]
    linarith
  unfold bpzWardCutWeight
  rw [mul_assoc (kt y * normPlus y ^ (4 : ℝ)), ← Real.exp_add]
  have hγ2 : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hexp : Real.exp (γ ^ 2 * q * bpzPin r y + γ ^ 2 * bpzPin r y) ≤
      Real.exp (γ ^ 2 * (q + 1) * (Real.log (max R 0 + 1) + 1)) := by
    apply Real.exp_le_exp.mpr
    have : γ ^ 2 * q * bpzPin r y + γ ^ 2 * bpzPin r y = γ ^ 2 * (q + 1) * bpzPin r y := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hpin (by positivity)
  have hkt : kt y ≤ max Bk 0 := le_trans (hBk y hy) (le_max_left _ _)
  have hp4 : normPlus y ^ (4 : ℝ) ≤ (max R 0 + 1) ^ (4 : ℝ) :=
    Real.rpow_le_rpow (bpz_normPlus_pos y).le hnp (by norm_num)
  have hkt0 := hd.kt_nonneg y
  have hn4 : 0 ≤ normPlus y ^ (4 : ℝ) := Real.rpow_nonneg (bpz_normPlus_pos y).le _
  calc kt y * normPlus y ^ (4 : ℝ) * Real.exp (γ ^ 2 * q * bpzPin r y + γ ^ 2 * bpzPin r y)
      ≤ max Bk 0 * (max R 0 + 1) ^ (4 : ℝ) *
          Real.exp (γ ^ 2 * (q + 1) * (Real.log (max R 0 + 1) + 1)) := by
        apply mul_le_mul (mul_le_mul hkt hp4 hn4 (le_max_right _ _)) hexp (Real.exp_pos _).le
        exact mul_nonneg (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

end Bounds

section Measurability

/-- Parametric integrals against the cutoff chaos are jointly measurable. -/
theorem measurable_integral_regularizedGMC_param (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (g : ℂ → ℂ → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : Ω × ℂ => ∫ y, g p.2 y ∂regularizedGMC P Xc γ r p.1) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hVm := measurable_bpz_circle_variance P Xc hXc.1 r
  set dens : Ω → ℂ → ℝ≥0∞ := fun ω y => ENNReal.ofReal
    (Real.exp (γ * Xc ω y r - γ ^ 2 / 2 * ∫ ω', Xc ω' y r ^ 2 ∂P) *
      normPlus y ^ (-4 : ℝ)) with hdens
  have hdm : Measurable (fun p : Ω × ℂ => dens p.1 p.2) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
    · exact Real.measurable_exp.comp (((hXc.1 r).const_mul γ).sub
        ((hVm.comp measurable_snd).const_mul _))
    · exact (bpz_measurable_normPlus.comp measurable_snd).pow_const _
  have heq : ∀ p : Ω × ℂ, ∫ y, g p.2 y ∂regularizedGMC P Xc γ r p.1 =
      ∫ y, (dens p.1 y).toReal * g p.2 y := by
    intro p
    change ∫ y, g p.2 y ∂(volume.withDensity (dens p.1)) = _
    have hd1 : Measurable (dens p.1) :=
      hdm.comp (f := fun y : ℂ => (p.1, y)) (measurable_const.prodMk measurable_id)
    rw [integral_withDensity_eq_integral_toReal_smul hd1
      (Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
    rfl
  simp_rw [heq]
  have hjoint : Measurable (fun q : (Ω × ℂ) × ℂ => (dens q.1.1 q.2).toReal * g q.1.2 q.2) :=
    ((hdm.comp (f := fun q : (Ω × ℂ) × ℂ => (q.1.1, q.2))
      (measurable_fst.fst.prodMk measurable_snd)).ennreal_toReal).mul
      (hg.comp (f := fun q : (Ω × ℂ) × ℂ => (q.1.2, q.2))
        (measurable_fst.snd.prodMk measurable_snd))
  exact (StronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))
    hjoint.stronglyMeasurable).measurable

end Measurability

section Measurability2

variable {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ}

theorem continuous_bpzCutRootKernel (γ r : ℝ) :
    Continuous (fun p : ℂ × ℂ => bpzCutRootKernel γ r p.1 p.2) := by
  unfold bpzCutRootKernel
  exact Real.continuous_exp.comp (continuous_const.mul
    (((continuous_bpzLam r).comp (continuous_fst.sub continuous_snd)).add
      ((continuous_bpzPin r).comp continuous_snd)))

theorem continuous_bpzLimRootKernel (γ r : ℝ) :
    Continuous (fun p : ℂ × ℂ => bpzLimRootKernel γ r p.1 p.2) := by
  unfold bpzLimRootKernel
  refine Real.continuous_exp.comp (continuous_const.mul
    (((continuous_bpzTruncLog r).comp (continuous_fst.sub continuous_snd)).add ?_))
  exact (Real.continuousOn_log.comp_continuous bpz_continuous_normPlus
    fun y => (bpz_normPlus_pos y).ne').comp continuous_snd

theorem measurable_bpzWard_J (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (M : Ω → Measure ℂ) (hMm : Measurable M) (hMfin : ∀ ω, IsFiniteMeasure (M ω))
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) :
    Measurable (fun p : Ω × ℂ =>
      bpzRootedMixedReal γ r ρ k₁ k₂ p.2 (regularizedGMC P Xc γ r p.1) (M p.1)) := by
  unfold bpzRootedMixedReal
  refine Measurable.add ?_ ?_
  · exact measurable_integral_regularizedGMC_param P X hX Xc hXc γ r
      (fun x y => ρ y * k₁ y * bpzCutRootKernel γ r x y)
      (((hρm.mul hk₁).comp measurable_snd).mul (continuous_bpzCutRootKernel γ r).measurable)
  · exact measurable_integral_finite_family M hMm hMfin
      (fun x y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y)
      ((((measurable_const.sub hρm).mul hk₂).comp measurable_snd).mul
        (continuous_bpzLimRootKernel γ r).measurable)

theorem measurable_bpzWard_S (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (M : Ω → Measure ℂ) (hMm : Measurable M) (hMfin : ∀ ω, IsFiniteMeasure (M ω))
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) (v : ℂ) :
    Measurable (fun p : Ω × ℂ =>
      bpzRootedMixedDerivApply γ r ρ k₁ k₂ p.2 v (regularizedGMC P Xc γ r p.1) (M p.1)) := by
  unfold bpzRootedMixedDerivApply
  have hL : Measurable (fun q : ℂ × ℂ => bpzLamDeriv r (q.1 - q.2) v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp
      ((measurable_bpzLamDeriv r).comp (measurable_fst.sub measurable_snd))
  have hT : Measurable (fun q : ℂ × ℂ => bpzTruncLogDeriv r (q.1 - q.2) v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp
      ((measurable_bpzTruncLogDeriv r).comp (measurable_fst.sub measurable_snd))
  refine Measurable.add ?_ ?_
  · exact measurable_integral_regularizedGMC_param P X hX Xc hXc γ r
      (fun x y => ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) * bpzLamDeriv r (x - y) v)
      ((((hρm.mul hk₁).comp measurable_snd).mul
        ((continuous_bpzCutRootKernel γ r).measurable.mul_const _)).mul hL)
  · exact measurable_integral_finite_family M hMm hMfin
      (fun x y => (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) *
        bpzTruncLogDeriv r (x - y) v)
      (((((measurable_const.sub hρm).mul hk₂).comp measurable_snd).mul
        ((continuous_bpzLimRootKernel γ r).measurable.mul_const _)).mul hT)

theorem measurable_bpzWard_Yhat (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (M : Ω → Measure ℂ) (hMm : Measurable M) (hMfin : ∀ ω, IsFiniteMeasure (M ω))
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) (v : ℂ) :
    Measurable (fun p : Ω × ℂ =>
      bpzMixedDerivReal γ r ρ k₁ k₂ p.2 v (regularizedGMC P Xc γ r p.1) (M p.1)) := by
  unfold bpzMixedDerivReal
  have hL : Measurable (fun q : ℂ × ℂ => bpzLamDeriv r (q.1 - q.2) v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp
      ((measurable_bpzLamDeriv r).comp (measurable_fst.sub measurable_snd))
  have hT : Measurable (fun q : ℂ × ℂ => bpzTruncLogDeriv r (q.1 - q.2) v) :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp
      ((measurable_bpzTruncLogDeriv r).comp (measurable_fst.sub measurable_snd))
  refine Measurable.add ?_ ?_
  · exact measurable_integral_regularizedGMC_param P X hX Xc hXc γ r
      (fun x y => ρ y * k₁ y * (γ ^ 2 * bpzLamDeriv r (x - y) v))
      (((hρm.mul hk₁).comp measurable_snd).mul (hL.const_mul _))
  · exact measurable_integral_finite_family M hMm hMfin
      (fun x y => (1 - ρ y) * k₂ y * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v))
      ((((measurable_const.sub hρm).mul hk₂).comp measurable_snd).mul (hT.const_mul _))

end Measurability2

section Lower

/-- An integral of a nonnegative function dominates its lower bound on a set. -/
theorem bpz_integral_lower_on_set {m : Measure ℂ} {f : ℂ → ℝ} {D : Set ℂ} (hD : MeasurableSet D)
    (hf : Integrable f m) (hf0 : ∀ y, 0 ≤ f y) {c : ℝ} (hc : ∀ y ∈ D, c ≤ f y) :
    c * (m D).toReal ≤ ∫ y, f y ∂m := by
  rcases eq_or_ne (m D) ⊤ with htop | htop
  · rw [htop, ENNReal.toReal_top, mul_zero]
    exact integral_nonneg hf0
  · calc c * (m D).toReal = ∫ _y in D, c ∂m := by
          rw [setIntegral_const, smul_eq_mul, measureReal_def, mul_comm]
      _ ≤ ∫ y in D, f y ∂m :=
          setIntegral_mono_on (integrableOn_const htop) hf.integrableOn hD hc
      _ ≤ ∫ y, f y ∂m := setIntegral_le_integral hf (Eventually.of_forall hf0)

theorem bpzLimRootKernel_ge (γ r : ℝ) (hr : 0 ≤ r) (x y : ℂ) :
    (1 + ‖x‖ + ‖y‖) ^ (-γ ^ 2) ≤ bpzLimRootKernel γ r x y := by
  have hpos : 0 < 1 + ‖x‖ + ‖y‖ := by positivity
  unfold bpzLimRootKernel bpzTruncLog
  rw [Real.rpow_def_of_pos hpos]
  apply Real.exp_le_exp.mpr
  have hmax : max (Real.exp (-r)) ‖x - y‖ ≤ 1 + ‖x‖ + ‖y‖ := by
    apply max_le
    · have : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith [norm_nonneg x, norm_nonneg y]
    · have := norm_sub_le x y
      linarith
  have hlog := Real.log_le_log (lt_of_lt_of_le (Real.exp_pos _) (le_max_left _ _)) hmax
  have hnp := Real.log_nonneg (bpz_one_le_normPlus y)
  have hγ := sq_nonneg γ
  nlinarith

end Lower

section LowerProb

variable {γ q r δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

/-- The mixed mass dominates a multiple of the chaos mass of the far set. -/
theorem bpzWard_mixed_lower (hd : BPZWardData γ q r δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) (k₁ : ℂ → ℝ) (hk₁0 : ∀ y, 0 ≤ k₁ y) :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂P, c * (M ω D).toReal ≤
      bpzMixedReal ρ k₁ k₂ (regularizedGMC P Xc γ r ω) (M ω) := by
  obtain ⟨c, hc, hck⟩ := hd.D_low
  refine ⟨c, hc, ?_⟩
  filter_upwards [hp.k₂_int] with ω hint
  have hA : 0 ≤ ∫ y, ρ y * k₁ y ∂regularizedGMC P Xc γ r ω :=
    integral_nonneg fun y => mul_nonneg (hd.ρ_nonneg y) (hk₁0 y)
  have hB := bpz_integral_lower_on_set hd.D_meas hint
    (fun y => mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y)) (c := c)
    (fun y hy => by rw [hd.D_rho y hy, sub_zero, one_mul]; exact hck y hy)
  unfold bpzMixedReal
  linarith

/-- The rooted mixed mass dominates a multiple of the chaos mass of the far set, for roots in a
bounded region where the limit part is integrable. -/
theorem bpzWard_J_lower (hd : BPZWardData γ q r δ ρ kt k₂ φ D) (k₁ : ℂ → ℝ)
    (hk₁0 : ∀ y, 0 ≤ k₁ y) (R' : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m₁ m₂ : Measure ℂ) (x : ℂ), ‖x‖ ≤ R' →
      Integrable (fun y => (1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) m₂ →
      c * (m₂ D).toReal ≤ bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ := by
  obtain ⟨c, hc, hck⟩ := hd.D_low
  obtain ⟨RD, hRD⟩ := hd.D_bdd
  set R'' : ℝ := max R' 0 with hR''
  set RD' : ℝ := max RD 0
  refine ⟨c * (1 + R'' + RD') ^ (-γ ^ 2), by positivity, ?_⟩
  intro m₁ m₂ x hx hint
  have hA : 0 ≤ ∫ y, ρ y * k₁ y * bpzCutRootKernel γ r x y ∂m₁ :=
    integral_nonneg fun y => mul_nonneg (mul_nonneg (hd.ρ_nonneg y) (hk₁0 y))
      (bpzCutRootKernel_pos γ r x y).le
  have hB := bpz_integral_lower_on_set hd.D_meas hint
    (fun y => mul_nonneg (mul_nonneg (by linarith [hd.ρ_le_one y]) (hd.k₂_nonneg y))
      (bpzLimRootKernel_pos γ r x y).le) (c := c * (1 + R'' + RD') ^ (-γ ^ 2))
    (fun y hy => by
      rw [hd.D_rho y hy, sub_zero, one_mul]
      have h1 := bpzLimRootKernel_ge γ r hd.r_nonneg x y
      have h2 : (1 + R'' + RD') ^ (-γ ^ 2) ≤ (1 + ‖x‖ + ‖y‖) ^ (-γ ^ 2) := by
        apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by nlinarith [sq_nonneg γ])
        have := hRD y hy
        have h3 : ‖x‖ ≤ R'' := le_trans hx (le_max_left _ _)
        have h4 : ‖y‖ ≤ RD' := le_trans this (le_max_left _ _)
        linarith
      calc c * (1 + R'' + RD') ^ (-γ ^ 2) ≤ k₂ y * bpzLimRootKernel γ r x y :=
            mul_le_mul (hck y hy) (h2.trans h1) (by positivity) (hd.k₂_nonneg y))
  unfold bpzRootedMixedReal
  linarith

end LowerProb

section NegPow

variable {γ : ℝ} {ρ k₂ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

/-- The far-set chaos mass is almost surely positive. -/
theorem bpzWard_far_mass_pos (hp : BPZWardProb P X γ M Xc ρ k₂ D) (hD : MeasurableSet D) :
    ∀ᵐ ω ∂P, 0 < (M ω D).toReal := by
  have hfin := hp.D_neg 1 zero_le_one
  have hmeas : AEMeasurable (fun ω => M ω D ^ (-(1 : ℝ))) P :=
    ((Measure.measurable_coe hD).comp hp.hMm).aemeasurable.pow_const _
  filter_upwards [ae_lt_top' hmeas hfin.ne] with ω hω
  have hne0 : M ω D ≠ 0 := by
    intro h0
    rw [h0, ENNReal.zero_rpow_of_neg (by norm_num)] at hω
    exact lt_irrefl _ hω
  have hnetop : M ω D ≠ ⊤ := by
    have := hp.hM.1 ω
    exact measure_ne_top _ _
  exact ENNReal.toReal_pos hne0 hnetop

/-- A real random variable dominating a multiple of the far-set mass has all negative moments. -/
theorem bpzWard_integrable_rpow_neg (hp : BPZWardProb P X γ M Xc ρ k₂ D) (hD : MeasurableSet D)
    {Y : Ω → ℝ} (hYm : AEStronglyMeasurable Y P) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ᵐ ω ∂P, c * (M ω D).toReal ≤ Y ω) {p : ℝ} (hp0 : 0 ≤ p) :
    Integrable (fun ω => Y ω ^ (-p)) P := by
  have hmD : Measurable (fun ω => M ω D) := (Measure.measurable_coe hD).comp hp.hMm
  have hg : Integrable (fun ω => (M ω D ^ (-p)).toReal) P :=
    integrable_toReal_of_lintegral_ne_top (hmD.aemeasurable.pow_const _) (hp.D_neg p hp0).ne
  refine (hg.const_mul (c ^ (-p))).mono' (hYm.aemeasurable.pow_const _).aestronglyMeasurable ?_
  filter_upwards [hlow, bpzWard_far_mass_pos hp hD] with ω hω hpos
  have hY : 0 < Y ω := lt_of_lt_of_le (mul_pos hc hpos) hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hY.le _), ← ENNReal.toReal_rpow,
    ← Real.mul_rpow hc.le hpos.le]
  exact Real.rpow_le_rpow_of_nonpos (mul_pos hc hpos) hω (by linarith)

end NegPow

end DOZZ.Proofs
