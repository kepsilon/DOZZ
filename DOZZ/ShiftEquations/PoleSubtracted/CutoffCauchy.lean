/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.CutoffIdentity

/-!
# The Cauchy estimate of the cutoff family

By the martingale identity, `F_{n+1} - F_n = G_{n+1,n+1} - G_{n+1,n}` is the expectation of
`e^{z X_{n+1}(0) - (n+1) z²/2}(B_{n+1}^{1-z/γ} - B_n^{1-z/γ})`. Taking norms, the real tilt by
`a = Re z` and the increment decay give, uniformly for `Re z` in a compact subinterval,
`|F_{n+1}(z) - F_n(z)| ≤ e^{(n+1) b²/2} |1 - z/γ| C e^{-κ n}`, `b = Im z` ([KRV, (estF1)]).
-/

@[expose] public section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

theorem cutoffIntegrand_succ_sub (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (γ η : ℝ)
    (m n : ℕ) (z : ℂ) (ω : Ω) :
    cutoffIntegrand Xc M γ η m (n + 1) z ω - cutoffIntegrand Xc M γ η m n z ω =
      Complex.exp (z * (Xc ω 0 m : ℂ) - (m : ℂ) * z ^ 2 / 2) *
        ((baseMassReal M γ η (n + 1) ω : ℂ) ^ (1 - z / γ) -
          (baseMassReal M γ η n ω : ℂ) ^ (1 - z / γ)) := by
  unfold cutoffIntegrand
  ring

/-- The pointwise bound of the increment integrand. -/
theorem norm_cutoffIntegrand_succ_sub_le (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (γ η : ℝ)
    (m n : ℕ) (z : ℂ) (ω : Ω) (hB : 0 < baseMassReal M γ η n ω)
    (hBB : baseMassReal M γ η n ω ≤ baseMassReal M γ η (n + 1) ω) :
    ‖cutoffIntegrand Xc M γ η m (n + 1) z ω - cutoffIntegrand Xc M γ η m n z ω‖ ≤
      Real.exp (m * z.im ^ 2 / 2) * ‖1 - z / γ‖ *
        (Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
          ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
            (baseMassReal M γ η (n + 1) ω ^ (-z.re / γ) +
              baseMassReal M γ η n ω ^ (-z.re / γ)))) := by
  rw [cutoffIntegrand_succ_sub]
  set B' := baseMassReal M γ η (n + 1) ω
  set B := baseMassReal M γ η n ω
  have hpow := norm_ofReal_cpow_sub_ofReal_cpow_le hB hBB (1 - z / γ)
  rw [re_one_sub_div] at hpow
  have he : 1 - z.re / γ - 1 = -z.re / γ := by ring
  rw [he] at hpow
  have hexp : ‖Complex.exp (z * (Xc ω 0 m : ℂ) - (m : ℂ) * z ^ 2 / 2)‖ =
      Real.exp (m * z.im ^ 2 / 2) * Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) := by
    rw [Complex.norm_exp, re_cutoffExponent, ← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, hexp]
  calc Real.exp (m * z.im ^ 2 / 2) * Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
        ‖(B' : ℂ) ^ (1 - z / γ) - (B : ℂ) ^ (1 - z / γ)‖
      ≤ Real.exp (m * z.im ^ 2 / 2) * Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
          (‖1 - z / γ‖ * (B' - B) * (B' ^ (-z.re / γ) + B ^ (-z.re / γ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- The increment functional `(T_{0,n+1} - T_{0,n})(T_{0,n+1}^s + T_{0,n}^s)` in real form. -/
noncomputable def incrementFunctional (γ η s : ℝ) (n : ℕ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (((cutoffTiltedMass γ η 0 (n + 1) μ).toReal -
      (cutoffTiltedMass γ η 0 n μ).toReal) *
    ((cutoffTiltedMass γ η 0 (n + 1) μ).toReal ^ s + (cutoffTiltedMass γ η 0 n μ).toReal ^ s))

theorem measurable_incrementFunctional (γ η s : ℝ) (n : ℕ) :
    Measurable (incrementFunctional γ η s n) := by
  have hT' := (measurable_cutoffTiltedMass γ η 0 (n + 1)).ennreal_toReal
  have hT := (measurable_cutoffTiltedMass γ η 0 n).ennreal_toReal
  exact ENNReal.measurable_ofReal.comp
    ((hT'.sub hT).mul ((hT'.pow_const s).add (hT.pow_const s)))

/-- **The tilted increment bound**: uniformly for `a` in a compact range,
`E[e^{a X_{n+1} - (n+1) a²/2}(B_{n+1} - B_n)(B_{n+1}^{-a/γ} + B_n^{-a/γ})] ≤ C e^{-κ n}`. -/
theorem exists_integral_cutoffIncrement_le (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) {a₁ a₂ : ℝ} (ha₁ : -2 * η - δ < a₁) (ha₂ : a₂ < 1 / γ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ a ∈ Icc a₁ a₂, ∀ n : ℕ,
      Integrable (fun ω => Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) -
        ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2) *
          ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
            (baseMassReal M γ η (n + 1) ω ^ (-a / γ) + baseMassReal M γ η n ω ^ (-a / γ)))) P ∧
      ∫ ω, Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2) *
        ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
          (baseMassReal M γ η (n + 1) ω ^ (-a / γ) + baseMassReal M γ η n ω ^ (-a / γ))) ∂P ≤
        C * Real.exp (-κ * n) := by
  obtain ⟨C, κ, hC, hκ, hbound⟩ :=
    exists_lintegral_cutoffIncrement_le P X hX γ hγ hγ2 M hM hW ha₁ ha₂
  refine ⟨C, κ, hC, hκ, fun a ha n => ?_⟩
  have hgood := ae_cutoffGood P X hX γ hγ hγ2 M hM hW
  have hnonneg : 0 ≤ᵐ[P] fun ω => Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) -
      ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2) *
      ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
        (baseMassReal M γ η (n + 1) ω ^ (-a / γ) + baseMassReal M γ η n ω ^ (-a / γ))) := by
    filter_upwards [hgood] with ω hω
    have hB := hω.localMassReal_pos.trans_le (hω.localMassReal_le hγ n)
    have hB' := hB.trans_le (hω.baseMassReal_le_succ hγ n)
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (sub_nonneg.2 (hω.baseMassReal_le_succ hγ n)) (by positivity))
  have hfac : ∀ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) -
      ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2) *
      ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
        (baseMassReal M γ η (n + 1) ω ^ (-a / γ) + baseMassReal M γ η n ω ^ (-a / γ)))) =
      ENNReal.ofReal (Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2)) *
        incrementFunctional γ η (-a / γ) n (M ω) := by
    intro ω
    rw [incrementFunctional, ← baseMassReal_eq, ← baseMassReal_eq,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hmeas : AEStronglyMeasurable (fun ω => Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) -
      ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2) *
      ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
        (baseMassReal M γ η (n + 1) ω ^ (-a / γ) + baseMassReal M γ η n ω ^ (-a / γ)))) P := by
    have hB := aemeasurable_baseMassReal P X hX γ hγ hγ2 M hM η n
    have hB' := aemeasurable_baseMassReal P X hX γ hγ hγ2 M hM η (n + 1)
    have hXm : AEMeasurable (fun ω => Xc ω 0 ((n + 1 : ℕ) : ℝ)) P :=
      (measurable_circleAverage_origin hXc (n + 1)).aemeasurable
    exact ((Real.measurable_exp.comp_aemeasurable ((hXm.const_mul a).sub aemeasurable_const)).mul
      ((hB'.sub hB).mul ((hB'.pow_const _).add (hB.pow_const _)))).aestronglyMeasurable
  have hlin : ∫⁻ ω, ENNReal.ofReal (Real.exp (a * Xc ω 0 ((n + 1 : ℕ) : ℝ) -
      ((n + 1 : ℕ) : ℝ) * a ^ 2 / 2) *
      ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
        (baseMassReal M γ η (n + 1) ω ^ (-a / γ) + baseMassReal M γ η n ω ^ (-a / γ)))) ∂P ≤
      ENNReal.ofReal (C * Real.exp (-κ * n)) := by
    simp_rw [hfac]
    rw [lintegral_circleTilt P X hX γ hγ hγ2 M hM Xc hXc a (n + 1) _
      (measurable_incrementFunctional γ η (-a / γ) n)]
    have hae : ∀ᵐ ω ∂P, incrementFunctional γ η (-a / γ) n
        ((M ω).withDensity (circleTiltDensity γ a (n + 1))) =
        (cutoffTiltedMass γ η a (n + 1) (M ω) - cutoffTiltedMass γ η a n (M ω)) *
          (cutoffTiltedMass γ η a (n + 1) (M ω) ^ (-a / γ) +
            cutoffTiltedMass γ η a n (M ω) ^ (-a / γ)) := by
      filter_upwards [hgood] with ω hω
      rw [incrementFunctional, cutoffTiltedMass_withDensity γ η a (le_refl (n + 1)),
        cutoffTiltedMass_withDensity γ η a (Nat.le_succ n)]
      exact ofReal_sub_mul_rpow_add_rpow
        (hω.1.trans_le (localMass_le_cutoffTiltedMass γ η a n (M ω)))
        (monotone_cutoffTiltedMass γ η a (M ω) (Nat.le_succ n))
        (hω.cutoffTiltedMass_lt_top hγ a (n + 1)).ne _
    rw [lintegral_congr_ae hae]
    exact hbound a ha n
  refine ⟨⟨hmeas, (hasFiniteIntegral_iff_ofReal hnonneg).2
    (hlin.trans_lt ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

/-- **The Cauchy estimate of the cutoff family** (`estF1`): uniformly for `Re z` in a compact
subinterval of `(-2η - δ, 1/γ)`,
`|F_{n+1}(z) - F_n(z)| ≤ e^{(n+1) (Im z)²/2} |1 - z/γ| C e^{-κ n}`. -/
theorem exists_cutoff_cauchy_bound (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) {η δ : ℝ}
    (hW : TwoPoleWindow γ η δ) {a₁ a₂ : ℝ} (ha₁ : -2 * η - δ < a₁) (ha₂ : a₂ < 1 / γ) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ z : ℂ, z.re ∈ Icc a₁ a₂ → ∀ n : ℕ,
      ‖poleSubtractedCutoff P Xc M γ η (n + 1) z -
          poleSubtractedCutoff P Xc M γ η n z‖ ≤
        Real.exp (((n + 1 : ℕ) : ℝ) * z.im ^ 2 / 2) * ‖1 - z / γ‖ * (C * Real.exp (-κ * n)) := by
  obtain ⟨C, κ, hC, hκ, hint⟩ :=
    exists_integral_cutoffIncrement_le P X hX γ hγ hγ2 M hM Xc hXc hW ha₁ ha₂
  refine ⟨C, κ, hC, hκ, fun z hz n => ?_⟩
  have hzH : z ∈ cutoffHalfPlane η δ := lt_of_lt_of_le ha₁ hz.1
  have hgood := ae_cutoffGood P X hX γ hγ hγ2 M hM hW
  rw [poleSubtractedCutoff_eq_cutoffFamily, poleSubtractedCutoff_eq_cutoffFamily,
    ← cutoffFamily_succ_eqOn P X hX γ hγ hγ2 M hM Xc hXc hW n hzH]
  have hi1 := (differentiableOn_cutoffFamily P X hX γ hγ hγ2 M hM Xc hXc hW
    (le_refl (n + 1))).2 z hzH
  have hi2 := (differentiableOn_cutoffFamily P X hX γ hγ hγ2 M hM Xc hXc hW
    (Nat.le_succ n)).2 z hzH
  obtain ⟨hgi, hgle⟩ := hint z.re hz n
  unfold cutoffFamily
  rw [← integral_sub hi1 hi2]
  have hbound : ∀ᵐ ω ∂P, ‖cutoffIntegrand Xc M γ η (n + 1) (n + 1) z ω -
      cutoffIntegrand Xc M γ η (n + 1) n z ω‖ ≤
      Real.exp (((n + 1 : ℕ) : ℝ) * z.im ^ 2 / 2) * ‖1 - z / γ‖ *
        (Real.exp (z.re * Xc ω 0 ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * z.re ^ 2 / 2) *
          ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
            (baseMassReal M γ η (n + 1) ω ^ (-z.re / γ) +
              baseMassReal M γ η n ω ^ (-z.re / γ)))) := by
    filter_upwards [hgood] with ω hω
    exact norm_cutoffIntegrand_succ_sub_le Xc M γ η (n + 1) n z ω
      (hω.localMassReal_pos.trans_le (hω.localMassReal_le hγ n)) (hω.baseMassReal_le_succ hγ n)
  calc ‖∫ ω, (cutoffIntegrand Xc M γ η (n + 1) (n + 1) z ω -
        cutoffIntegrand Xc M γ η (n + 1) n z ω) ∂P‖
      ≤ ∫ ω, Real.exp (((n + 1 : ℕ) : ℝ) * z.im ^ 2 / 2) * ‖1 - z / γ‖ *
          (Real.exp (z.re * Xc ω 0 ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * z.re ^ 2 / 2) *
            ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
              (baseMassReal M γ η (n + 1) ω ^ (-z.re / γ) +
                baseMassReal M γ η n ω ^ (-z.re / γ)))) ∂P :=
        norm_integral_le_of_norm_le (hgi.const_mul _) hbound
    _ = Real.exp (((n + 1 : ℕ) : ℝ) * z.im ^ 2 / 2) * ‖1 - z / γ‖ *
          ∫ ω, Real.exp (z.re * Xc ω 0 ((n + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) * z.re ^ 2 / 2) *
            ((baseMassReal M γ η (n + 1) ω - baseMassReal M γ η n ω) *
              (baseMassReal M γ η (n + 1) ω ^ (-z.re / γ) +
                baseMassReal M γ η n ω ^ (-z.re / γ))) ∂P := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hgle (by positivity)

end DOZZ.Proofs

end
