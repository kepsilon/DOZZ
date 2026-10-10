/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.Masses
public import DOZZ.ShiftEquations.PoleSubtracted.PowerBounds
public import DOZZ.Statements.Defs.IsCircleAverage

/-!
# The cutoff integrand

For the tilt index `m` and the domain index `n`, the cutoff integrand is
`e^{z X_m(0) - m z²/2} (B_n^{1-z/γ} - R₁^{1-z/γ})` with the real base mass `B_n = Z_{C_n}(0)` and
the real local mass `R₁` ([KRV, §10.2]); its expectation `G_{m,n}` is the source's `F_t` for
`m = n`. When `0 < R₁ ≤ B_n` the integrand is entire in `z`, and with `z = a + ib`
`|·| ≤ e^{m b²/2} |1 - z/γ| e^{a X_m - m a²/2} (B_n - R₁)(B_n^{-a/γ} + R₁^{-a/γ})`; on a range
`a ∈ [a₁, a₂]` the `a`-dependence is dominated by the two endpoints.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real base mass `B_n(ω) = Z_{C_n}(0)`. -/
noncomputable def baseMassReal (M : Ω → Measure ℂ) (γ η : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (poleCutoffBaseMass M γ η n ω).toReal

/-- The real local mass `R₁(ω)`. -/
noncomputable def localMassReal (M : Ω → Measure ℂ) (γ η : ℝ) (ω : Ω) : ℝ :=
  (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal

/-- The cutoff integrand `e^{z X_m(0) - m z²/2} (B_n^{1-z/γ} - R₁^{1-z/γ})`. -/
noncomputable def cutoffIntegrand (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (γ η : ℝ)
    (m n : ℕ) (z : ℂ) (ω : Ω) : ℂ :=
  Complex.exp (z * (Xc ω 0 m : ℂ) - (m : ℂ) * z ^ 2 / 2) *
    ((baseMassReal M γ η n ω : ℂ) ^ (1 - z / γ) - (localMassReal M γ η ω : ℂ) ^ (1 - z / γ))

/-- `G_{m,n}(z)`, the expectation of the cutoff integrand. -/
noncomputable def cutoffFamily (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ)
    (γ η : ℝ) (m n : ℕ) (z : ℂ) : ℂ :=
  ∫ ω, cutoffIntegrand Xc M γ η m n z ω ∂P

/-- The cutoff observable `poleSubtractedCutoff` is the diagonal `G_{n,n}`. -/
theorem poleSubtractedCutoff_eq_cutoffFamily (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (M : Ω → Measure ℂ) (γ η : ℝ) (n : ℕ) :
    poleSubtractedCutoff P Xc M γ η n = cutoffFamily P Xc M γ η n n := rfl

/-- The `a`-dependent factor `e^{a X} (B^{-a/γ} + R^{-a/γ})` of the bound. -/
noncomputable def cutoffWeight (γ X B L a : ℝ) : ℝ :=
  Real.exp (a * X) * (B ^ (-a / γ) + L ^ (-a / γ))

/-- The real part of the Gaussian exponent. -/
theorem re_cutoffExponent (z : ℂ) (X : ℝ) (m : ℕ) :
    (z * (X : ℂ) - (m : ℂ) * z ^ 2 / 2).re = z.re * X - m * (z.re ^ 2 - z.im ^ 2) / 2 := by
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.div_ofNat_re, Complex.natCast_re, Complex.natCast_im, sq]
  ring

theorem re_one_sub_div (z : ℂ) (γ : ℝ) : (1 - z / γ).re = 1 - z.re / γ := by
  simp [Complex.div_ofReal_re]

/-- **The pointwise bound** of the cutoff integrand. -/
theorem norm_cutoffIntegrand_le (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) {γ : ℝ} (η : ℝ)
    (m n : ℕ) (z : ℂ) (ω : Ω) (hL : 0 < localMassReal M γ η ω)
    (hLB : localMassReal M γ η ω ≤ baseMassReal M γ η n ω) :
    ‖cutoffIntegrand Xc M γ η m n z ω‖ ≤
      Real.exp (m * z.im ^ 2 / 2) * ‖1 - z / γ‖ *
        (Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
          ((baseMassReal M γ η n ω - localMassReal M γ η ω) *
            (baseMassReal M γ η n ω ^ (-z.re / γ) + localMassReal M γ η ω ^ (-z.re / γ)))) := by
  set B := baseMassReal M γ η n ω
  set L := localMassReal M γ η ω
  have hpow := norm_ofReal_cpow_sub_ofReal_cpow_le hL hLB (1 - z / γ)
  rw [re_one_sub_div] at hpow
  have he : 1 - z.re / γ - 1 = -z.re / γ := by ring
  rw [he] at hpow
  have hexp : ‖Complex.exp (z * (Xc ω 0 m : ℂ) - (m : ℂ) * z ^ 2 / 2)‖ =
      Real.exp (m * z.im ^ 2 / 2) * Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) := by
    rw [Complex.norm_exp, re_cutoffExponent, ← Real.exp_add]
    congr 1
    ring
  unfold cutoffIntegrand
  rw [norm_mul, hexp]
  calc Real.exp (m * z.im ^ 2 / 2) * Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
        ‖(B : ℂ) ^ (1 - z / γ) - (L : ℂ) ^ (1 - z / γ)‖
      ≤ Real.exp (m * z.im ^ 2 / 2) * Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
          (‖1 - z / γ‖ * (B - L) * (B ^ (-z.re / γ) + L ^ (-z.re / γ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by ring

/-- Two-endpoint domination of the `a`-dependent factor. -/
theorem cutoffWeight_le_endpoints {γ X B L a a₁ a₂ : ℝ} (hB : 0 < B) (hL : 0 < L)
    (ha : a ∈ Icc a₁ a₂) :
    cutoffWeight γ X B L a ≤ cutoffWeight γ X B L a₁ + cutoffWeight γ X B L a₂ := by
  have key : ∀ (C : ℝ), 0 < C → ∀ b : ℝ,
      Real.exp (b * X) * C ^ (-b / γ) = Real.exp (b * (X - Real.log C / γ)) := by
    intro C hC b
    rw [Real.rpow_def_of_pos hC, ← Real.exp_add]
    congr 1
    ring
  have h1 := exp_mul_le_add_of_mem_Icc ha (X - Real.log B / γ)
  have h2 := exp_mul_le_add_of_mem_Icc ha (X - Real.log L / γ)
  unfold cutoffWeight
  rw [mul_add, mul_add, mul_add, key B hB, key L hL, key B hB, key L hL, key B hB, key L hL]
  linarith

/-- **Domination on a parameter box**: for `Re z ∈ [a₁, a₂]`, `|Im z| ≤ b₀` and
`|1 - z/γ| ≤ W`, the cutoff integrand is dominated by the two endpoint weights. -/
theorem norm_cutoffIntegrand_le_endpoints (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) {γ : ℝ}
    (η : ℝ) (m n : ℕ) {z : ℂ} (ω : Ω) (hL : 0 < localMassReal M γ η ω)
    (hLB : localMassReal M γ η ω ≤ baseMassReal M γ η n ω) {a₁ a₂ b₀ W : ℝ}
    (hz : z.re ∈ Icc a₁ a₂) (hb : |z.im| ≤ b₀) (hW : ‖1 - z / γ‖ ≤ W) :
    ‖cutoffIntegrand Xc M γ η m n z ω‖ ≤
      Real.exp (m * b₀ ^ 2 / 2) * W *
        ((baseMassReal M γ η n ω - localMassReal M γ η ω) *
          (cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a₁ +
            cutoffWeight γ (Xc ω 0 m) (baseMassReal M γ η n ω) (localMassReal M γ η ω) a₂)) := by
  set B := baseMassReal M γ η n ω
  set L := localMassReal M γ η ω
  have hB : 0 < B := hL.trans_le hLB
  have hBL : 0 ≤ B - L := sub_nonneg.2 hLB
  refine (norm_cutoffIntegrand_le Xc M η m n z ω hL hLB).trans ?_
  have him : Real.exp (m * z.im ^ 2 / 2) ≤ Real.exp (m * b₀ ^ 2 / 2) := by
    apply Real.exp_le_exp.2
    have : z.im ^ 2 ≤ b₀ ^ 2 := by
      rw [← sq_abs z.im]
      exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  have hgauss : Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) ≤ Real.exp (z.re * Xc ω 0 m) := by
    apply Real.exp_le_exp.2
    have : (0 : ℝ) ≤ m * z.re ^ 2 / 2 := by positivity
    linarith
  have hweight := cutoffWeight_le_endpoints (γ := γ) (X := Xc ω 0 m) hB hL hz
  have hfac : Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
      ((B - L) * (B ^ (-z.re / γ) + L ^ (-z.re / γ))) ≤
      (B - L) * (cutoffWeight γ (Xc ω 0 m) B L a₁ + cutoffWeight γ (Xc ω 0 m) B L a₂) := by
    calc Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
          ((B - L) * (B ^ (-z.re / γ) + L ^ (-z.re / γ)))
        ≤ Real.exp (z.re * Xc ω 0 m) * ((B - L) * (B ^ (-z.re / γ) + L ^ (-z.re / γ))) :=
          mul_le_mul_of_nonneg_right hgauss (by positivity)
      _ = (B - L) * cutoffWeight γ (Xc ω 0 m) B L z.re := by
          unfold cutoffWeight
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hweight hBL
  have hW0 : ‖1 - z / γ‖ ≤ W := hW
  calc Real.exp (m * z.im ^ 2 / 2) * ‖1 - z / γ‖ *
        (Real.exp (z.re * Xc ω 0 m - m * z.re ^ 2 / 2) *
          ((B - L) * (B ^ (-z.re / γ) + L ^ (-z.re / γ))))
      ≤ Real.exp (m * b₀ ^ 2 / 2) * W *
          ((B - L) * (cutoffWeight γ (Xc ω 0 m) B L a₁ + cutoffWeight γ (Xc ω 0 m) B L a₂)) := by
        apply mul_le_mul (mul_le_mul him hW0 (norm_nonneg _) (Real.exp_pos _).le) hfac
          (by positivity)
        exact mul_nonneg (Real.exp_pos _).le ((norm_nonneg _).trans hW0)

/-- For `0 < R₁ ≤ B_n` the cutoff integrand is entire in `z`. -/
theorem differentiable_cutoffIntegrand (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ) (γ η : ℝ)
    (m n : ℕ) (ω : Ω) (hL : 0 < localMassReal M γ η ω)
    (hLB : localMassReal M γ η ω ≤ baseMassReal M γ η n ω) :
    Differentiable ℂ fun z => cutoffIntegrand Xc M γ η m n z ω := by
  have hB : (baseMassReal M γ η n ω : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (hL.trans_le hLB).ne'
  have hL' : (localMassReal M γ η ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  intro z
  unfold cutoffIntegrand
  apply DifferentiableAt.mul
  · fun_prop
  · apply DifferentiableAt.sub
    · exact (differentiableAt_const _).sub ((differentiableAt_id).div_const _) |>.const_cpow
        (Or.inl hB)
    · exact (differentiableAt_const _).sub ((differentiableAt_id).div_const _) |>.const_cpow
        (Or.inl hL')

end DOZZ.Proofs

end
