/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ComplexMassFunctional
public import DOZZ.Correlations.Analytic.NormalizedRealValue

/-! Taking absolute values before the real tilt in the complex cutoff increment. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Scaling both nonnegative masses scales their complex-power difference by the real power
of the scale. This includes zero masses and exponent zero. -/
theorem cpow_scaled_difference_norm (c x y : ℝ) (hc : 0 < c) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (p : ℂ) :
    ‖((c * x : ℝ) : ℂ) ^ p - ((c * y : ℝ) : ℂ) ^ p‖ =
      c ^ p.re * ‖(x : ℂ) ^ p - (y : ℂ) ^ p‖ := by
  rw [Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hx p, Complex.mul_cpow_ofReal_nonneg hc.le hy p,
    ← mul_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc]

/-- The norm integral of the actual complex increment is exactly a deterministic imaginary
Wick factor times the norm integral of the retained Coulomb mass-power increment. -/
theorem normalized_vertex_increment_tilt_norm
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (β : Fin (N + 1) → ℂ) (z : Fin N → ℂ) (r : ℝ) (hr : 0 ≤ r)
    (O₁ O₀ : Set ℂ) (h₁ : MeasurableSet O₁) (h₀ : MeasurableSet O₀)
    (hO₁ : O₁ ⊆ retainedRegion z r) (hO₀ : O₀ ⊆ retainedRegion z r) :
    let a := fun i => (β i).re
    let L := fun ω => ∑ i, a i * Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)
    let p := complexMomentPower γ β
    let A := γ * ∑ i, a i.castSucc * equatorCircleMean (z i) r
    (∫⁻ ω, ENNReal.ofReal ‖Complex.exp (normalizedVertexPolynomial P Xc γ z r β +
      ∑ i, β i * (Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i) : ℂ)) *
        (((M ω O₁).toReal : ℂ) ^ p - ((M ω O₀).toReal : ℂ) ^ p)‖ ∂P) =
      ENNReal.ofReal (Real.exp ((normalizedVertexPolynomial P Xc γ z r β).re +
        gaussianVariance P L / 2 + A * p.re)) *
        ∫⁻ ω, ENNReal.ofReal
          ‖((∫⁻ x in O₁, coulombWeight γ (fun i => a i.castSucc) z (a (Fin.last N)) x ∂M ω).toReal : ℂ) ^ p -
            ((∫⁻ x in O₀, coulombWeight γ (fun i => a i.castSucc) z (a (Fin.last N)) x ∂M ω).toReal : ℂ) ^ p‖ ∂P := by
  dsimp only
  let a := fun i => (β i).re
  let L (ω : Ω) := ∑ i, a i * Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i)
  let p := complexMomentPower γ β
  let A := γ * ∑ i, a i.castSucc * equatorCircleMean (z i) r
  let D := (normalizedVertexPolynomial P Xc γ z r β).re + gaussianVariance P L / 2
  let H (μ : Measure ℂ) := ENNReal.ofReal ‖((μ O₁).toReal : ℂ) ^ p - ((μ O₀).toReal : ℂ) ^ p‖
  have hH : Measurable H := measurable_complex_mass_difference O₁ O₀ h₁ h₀ p
  have he (ω : Ω) :
      ENNReal.ofReal ‖Complex.exp (normalizedVertexPolynomial P Xc γ z r β +
        ∑ i, β i * (Xc ω (mixedVertexCenters z i) (mixedVertexTimes N r i) : ℂ)) *
          (((M ω O₁).toReal : ℂ) ^ p - ((M ω O₀).toReal : ℂ) ^ p)‖ =
      ENNReal.ofReal (Real.exp D) *
        (ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) * H (M ω)) := by
    have hexp : (normalizedVertexPolynomial P Xc γ z r β +
        ∑ i, β i * (Xc ω (mixedVertexCenters z i)
          (mixedVertexTimes N r i) : ℂ)).re =
        D + (L ω - gaussianVariance P L / 2) := by
      dsimp only [D, L, a]
      simp only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      ring
    rw [norm_mul, Complex.norm_exp, hexp, Real.exp_add,
      ENNReal.ofReal_mul (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)),
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact mul_assoc _ _ _
  conv_lhs =>
    arg 2
    ext ω
    rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    mixed_vertex_tilt_functional P X hX γ hγ hγ2 M hM Xc hXc a
      (mixedVertexCenters z) (mixedVertexTimes N r) H hH]
  have hs (μ : Measure ℂ) :
      H (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * ∑ i, a i *
        ∫ v, gffKernel x v ∂circleMeasure (mixedVertexCenters z i)
          (mixedVertexTimes N r i))))) =
      ENNReal.ofReal (Real.exp (A * p.re)) * ENNReal.ofReal
        ‖((∫⁻ x in O₁, coulombWeight γ (fun i => a i.castSucc) z (a (Fin.last N)) x ∂μ).toReal : ℂ) ^ p -
          ((∫⁻ x in O₀, coulombWeight γ (fun i => a i.castSucc) z (a (Fin.last N)) x ∂μ).toReal : ℂ) ^ p‖ := by
    dsimp only [H]
    rw [mixed_tilted_retained_measure_eq μ γ a z r hr O₁ h₁ hO₁,
      mixed_tilted_retained_measure_eq μ γ a z r hr O₀ h₀ hO₀,
      ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    rw [cpow_scaled_difference_norm (Real.exp A) _ _ (Real.exp_pos A)
      ENNReal.toReal_nonneg ENNReal.toReal_nonneg p, ← Real.exp_mul,
      ENNReal.ofReal_mul (Real.exp_nonneg _)]
  simp_rw [hs]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

end DOZZ.Proofs
