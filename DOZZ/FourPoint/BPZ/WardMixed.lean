/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardTilt

/-! # The mixed cutoff mass of the Ward identity

On a bounded region (a cutoff function `ρ`) the degenerate four-point weight is integrated
against the cutoff chaos, and elsewhere against the limit chaos. Rooting the mixed mass at a point
`x` of the cutoff region multiplies it by `e^{γ² h_r(x)}` and replaces the two chaos measures by
the translation kernels `e^{γ² Λ_r(x - ·)}` and `e^{γ² Λ¹_r(x - ·)}`; the factor `e^{γ² h_r(x)}`
is the only dependence on the pinning at the root. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The degenerate four-point weight without its factors of `|x|₊`. -/
noncomputable def bpzTildeWeight (γ χ α₁ α₂ : ℝ) (z x : ℂ) : ℝ :=
  ‖x - z‖ ^ (γ * χ) * ‖x‖ ^ (-(γ * α₁)) * ‖x - 1‖ ^ (-(γ * α₂))


/-- The mixed mass `∫ ρ k₁ dm₁ + ∫ (1 - ρ) k₂ dm₂`. -/
noncomputable def bpzMixedMass (ρ k₁ k₂ : ℂ → ℝ) (m₁ m₂ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ y * k₁ y) ∂m₁ + ∫⁻ y, ENNReal.ofReal ((1 - ρ y) * k₂ y) ∂m₂

/-- The cutoff-region kernel of the rooted mixed mass. -/
noncomputable def bpzCutRootKernel (γ r : ℝ) (x y : ℂ) : ℝ :=
  Real.exp (γ ^ 2 * (bpzLam r (x - y) + bpzPin r y))

/-- The limit-region kernel of the rooted mixed mass. -/
noncomputable def bpzLimRootKernel (γ r : ℝ) (x y : ℂ) : ℝ :=
  Real.exp (γ ^ 2 * (bpzTruncLog r (x - y) + Real.log (normPlus y)))

/-- The mixed mass rooted at `x`, with the root pinning factor removed. -/
noncomputable def bpzRootedMixedMass (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x : ℂ)
    (m₁ m₂ : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (ρ y * k₁ y * bpzCutRootKernel γ r x y) ∂m₁ +
    ∫⁻ y, ENNReal.ofReal ((1 - ρ y) * k₂ y * bpzLimRootKernel γ r x y) ∂m₂

theorem continuous_bpzLam (r : ℝ) : Continuous (bpzLam r) := by
  refine (LipschitzWith.of_dist_le_mul fun w w' => ?_).continuous (K := Real.toNNReal (Real.exp r))
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos r).le]
  exact abs_bpzLam_sub_le r w w'

theorem bpzPin_eq_interval (r : ℝ) (x : ℂ) :
    bpzPin r x = (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        Real.log (normPlus (x + Real.exp (-r) * Complex.exp (θ * Complex.I))) := by
  have hm : Measurable fun a : ℂ => Real.log (normPlus a) :=
    Real.measurable_log.comp bpz_measurable_normPlus
  rw [bpzPin, bpz_integral_circleMeasure_eq x r (fun a => Real.log (normPlus a)) hm]
  rfl

theorem abs_bpzPin_sub_le' (r : ℝ) (x x' : ℂ) : |bpzPin r x - bpzPin r x'| ≤ ‖x - x'‖ := by
  have hcont : ∀ c : ℂ, Continuous fun θ : ℝ =>
      Real.log (normPlus (c + Real.exp (-r) * Complex.exp (θ * Complex.I))) := by
    intro c
    refine (Real.continuousOn_log.comp_continuous (bpz_continuous_normPlus.comp
      (continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))))) fun θ => ?_)
    exact (bpz_normPlus_pos _).ne'
  rw [bpzPin_eq_interval, bpzPin_eq_interval, ← mul_sub,
    ← intervalIntegral.integral_sub ((hcont x).intervalIntegrable _ _)
      ((hcont x').intervalIntegrable _ _)]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpi)]
  have hb : ∀ θ ∈ Set.uIoc 0 (2 * Real.pi),
      ‖Real.log (normPlus (x + Real.exp (-r) * Complex.exp (θ * Complex.I))) -
        Real.log (normPlus (x' + Real.exp (-r) * Complex.exp (θ * Complex.I)))‖ ≤ ‖x - x'‖ := by
    intro θ _
    rw [Real.norm_eq_abs]
    refine (abs_log_normPlus_sub_le' _ _).trans (le_of_eq ?_)
    congr 1
    ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpi] at hint
  calc (2 * Real.pi)⁻¹ * |∫ θ in (0 : ℝ)..2 * Real.pi, _|
      ≤ (2 * Real.pi)⁻¹ * (‖x - x'‖ * (2 * Real.pi)) := by gcongr
    _ = ‖x - x'‖ := by field_simp

theorem continuous_bpzPin (r : ℝ) : Continuous (bpzPin r) := by
  refine (LipschitzWith.of_dist_le_mul fun w w' => ?_).continuous (K := 1)
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_bpzPin_sub_le' r w w'

theorem measurable_bpzCutRootDensity (γ r : ℝ) (x : ℂ) :
    Measurable (bpzCutRootDensity γ r x) := by
  unfold bpzCutRootDensity
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.const_mul ?_ _))
  exact (((continuous_bpzLam r).comp (continuous_const.sub continuous_id)).measurable.add
    measurable_const).add (continuous_bpzPin r).measurable

theorem measurable_bpzLimRootDensity (γ r : ℝ) (x : ℂ) :
    Measurable (bpzLimRootDensity γ r x) := by
  unfold bpzLimRootDensity
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (Measurable.const_mul ?_ _))
  exact (((continuous_bpzTruncLog r).comp (continuous_const.sub continuous_id)).measurable.add
    measurable_const).add (Real.measurable_log.comp bpz_measurable_normPlus)


end DOZZ.Proofs
