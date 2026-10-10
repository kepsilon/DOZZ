/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.LateralProjectedGMC

/-!
# Polar integral formula for the lateral projection

The lateral projection `DOZZ.lateralProjectedGMC` is a weighted pushforward under logarithmic
radius. This module records its exact annular-integral formula, which is the measure-theoretic
change of variables needed before identifying a polar GMC limit.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs


/-- Integrating any nonnegative measurable test against the lateral projection is equivalent to
integrating its logarithmic-radius pullback against the plane GMC with the radial Wick weight.
This is the full weighted pushforward identity behind the interval formula above. -/
theorem lateralProjectedGMC_lintegral_eq
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ s, f s ∂lateralProjectedGMC γ A M =
      ∫⁻ x, (ENNReal.ofReal (if ‖x‖ = 0 then 0 else
        Real.exp (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|)) *
          f (-Real.log ‖x‖)) ∂M := by
  let ρ : ℂ → ℝ := fun x => -Real.log ‖x‖
  let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (if ‖x‖ = 0 then 0 else
    Real.exp (-γ * A (ρ x) + γ * Q γ * |Real.log ‖x‖|))
  have hρ : Measurable ρ := measurable_neg.comp (Real.measurable_log.comp measurable_norm)
  have hw : Measurable w := by
    dsimp [w, ρ]
    apply ENNReal.measurable_ofReal.comp
    refine Measurable.ite ?_ measurable_const ?_
    · simp
    · fun_prop
  have hpull : Measurable (fun x : ℂ => f (ρ x)) := hf.comp hρ
  change ∫⁻ s, f s ∂((M.withDensity w).map ρ) =
    ∫⁻ x, (w x * f (ρ x)) ∂M
  rw [lintegral_map hf hρ]
  rw [lintegral_withDensity_eq_lintegral_mul M hw hpull]
  rfl


end DOZZ.Proofs

end
