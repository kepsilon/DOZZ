/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizedCopiedLaw

/-! The five literal masses in the localized one-insertion comparison. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

noncomputable def localizedOriginal {Ω : Type*} (M : Ω → Measure ℂ)
    (χ F : ℂ → ℝ) (z : ℂ) (γ α : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (χ (y-z)*F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω

noncomputable def localizedCopy {Ω : Type*} (N : Ω → Measure ℂ)
    (Xc : Ω → ℂ → ℝ → ℝ) (χ F : ℂ → ℝ) (z : ℂ) (γ α : ℝ) (q : Ω × Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
    ∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x)*
      (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1

noncomputable def canonicalLeading {Ω : Type*} (N : Ω → Measure ℂ)
    (Xc : Ω → ℂ → ℝ → ℝ) (f : ℝ) (z : ℂ) (γ α : ℝ) (q : Ω × Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
    localSingularMass N (fun _ => 1) 0 γ α q.1

noncomputable def originalAnnular {Ω : Type*} (M : Ω → Measure ℂ)
    (F : ℂ → ℝ) (z : ℂ) (γ α δ : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ y in Metric.ball z 1 \ Metric.ball z δ,
    ENNReal.ofReal (F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω

noncomputable def copiedRemainder {Ω : Type*} (N : Ω → Measure ℂ)
    (Xc : Ω → ℂ → ℝ → ℝ) (F : ℂ → ℝ) (z : ℂ) (γ α ρ : ℝ) (q : Ω × Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
    (∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
      |copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x-
        F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)+
  ENNReal.ofReal (F z*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
    (∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (ρ/4),
      (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)

end DOZZ.Proofs
