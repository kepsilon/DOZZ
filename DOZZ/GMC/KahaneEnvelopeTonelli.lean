/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-! Tonelli on a kernel supported by an integrable finite density. -/

@[expose] public section

open MeasureTheory Function
open scoped ENNReal

namespace DOZZ.Proofs

/-- An integrable density permits Tonelli even when the ambient measure is not sigma-finite.
The kernel must vanish where the density vanishes. -/
theorem lintegral_swap_of_finite_density
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (P : Measure Ω) (ν : Measure T) [SFinite ν] (g : Ω → ℝ≥0∞)
    (hg : Measurable g) (hgfinite : ∀ ω, g ω ≠ ∞)
    (hInt : (∫⁻ ω, g ω ∂P) < ∞) (f : Ω → T → ℝ≥0∞)
    (hf : Measurable (uncurry f)) (hz : ∀ ω, g ω = 0 → ∀ t, f ω t = 0) :
    (∫⁻ ω, ∫⁻ t, f ω t ∂ν ∂P) = ∫⁻ t, ∫⁻ ω, f ω t ∂P ∂ν := by
  let ρ := P.withDensity g
  have : IsFiniteMeasure ρ := by
    constructor
    dsimp [ρ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hInt
  let F : Ω → T → ℝ≥0∞ := fun ω t => f ω t / g ω
  have hF : Measurable (uncurry F) := hf.div (hg.comp measurable_fst)
  have hcancel (ω : Ω) (t : T) : g ω * F ω t = f ω t := by
    by_cases hg0 : g ω = 0
    · simp [hg0, hz ω hg0 t, F]
    · dsimp [F]
      rw [ENNReal.mul_div_cancel hg0 (hgfinite ω)]
  have hinner : (∫⁻ ω, ∫⁻ t, F ω t ∂ν ∂ρ) = ∫⁻ ω, ∫⁻ t, f ω t ∂ν ∂P := by
    rw [lintegral_withDensity_eq_lintegral_mul P hg hF.lintegral_prod_right]
    apply lintegral_congr
    intro ω
    change g ω * (∫⁻ t, F ω t ∂ν) = _
    rw [← lintegral_const_mul' _ _ (hgfinite ω)]
    exact lintegral_congr fun t => hcancel ω t
  have houter : (∫⁻ t, ∫⁻ ω, F ω t ∂ρ ∂ν) = ∫⁻ t, ∫⁻ ω, f ω t ∂P ∂ν := by
    apply lintegral_congr
    intro t
    rw [lintegral_withDensity_eq_lintegral_mul P hg hF.of_uncurry_right]
    exact lintegral_congr fun ω => hcancel ω t
  rw [← hinner, ← houter]
  exact lintegral_lintegral_swap hF.aemeasurable

end DOZZ.Proofs
