/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralIntervalFirstMoment
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Positive lateral moments through order one

The exact first-moment intensity and the probability normalization imply all nonnegative moments
through order one by the concave-power form of Hölder's inequality. This gives a uniform strip of
the lateral interval moment theorem without invoking any higher-order chaos estimate.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- On a probability space, the moment of order `q ∈ [0,1]` is bounded by the first moment to the
power `q`. -/
theorem lintegral_rpow_le_mean_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hP : IsProbabilityMeasure P)
    (X : Ω → ℝ≥0∞) (hX : AEMeasurable X P) (q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫⁻ ω, X ω ^ q ∂P) ≤ (∫⁻ ω, X ω ∂P) ^ q := by
  have h := ENNReal.lintegral_mul_norm_pow_le
    hX (measurable_const.aemeasurable : AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P)
    hq0 (by linarith) (by linarith : q + (1 - q) = 1)
  simpa [lintegral_const, hP.measure_univ] using h

/-- Every lateral interval has the Jensen bound for moment orders from zero to one. -/
theorem lateralGMC_interval_rpow_le_intensity_rpow
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hab : a < b) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫⁻ ω, ENNReal.rpow (Z ω (Set.Ioc a b)) q ∂P) ≤
      ENNReal.ofReal (2 * Real.pi * (b - a)) ^ q := by
  rcases hZ with ⟨_, _, hP, hZm, _, _, _, hIntensity, _⟩
  let X : Ω → ℝ≥0∞ := fun ω => Z ω (Set.Ioc a b)
  have hX : AEMeasurable X P :=
    (Measure.measurable_coe measurableSet_Ioc).comp_aemeasurable hZm
  calc
    (∫⁻ ω, ENNReal.rpow (Z ω (Set.Ioc a b)) q ∂P) ≤
        (∫⁻ ω, X ω ∂P) ^ q := by
          exact lintegral_rpow_le_mean_rpow P hP X hX q hq0 hq1
    _ = ENNReal.ofReal (2 * Real.pi * (b - a)) ^ q := by
          rw [show (∫⁻ ω, X ω ∂P) = ENNReal.ofReal (2 * Real.pi * (b - a)) by
            exact hIntensity a b hab]


end DOZZ.Proofs

end
