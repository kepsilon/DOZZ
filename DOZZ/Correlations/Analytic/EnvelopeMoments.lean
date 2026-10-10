/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.CommonThreshold

/-! Converting negative lower-mass and positive upper-mass moments to envelope moments. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The common real mass envelope has a uniform higher-moment bound whenever its two
endpoint ENNReal moments do. This includes zero and negative endpoint orders. -/
theorem mass_envelope_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (L U : Ω → ℝ≥0∞)
    (hL : AEMeasurable L P) (hU : AEMeasurable U P)
    (hLp : ∀ᵐ ω ∂P, L ω ≠ 0 ∧ L ω ≠ ⊤)
    (hUp : ∀ᵐ ω ∂P, U ω ≠ 0 ∧ U ω ≠ ⊤)
    (lo hi q : ℝ) (hq : 1 ≤ q) (KL KU : ℝ≥0∞)
    (hbL : (∫⁻ ω, L ω ^ (lo * q) ∂P) ≤ KL)
    (hbU : (∫⁻ ω, U ω ^ (hi * q) ∂P) ≤ KU) :
    (∫⁻ ω, ENNReal.ofReal ((L ω).toReal ^ lo + (U ω).toReal ^ hi) ^ q ∂P) ≤
      (2 : ℝ≥0∞) ^ (q - 1) * (KL + KU) := by
  have he : ∀ᵐ ω ∂P,
      ENNReal.ofReal ((L ω).toReal ^ lo + (U ω).toReal ^ hi) = L ω ^ lo + U ω ^ hi := by
    filter_upwards [hLp, hUp] with ω hl hu
    rw [ENNReal.ofReal_add (Real.rpow_nonneg ENNReal.toReal_nonneg _)
      (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hl.1 hl.2),
      ← ENNReal.ofReal_rpow_of_pos (ENNReal.toReal_pos hu.1 hu.2),
      ENNReal.ofReal_toReal hl.2, ENNReal.ofReal_toReal hu.2]
  calc
    _ ≤ ∫⁻ ω, (2 : ℝ≥0∞) ^ (q - 1) *
        (L ω ^ (lo * q) + U ω ^ (hi * q)) ∂P := by
      apply lintegral_mono_ae
      filter_upwards [he] with ω hω
      rw [hω]
      simpa only [← ENNReal.rpow_mul] using
        ENNReal.rpow_add_le_mul_rpow_add_rpow (L ω ^ lo) (U ω ^ hi) hq
    _ = (2 : ℝ≥0∞) ^ (q - 1) *
        ((∫⁻ ω, L ω ^ (lo * q) ∂P) + ∫⁻ ω, U ω ^ (hi * q) ∂P) := by
      have hsum : AEMeasurable (fun ω => L ω ^ (lo * q) + U ω ^ (hi * q)) P := by
        simpa only [Pi.add_def] using (hL.pow_const (lo * q)).add (hU.pow_const (hi * q))
      rw [lintegral_const_mul'' _ hsum, lintegral_add_left' (hL.pow_const _)]
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add hbL hbU)

end DOZZ.Proofs
