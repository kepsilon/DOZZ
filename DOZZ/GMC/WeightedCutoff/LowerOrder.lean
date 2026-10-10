module

public import DOZZ.GMC.WeightedCutoff.ReferenceUniform

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem lintegral_lower_rpow_const_mul_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ≥0∞)
    (hf : AEMeasurable f P) (c D : ℝ≥0∞) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hD : (∫⁻ ω, f ω ^ q ∂P) ≤ D) :
    (∫⁻ ω, (c * f ω) ^ p ∂P) ≤ 1 + c ^ q * D := by
  have hq : 0 ≤ q := hp.trans hpq
  have hmeas : AEMeasurable (fun ω => f ω ^ q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf
  calc
    _ ≤ P Set.univ + ∫⁻ ω, (c * f ω) ^ q ∂P :=
      lintegral_rpow_le_measure_add_larger_order P _ (hf.const_mul c) hp hpq
    _ = 1 + c ^ q * ∫⁻ ω, f ω ^ q ∂P := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq]
      rw [measure_univ, lintegral_const_mul'' _ hmeas]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_right hD _)

end DOZZ.Proofs
