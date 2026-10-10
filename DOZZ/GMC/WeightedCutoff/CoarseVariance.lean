module

public import DOZZ.GMC.Annulus.CutoffScale
public import DOZZ.GFFStructure.AnnularCircleEnergy

/-! # Coarse cutoff control without a sign restriction on the cutoff time -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A bounded circle radius and a bounded cutoff time give a uniform variance bound.
This also covers physical cutoffs larger than one. -/
theorem gmcCircle_variance_le_bounded_radius
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (B U T r : ℝ) (hB : 0 ≤ B) (hU : 0 ≤ U) (hrT : r ≤ T)
    (hrU : Real.exp (-r) ≤ U) (x : ℂ) (hx : ‖x‖ ≤ B) :
    gaussianVariance P (fun ω => Xc ω x r) ≤ T + 2 * Real.log (1 + B + U) := by
  let _ := circleMeasure_isProbability x r
  have hpin := integrable_log_normPlus_circleMeasure x r
  have hpoint : ∀ᵐ z ∂circleMeasure x r, Real.log (normPlus z) ≤ Real.log (1 + B + U) := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    have hn : ‖z‖ ≤ U + B := by
      calc
        ‖z‖ = ‖(z - x) + x‖ := by congr 1; abel
        _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
        _ ≤ U + B := by rw [hz]; exact add_le_add hrU hx
    apply Real.log_le_log (by dsimp [normPlus]; positivity)
    dsimp [normPlus]
    exact max_le (by linarith) (by linarith)
  have hpinUpper : (∫ z, Real.log (normPlus z) ∂circleMeasure x r) ≤ Real.log (1 + B + U) := by
    have h := integral_mono_ae hpin (integrable_const (Real.log (1 + B + U))) hpoint
    simpa using h
  rw [gaussianVariance, isCircleAverage_covariance P X hX Xc hXc x x r r]
  change circleSelfEnergy x r ≤ _
  rw [circleSelfEnergy_eq]
  linarith

end DOZZ.Proofs
