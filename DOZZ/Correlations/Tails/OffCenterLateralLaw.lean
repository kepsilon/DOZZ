/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TranslatedTests
public import DOZZ.GMC.Moments.GaussianFDD
public import DOZZ.GMC.GaussianInputs

/-! The translated lateral test law is independent of the insertion center and
of the realization of the equator field. The pin/lateral joint law is not asserted
to be independent of the center. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set

namespace DOZZ.Proofs

/-- The off-center lateral evaluation is centered on every supported test. -/
theorem offCenter_lateral_mean_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (ψ : offCenterTest z) :
    (∫ ω, offCenterLateral X Xc z ψ ω ∂P) = 0 := by
  let : IsProbabilityMeasure P := hX.1
  have hz := notMem_tsupport_of_punctured ψ.property
  unfold offCenterLateral
  rw [← integral_congr_ae (lateralEvaluationL2_ae_eq X Xc hX hc hm z ψ.val hz)]
  rw [lateralEvaluationL2, integral_congr_ae (Lp.coeFn_sub _ _)]
  change (∫ ω, ((equatorGFF_test_memLp X hX ψ.val).toLp (fun ω => X ω ψ.val)) ω -
    (radialIntegralL2 X Xc hc z ψ.val) ω ∂P) = 0
  rw [integral_sub ((Lp.memLp _).integrable (by norm_num))
    ((Lp.memLp _).integrable (by norm_num)),
    integral_congr_ae (MemLp.coeFn_toLp (equatorGFF_test_memLp X hX ψ.val)),
    equatorGFF_test_integral X hX ψ.val,
    radialIntegralL2_integral_eq_zero X Xc hX hc z ψ.val hz, sub_self]

/-- The centered covariance on translated tests is the same origin-coordinate kernel
at every allowed center. -/
theorem offCenter_lateral_translated_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (ψ χ : offCenterTest 0) :
    gaussianCovariance P
      (offCenterLateral X Xc z (translateDiskTest z ψ))
      (offCenterLateral X Xc z (translateDiskTest z χ)) =
        ∫ w : ℂ, ψ.val w * ∫ v : ℂ,
          (-Real.log ‖w - v‖ + Real.log (max ‖w‖ ‖v‖)) * χ.val v := by
  let : IsProbabilityMeasure P := hX.1
  have he := offCenter_lateral_covariance X Xc hX hc hm z hz
    (translatedTest z ψ.val) (translatedTest z χ.val)
    (translateDiskTest z ψ).property (translateDiskTest z χ).property
  have hmψ := offCenter_lateral_mean_zero P X Xc hX hc hm z
    (translateDiskTest z ψ)
  have hmχ := offCenter_lateral_mean_zero P X Xc hX hc hm z
    (translateDiskTest z χ)
  change covariance
    (offCenterLateral X Xc z (translateDiskTest z ψ))
    (offCenterLateral X Xc z (translateDiskTest z χ)) P = _ at he
  rw [covariance, hmψ, hmχ] at he
  simp only [sub_zero] at he
  exact he.trans (translated_lateral_kernel z ψ.val χ.val)

/-- Joint Gaussianity and the common covariance kernel identify every finite translated
lateral vector, even between different probability spaces. -/
theorem offCenter_lateral_translated_fdd_law
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (P' : Measure Ω') (X' : Ω' → Distr) (Xc' : Ω' → ℂ → ℝ → ℝ)
    (hX' : IsEquatorGFF P' X') (hc' : IsCircleAverage P' X' Xc')
    (hm' : Measurable (fun p : Ω' × (ℂ × ℝ) => Xc' p.1 p.2.1 p.2.2))
    (z z' : ℂ) (hz : 2 ≤ ‖z‖) (hz' : 2 ≤ ‖z'‖)
    (ψ : ι → offCenterTest 0) :
    P.map (fun ω i => offCenterLateral X Xc z (translateDiskTest z (ψ i)) ω) =
      P'.map (fun ω i => offCenterLateral X' Xc' z'
        (translateDiskTest z' (ψ i)) ω) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let : IsProbabilityMeasure P' := hX'.1
  have hG := offCenter_lateral_isGaussianProcess X Xc hX hc hm z
  have hG' := offCenter_lateral_isGaussianProcess X' Xc' hX' hc' hm' z'
  apply map_eq_of_centeredJointlyGaussian_of_covariance_eq P P' _ _
    (centeredJointlyGaussian_of_isGaussianProcess P _
      (hG.comp_right (fun i => some (translateDiskTest z (ψ i))))
      (fun i => offCenter_lateral_mean_zero P X Xc hX hc hm z _))
    (centeredJointlyGaussian_of_isGaussianProcess P' _
      (hG'.comp_right (fun i => some (translateDiskTest z' (ψ i))))
      (fun i => offCenter_lateral_mean_zero P' X' Xc' hX' hc' hm' z' _))
  intro i j
  change gaussianCovariance P
    (offCenterLateral X Xc z (translateDiskTest z (ψ i)))
    (offCenterLateral X Xc z (translateDiskTest z (ψ j))) =
      gaussianCovariance P'
        (offCenterLateral X' Xc' z' (translateDiskTest z' (ψ i)))
        (offCenterLateral X' Xc' z' (translateDiskTest z' (ψ j)))
  rw [offCenter_lateral_translated_covariance P X Xc hX hc hm z hz,
    offCenter_lateral_translated_covariance P' X' Xc' hX' hc' hm' z' hz']


end DOZZ.Proofs
