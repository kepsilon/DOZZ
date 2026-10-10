/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCovariance
public import DOZZ.GMC.GaussianInputs

/-! Gaussian law of the equator field transported through the punctured inversion chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions

namespace DOZZ.Proofs

/-- The second-moment covariance `DOZZ.gaussianCovariance` of compact field tests is
`DOZZ.gffCov`. -/
theorem equatorGFF_test_gaussianCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (f g : TestFn) :
    gaussianCovariance P (fun ω => X ω f) (fun ω => X ω g) = gffCov f g := by
  unfold gaussianCovariance
  calc
    (∫ ω, X ω f * X ω g ∂P) = covariance (fun ω => X ω f) (fun ω => X ω g) P := by
      rw [ProbabilityTheory.covariance, equatorGFF_test_integral X hX f,
        equatorGFF_test_integral X hX g]
      simp
    _ = gffCov f g := equatorGFF_test_covariance X hX f g

/-- Local compact test evaluations of the inverted field have the ordinary equator GFF law.
The two field models and their probability spaces may be different. -/
theorem equatorGFF_inversion_local_test_fdd_law
    {Ω Ω' ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (f : ι → TestFn) (hf : ∀ i, tsupport (f i : ℂ → ℝ) ⊆ inversionChart) :
    P.map (fun ω i => X ω (inversionTest (f i) (hf i))) =
      P'.map (fun ω i => X' ω (f i)) := by
  classical
  apply map_eq_of_centeredJointlyGaussian_of_covariance_eq P P'
    (fun ω i => X ω (inversionTest (f i) (hf i))) (fun ω i => X' ω (f i))
    (equatorGFF_finite_evaluations_jointly_gaussian P X hX
      (fun i => inversionTest (f i) (hf i)))
    (equatorGFF_finite_evaluations_jointly_gaussian P' X' hX' f)
  intro i j
  rw [equatorGFF_test_gaussianCovariance P X hX,
    equatorGFF_test_gaussianCovariance P' X' hX',
    gffCov_inversionTest]

end DOZZ.Proofs
