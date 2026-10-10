/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.InversionCircleFamily
public import DOZZ.GMC.CircleAverage

/-! Admissibility of the coupled transformed-circle regularization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- Admissibility depends on measurability, centered Gaussian laws and the covariance kernel. -/
theorem isAdmissibleLogRegularization_of_covariance_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {U : Set ℂ}
    {dens : ℂ → ℝ} {ε₀ : ℝ} {Y Z : Ω → ℝ → ℂ → ℝ}
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hm : ∀ ε, Measurable (fun q : Ω × ℂ => Z q.1 ε q.2))
    (hg : ∀ n (q : Fin n → ℝ × ℂ), (∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀) →
      IsCenteredJointlyGaussian P (fun ω i => Z ω (q i).1 (q i).2))
    (hc : ∀ ε δ x y, gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Z ω δ y) =
      gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y)) :
    IsAdmissibleLogRegularization P U dens ε₀ Z := by
  refine
    { measurableAtScale := hm
      openChart := hY.openChart
      densityContinuous := hY.densityContinuous
      densityPositive := hY.densityPositive
      cutoffPositive := hY.cutoffPositive
      gaussian := hg
      covarianceBound := ?_
      coarseVarianceBound := ?_
      coarseMixedBound := ?_
      offDiagonalLimit := ?_
      fixedCoarseLimit := ?_ }
  · simpa only [hc] using hY.covarianceBound
  · simpa only [gaussianVariance, hc] using hY.coarseVarianceBound
  · simpa only [hc] using hY.coarseMixedBound
  · simpa only [hc] using hY.offDiagonalLimit
  · simpa only [hc] using hY.fixedCoarseLimit

/-- A jointly measurable centered Gaussian family with ordinary circle covariance is admissible
on every open chart, even when constructed by inversion on the source probability space. -/
theorem inversionCircle_admissible_of_geometry
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (Z : Ω → ℂ → ℝ → ℝ)
    (hm : ∀ r, Measurable (fun p : Ω × ℂ => Z p.1 p.2 r))
    (hg : IsGaussianProcess (fun p : ℂ × ℝ => fun ω => Z ω p.1 p.2) P)
    (hmean : ∀ p : ℂ × ℝ, (∫ ω, Z ω p.1 p.2 ∂P) = 0)
    (hcov : ∀ p q : ℂ × ℝ, covariance (fun ω => Z ω p.1 p.2)
        (fun ω => Z ω q.1 q.2) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure p.1 p.2 ∂circleMeasure q.1 q.2)
    (U : Set ℂ) (hU : IsOpen U) :
    IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) 1
      (fun ω ε x => Z ω x (Real.log (1 / ε))) := by
  obtain ⟨Xc, hXc⟩ := exists_equatorGFF_circle_average_witness X hX
  apply isAdmissibleLogRegularization_of_covariance_eq
    (isCircleAverage_admissible P X hX Xc hXc U hU)
    (fun ε => hm (Real.log (1 / ε)))
  · intro n q _
    exact centeredJointlyGaussian_of_isGaussianProcess P
      (fun i ω => Z ω (q i).2 (Real.log (1 / (q i).1)))
      (hg.comp_right (fun i => ((q i).2, Real.log (1 / (q i).1))))
      (fun i => hmean ((q i).2, Real.log (1 / (q i).1)))
  · intro ε δ x y
    have hz : gaussianCovariance P (fun ω => Z ω x (Real.log (1 / ε)))
        (fun ω => Z ω y (Real.log (1 / δ))) =
        covariance (fun ω => Z ω x (Real.log (1 / ε)))
          (fun ω => Z ω y (Real.log (1 / δ))) P := by
      simp only [gaussianCovariance, covariance,
        hmean (x, Real.log (1 / ε)), hmean (y, Real.log (1 / δ)), sub_zero]
    rw [hz, hcov (x, Real.log (1 / ε)) (y, Real.log (1 / δ)),
      isCircleAverage_covariance P X hX Xc hXc]
    obtain ⟨_, _, Y0, _, _, _, _, _, _, hc0⟩ :=
      exists_equatorGFF_circle_L2_geometry X hX
    rw [← hc0 (x, Real.log (1 / ε)) (y, Real.log (1 / δ)),
      ← hc0 (y, Real.log (1 / δ)) (x, Real.log (1 / ε))]
    exact covariance_comm _ _


end DOZZ.Proofs
