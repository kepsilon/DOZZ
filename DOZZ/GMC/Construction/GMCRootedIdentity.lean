/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.Statements.GMC.GffRootCovariance
public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import DOZZ.GMC.EquatorGFFCameronMartin
public import DOZZ.GMC.CircleAverageLimits
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import DOZZ.GFFStructure.AnnularWeakLimit
import Mathlib.MeasureTheory.Measure.Prod

/-! The finite-cutoff rooted identity for functionals of the field coordinates. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The point-root covariance against a smooth test is a continuous function of the root. -/
theorem gffRootCovariance_continuous (f : TestFn) :
    Continuous (fun u : ℂ => gffRootCovariance u f) := by
  simpa [gffRootCovariance] using continuous_testKernelPotential f


private theorem rootedCutoffVariance_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (u : ℂ) (r : ℝ) :
    gaussianVariance P (fun ω => Xc ω u r) = ∫ ω, Xc ω u r ^ 2 ∂P := by
  simp [gaussianVariance, gaussianCovariance, pow_two]


end DOZZ.Proofs
