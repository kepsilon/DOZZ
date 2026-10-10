/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.CircleCross
public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.GMC.GaussianCovariance
public import DOZZ.Statements.GMC.IsGaussianL2Limit
public import DOZZ.GMC.CircleAverage

/-! Direct closure consequences for circle-average witnesses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every circle-average variable is the Gaussian `L²` limit of test evaluations. -/
theorem isCircleAverage_isGaussianL2Limit
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) :
    IsGaussianL2Limit P X (fun ω => Xc ω x r) := by
  let _ := hX
  obtain ⟨f, _, _, hf⟩ := exists_testFn_circleEnergyGap_tendsto_zero x r
  have hcomm n :
      eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P =
        eLpNorm (fun ω => Xc ω x r - X ω (f n)) 2 P :=
    eLpNorm_sub_comm _ _ _ _
  exact ⟨hXc.2.1 x r, ⟨f, by simpa only [hcomm] using hXc.2.2 x r f hf⟩⟩

/-- Cross covariance between a test evaluation and a circle average. -/
theorem isCircleAverage_cross_covariance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) (f : TestFn) :
    gaussianCovariance P (fun ω => X ω f) (fun ω => Xc ω x r) = circleCross x r f := by
  obtain ⟨_, hMean⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  have hCovariance :
      gaussianCovariance P (fun ω => X ω f) (fun ω => Xc ω x r) =
        covariance (fun ω => X ω f) (fun ω => Xc ω x r) P := by
    simp only [gaussianCovariance, ProbabilityTheory.covariance]
    rw [equatorGFF_test_integral X hX f, hMean x r]
    simp
  calc
    gaussianCovariance P (fun ω => X ω f) (fun ω => Xc ω x r) =
        covariance (fun ω => X ω f) (fun ω => Xc ω x r) P := hCovariance
    _ = covariance (fun ω => Xc ω x r) (fun ω => X ω f) P := by
      rw [covariance_comm]
    _ = circleCross x r f := circleAverage_test_covariance P X Xc hX hXc x r f

end DOZZ.Proofs
