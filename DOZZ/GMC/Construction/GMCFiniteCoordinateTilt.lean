/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTiltJointCutoff
public import DOZZ.GMC.Construction.GMCGeneralTiltBasisProxy

/-! Finite-dimensional coordinate laws for one regularized GMC cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- Sets indexing the total mass and rational lower-box masses of a planar measure. -/
def gmcTiltCoordinateSet : Option (ℚ × ℚ) → Set ℂ
  | none => Set.univ
  | some i => gmcLowerBox i

def gmcTiltCoordinateIndex := TestFn ⊕ Option (ℚ × ℚ)

/-- The joint coordinates of a test field and planar measure, with measure values converted
into real coordinates for convergence-in-measure arguments. -/
def gmcTiltCoordinatePath (q : TestFn → ℝ) (μ : Measure ℂ) :
    gmcTiltCoordinateIndex → ℝ
  | .inl f => q f
  | .inr i => (μ (gmcTiltCoordinateSet i)).toReal

/-- Restriction of the joint field/measure path to a finite coordinate set. -/
def gmcTiltFiniteCoordinatePath (s : Finset gmcTiltCoordinateIndex)
    (q : TestFn → ℝ) (μ : Measure ℂ) : ∀ _i : {i // i ∈ s}, ℝ :=
  fun i => gmcTiltCoordinatePath q μ i.1

theorem measurable_gmcTiltCoordinatePath : Measurable
    (fun p : (TestFn → ℝ) × Measure ℂ => gmcTiltCoordinatePath p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  cases i with
  | inl f => exact (measurable_pi_apply f).comp measurable_fst
  | inr j =>
      have hset : MeasurableSet (gmcTiltCoordinateSet j) := by
        cases j with
        | none => exact MeasurableSet.univ
        | some j => exact gmcLowerBox_measurableSet j
      exact (ENNReal.measurable_toReal.comp
        (Measure.measurable_coe hset)).comp measurable_snd

theorem measurable_gmcTiltFiniteCoordinatePath (s : Finset gmcTiltCoordinateIndex) :
    Measurable (fun p : (TestFn → ℝ) × Measure ℂ =>
      gmcTiltFiniteCoordinatePath s p.1 p.2) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun p : (TestFn → ℝ) × Measure ℂ =>
    gmcTiltCoordinatePath p.1 p.2 i.1)
  exact (measurable_pi_apply i.1).comp measurable_gmcTiltCoordinatePath

/-- At each fixed cutoff, the finite real coordinates of the test field and cutoff GMC have
the Cameron--Martin transported joint law. -/
theorem equatorGFF_tilted_finiteGmcCoordinate_law_at_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (s : Finset gmcTiltCoordinateIndex) (r : ℝ) :
      Measure.map (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f)
        (regularizedGMC P Xc γ r ω))
        (P.withDensity (fun ω => ENNReal.ofReal
          (Real.exp (L ω - gaussianVariance P L / 2)))) =
      Measure.map (fun ω => gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
        ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))) P := by
  classical
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let field : Ω → TestFn → ℝ := fun ω f => X ω f
  let fieldShift : Ω → TestFn → ℝ := fun ω f => X ω f +
    gaussianCovariance P (fun ω' => X ω' f) L
  let leftPath : Ω → (∀ i : {i // i ∈ s}, ℝ) := fun ω =>
    gmcTiltFiniteCoordinatePath s (field ω) (regularizedGMC P Xc γ r ω)
  let rightPath : Ω → (∀ i : {i // i ∈ s}, ℝ) := fun ω =>
    gmcTiltFiniteCoordinatePath s (fieldShift ω)
      ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal
        (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))
  have hfield : Measurable field := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hfieldShift : Measurable fieldShift := by
    rw [measurable_pi_iff]
    intro f
    exact ((hX.2 f).1).add measurable_const
  have hregMeas : Measurable (fun ω => regularizedGMC P Xc γ r ω) :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  have hcovCont : Continuous (fun z : ℂ =>
      gaussianCovariance P (fun ω' => Xc ω' z r) L) :=
    continuous_gaussianCovariance_circle_of_IsGaussianL2Limit P X hX Xc hXc L hL r
  have hweight : Measurable (fun z : ℂ => ENNReal.ofReal
      (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul hcovCont.measurable))
  have hleft : Measurable leftPath := by
    exact (measurable_gmcTiltFiniteCoordinatePath s).comp
      (Measurable.prodMk hfield hregMeas)
  have hregWeighted : Measurable (fun ω =>
      (regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal
        (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L)))) := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    change Measurable (fun ω => (regularizedGMC P Xc γ r ω).withDensity
      (fun z => ENNReal.ofReal
        (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) A)
    have hEval : (fun ω => (regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) A) =
        fun ω => ∫⁻ z, A.indicator (fun z => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) z ∂regularizedGMC P Xc γ r ω := by
      funext ω
      rw [withDensity_apply _ hA, ← lintegral_indicator hA]
    rw [hEval]
    exact (Measure.measurable_lintegral (hweight.indicator hA)).comp hregMeas
  have hright : Measurable rightPath := by
    exact (measurable_gmcTiltFiniteCoordinatePath s).comp
      (Measurable.prodMk hfieldShift hregWeighted)
  have hObs : Measurable (fun p : (TestFn → ℝ) × Measure ℂ =>
      gmcTiltFiniteCoordinatePath s p.1 p.2) := measurable_gmcTiltFiniteCoordinatePath s
  apply Measure.ext
  intro A hA
  let obs : (TestFn → ℝ) × Measure ℂ → (∀ i : {i // i ∈ s}, ℝ) := fun p =>
    gmcTiltFiniteCoordinatePath s p.1 p.2
  let F : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun q μ =>
    if gmcTiltFiniteCoordinatePath s q μ ∈ A then 1 else 0
  have hF : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => F p.1 p.2) := by
    dsimp [F]
    exact Measurable.ite (hA.preimage hObs) measurable_const measurable_const
  have hEqInt := equatorGFF_tilted_test_regularizedGMC_cutoff_lintegral
    P X hX Xc hXc γ r L hL F hF
  have hPreLeft : MeasurableSet (leftPath ⁻¹' A) := hA.preimage hleft
  have hPreRight : MeasurableSet (rightPath ⁻¹' A) := hA.preimage hright
  have hleftInt : (∫⁻ ω in leftPath ⁻¹' A, density ω ∂P) =
      ∫⁻ ω, density ω * F (field ω) (regularizedGMC P Xc γ r ω) ∂P := by
    rw [← lintegral_indicator hPreLeft]
    apply lintegral_congr_ae
    filter_upwards [] with ω
    by_cases hx : leftPath ω ∈ A <;> simp [Set.indicator, F, leftPath, field, hx]
  have hrightInt : (P (rightPath ⁻¹' A)) =
      ∫⁻ ω, F (fieldShift ω)
        ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L)))) ∂P := by
    calc
      P (rightPath ⁻¹' A) =
          ∫⁻ ω, (rightPath ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂P := by
            symm
            rw [lintegral_indicator_const hPreRight 1]
            simp
      _ = ∫⁻ ω, F (fieldShift ω)
          ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal
            (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L)))) ∂P := by
            apply lintegral_congr_ae
            filter_upwards [] with ω
            by_cases hx : rightPath ω ∈ A <;>
              simp [Set.indicator, F, rightPath, fieldShift, hx]
  calc
    _ = ∫⁻ ω in leftPath ⁻¹' A, density ω ∂P := by
      rw [Measure.map_apply hleft hA, withDensity_apply density hPreLeft]
    _ = ∫⁻ ω, density ω * F (field ω) (regularizedGMC P Xc γ r ω) ∂P := hleftInt
    _ = ∫⁻ ω, F (fieldShift ω)
        ((regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L)))) ∂P := hEqInt
    _ = P (rightPath ⁻¹' A) := hrightInt.symm
    _ = _ := by rw [Measure.map_apply hright hA]


end DOZZ.Proofs
