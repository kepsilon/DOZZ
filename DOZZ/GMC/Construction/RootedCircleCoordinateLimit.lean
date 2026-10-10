/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCircleMassLimit
public import DOZZ.GMC.Construction.GMCFiniteCoordinateTilt
public import DOZZ.GMC.Construction.GMCRootedMeasureFinite

/-! Almost-sure convergence of the field and chaos coordinates under a circle root shift. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- Whenever the point-root insertion is finite, all field and determining measure coordinates
of the single-circle insertion converge on one full-measure set. -/
theorem ae_circleRootedCoordinatePath_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (u : ℂ)
    (hRoot : ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => gmcTiltCoordinatePath
      (fun f => X ω f + γ * circleCross u (n : ℝ) f)
      ((M ω).withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ ^ 2 * ∫ v, gffKernel x v ∂circleMeasure u (n : ℝ))))))
      atTop (𝓝 (gmcTiltCoordinatePath
        (fun f => X ω f + γ * gffRootCovariance u f)
        (gmcRootedMeasure γ u (M ω)))) := by
  filter_upwards [hRoot, gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM u]
    with ω hfinite hAtom
  let _ := hfinite
  apply tendsto_pi_nhds.mpr
  intro i
  cases i with
  | inl f =>
    change Tendsto (fun n : ℕ => X ω f + γ * circleCross u (n : ℝ) f) atTop
      (𝓝 (X ω f + γ * gffRootCovariance u f))
    exact tendsto_const_nhds.add
      (((circleCross_tendsto_gffRootCovariance u f).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).const_mul γ)
  | inr j =>
    have hA : MeasurableSet (gmcTiltCoordinateSet j) := by
      cases j with
      | none => exact MeasurableSet.univ
      | some j => exact gmcLowerBox_measurableSet j
    exact (ENNReal.continuousAt_toReal
      (measure_ne_top (gmcRootedMeasure γ u (M ω)) (gmcTiltCoordinateSet j))).tendsto.comp
        (circleRootedMeasure_mass_tendsto γ u (M ω) hAtom hfinite _ hA)


end DOZZ.Proofs
