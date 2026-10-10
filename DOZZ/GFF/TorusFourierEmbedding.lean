/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusModeHS
public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.FDeriv.Const

/-!
# DOZZ.GFF.TorusFourierEmbedding

Periodize a compactly supported test on a concrete square and expose its Fourier expansion through
Mathlib's unit-torus Hilbert basis.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Topology lp

namespace DOZZ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit two-torus used for the local Fourier coordinates. -/
abbrev GFFUnitTorus2 := UnitAddTorus (Fin 2)

local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by
  infer_instance

/-- Choose the representative in `(-1/2,1/2]²` and scale it to the physical square. -/
noncomputable def torusBoxPoint (L : ℝ) (x : GFFUnitTorus2) : ℂ :=
  let y := (UnitAddTorus.measurableEquivPiIoc (fun _ : Fin 2 => (-1 / 2 : ℝ)) x).1
  ⟨L * y 0, L * y 1⟩

/-- The periodization of a test function on the square of side `L`. -/
noncomputable def torusPeriodizationFunction (L : ℝ) (f : TestFn) : GFFUnitTorus2 → ℂ :=
  fun x => (f (torusBoxPoint L x) : ℂ)

theorem measurable_torusBoxPoint (L : ℝ) : Measurable (torusBoxPoint L) := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 / 2 : ℝ))
  let yMap : GFFUnitTorus2 → Fin 2 → ℝ := fun x => (e x).1
  have hy : Measurable yMap := measurable_subtype_coe.comp e.measurable
  have hpair : Measurable (fun x => (L * yMap x 0, L * yMap x 1)) := by fun_prop
  change Measurable (fun x => Complex.equivRealProdCLM.symm
    (L * yMap x 0, L * yMap x 1))
  exact Complex.equivRealProdCLM.symm.continuous.measurable.comp hpair

theorem measurable_torusPeriodizationFunction (L : ℝ) (f : TestFn) :
    Measurable (torusPeriodizationFunction L f) := by
  unfold torusPeriodizationFunction
  exact (Complex.measurable_ofReal.comp f.continuous.measurable).comp
    (measurable_torusBoxPoint L)

theorem memLp_torusPeriodizationFunction (L : ℝ) (f : TestFn) :
    MemLp (torusPeriodizationFunction L f) 2 (volume : Measure GFFUnitTorus2) := by
  let BCF : ℂ →ᵇ ℝ := f
  have hbound : ∀ x : GFFUnitTorus2,
      ‖torusPeriodizationFunction L f x‖ ≤ ‖BCF‖ := by
    intro x
    simp only [torusPeriodizationFunction, Complex.norm_real]
    exact BCF.norm_coe_le_norm (torusBoxPoint L x)
  exact MemLp.of_bound (measurable_torusPeriodizationFunction L f).aestronglyMeasurable
    ‖BCF‖ (Filter.Eventually.of_forall hbound)

/-- The periodized test as an element of the complex `L²` space on the unit two-torus. -/
noncomputable def torusPeriodizationLp (L : ℝ) (f : TestFn) :
    Lp ℂ 2 (volume : Measure GFFUnitTorus2) :=
  (memLp_torusPeriodizationFunction L f).toLp (torusPeriodizationFunction L f)

/-- Fourier partial sums of a periodized test converge in `L²` on the concrete unit torus. -/
theorem hasSum_torusPeriodization_fourier (L : ℝ) (f : TestFn) :
    HasSum (fun k : Fin 2 → ℤ =>
      UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k •
        UnitAddTorus.mFourierLp 2 k)
      (torusPeriodizationLp L f) :=
  UnitAddTorus.hasSum_mFourier_series_L2 (torusPeriodizationLp L f)

/-- The Fourier coefficient of the periodized test is its integral over the representative unit
square. This is the concrete chart formula used for coefficient estimates. -/
theorem torusPeriodizationCoeff_eq_boxIntegral (L : ℝ) (f : TestFn)
    (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
      ∫ (x : Fin 2 → ℝ) in
        {x | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)},
        UnitAddTorus.mFourier (-k) (fun i => x i) •
          torusPeriodizationFunction L f (fun i => x i) := by
  change (∫ t : GFFUnitTorus2,
      UnitAddTorus.mFourier (-k) t • torusPeriodizationLp L f t) = _
  calc
    (∫ t : GFFUnitTorus2,
        UnitAddTorus.mFourier (-k) t • torusPeriodizationLp L f t) =
        ∫ t : GFFUnitTorus2,
          UnitAddTorus.mFourier (-k) t • torusPeriodizationFunction L f t := by
      apply integral_congr_ae
      filter_upwards [(memLp_torusPeriodizationFunction L f).coeFn_toLp] with t ht
      have ht' : torusPeriodizationLp L f t = torusPeriodizationFunction L f t := by
        simpa [torusPeriodizationLp] using ht
      rw [ht']
    _ = ∫ (x : Fin 2 → ℝ) in
          {x | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)},
          UnitAddTorus.mFourier (-k) (fun i => x i) •
            torusPeriodizationFunction L f (fun i => x i) := by
      exact UnitAddTorus.integral_preimage
        (fun t => UnitAddTorus.mFourier (-k) t • torusPeriodizationFunction L f t)
        (fun _ : Fin 2 => -1 / 2)

/-- On the representative square, the periodization evaluates the original test at the scaled
physical point. -/
theorem torusPeriodizationFunction_rep (L : ℝ) (f : TestFn)
    (x : {x : Fin 2 → ℝ // ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ)
      ((-1 / 2 : ℝ) + 1)}) :
    torusPeriodizationFunction L f (fun i => (x.1 i : UnitAddCircle)) =
      ((f (Complex.equivRealProdCLM.symm
        (L * x.1 0, L * x.1 1)) : ℝ) : ℂ) := by
  let e := UnitAddTorus.measurableEquivPiIoc
    (fun _ : Fin 2 => (-1 / 2 : ℝ))
  have he : e (fun i => (x.1 i : UnitAddCircle)) = x := by
    calc
      e (fun i => (x.1 i : UnitAddCircle)) = e (e.symm x) := by
        rfl
      _ = x := e.apply_symm_apply x
  have hpoint : Complex.equivRealProdCLM.symm
      (L * x.1 0, L * x.1 1) = ⟨L * x.1 0, L * x.1 1⟩ := by
    rw [Complex.equivRealProdCLM_symm_apply]
    rw [Complex.ext_iff]
    constructor <;> simp
  simp [torusPeriodizationFunction, torusBoxPoint, e, he, hpoint]

/-- The continuous real-part map on the complex Fourier `L²` space. -/
noncomputable def torusFourierRealPartCLM :
    Lp ℂ 2 (volume : Measure GFFUnitTorus2) →L[ℝ]
      Lp ℝ 2 (volume : Measure GFFUnitTorus2) :=
  Complex.reCLM.compLpL 2 (volume : Measure GFFUnitTorus2)

/-- Taking real parts preserves the `L²` Fourier expansion of a real test function. -/
theorem hasSum_torusPeriodization_realFourier (L : ℝ) (f : TestFn) :
    HasSum (fun k : Fin 2 → ℤ =>
      torusFourierRealPartCLM
        (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k •
          UnitAddTorus.mFourierLp 2 k))
      (torusFourierRealPartCLM (torusPeriodizationLp L f)) := by
  exact (hasSum_torusPeriodization_fourier L f).mapL torusFourierRealPartCLM

/-- A directional derivative of a compactly supported test function, again as a test function. -/
noncomputable def directionalDerivativeTest (f : TestFn) (v : ℂ) : TestFn := by
  have hfOn : ContDiffOn ℝ (↑(⊤ : ENat)) f Set.univ := f.contDiff.contDiffOn
  have hfderivOn : ContDiffOn ℝ (↑(⊤ : ENat)) (fderiv ℝ f) Set.univ := by
    exact hfOn.fderiv_of_isOpen isOpen_univ (by simp)
  have hfderiv : ContDiff ℝ (↑(⊤ : ENat)) (fderiv ℝ f) := by
    exact contDiffOn_univ.mp hfderivOn
  have hdir : ContDiff ℝ (↑(⊤ : ENat)) (fun z : ℂ => (fderiv ℝ f z) v) := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).contDiff.comp hfderiv
  have hsupport : HasCompactSupport (fun z : ℂ => (fderiv ℝ f z) v) :=
    f.hasCompactSupport.fderiv_apply ℝ v
  exact TestFunction.mk (fun z => (fderiv ℝ f z) v) hdir hsupport (by simp)

@[simp]
theorem directionalDerivativeTest_apply (f : TestFn) (v z : ℂ) :
    directionalDerivativeTest f v z = (fderiv ℝ f z) v := rfl

end DOZZ

end
