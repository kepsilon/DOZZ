/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusFourierEmbedding

/-!
# DOZZ.GFF.TorusPeriodizationCLM

The concrete torus periodization is a continuous linear map from compactly supported tests to
the torus `L²` space. Its norm is controlled by the zeroth test-function seminorm.
-/

@[expose] public section

open MeasureTheory
open scoped BoundedContinuousFunction ENNReal InnerProductSpace Topology lp

namespace DOZZ

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by infer_instance

/-- Pull a bounded real function back along the measurable representative of the torus box. -/
noncomputable def torusBCFFunction (L : ℝ) (f : ℂ →ᵇ ℝ) : GFFUnitTorus2 → ℂ :=
  fun x => (f (torusBoxPoint L x) : ℂ)

theorem measurable_torusBCFFunction (L : ℝ) (f : ℂ →ᵇ ℝ) :
    Measurable (torusBCFFunction L f) := by
  unfold torusBCFFunction
  exact (Complex.measurable_ofReal.comp f.continuous.measurable).comp
    (measurable_torusBoxPoint L)

theorem memLp_torusBCFFunction (L : ℝ) (f : ℂ →ᵇ ℝ) :
    MemLp (torusBCFFunction L f) 2 (volume : Measure GFFUnitTorus2) := by
  have hbound (x : GFFUnitTorus2) : ‖torusBCFFunction L f x‖ ≤ ‖f‖ := by
    simp only [torusBCFFunction, Complex.norm_real]
    exact f.norm_coe_le_norm (torusBoxPoint L x)
  exact MemLp.of_bound (measurable_torusBCFFunction L f).aestronglyMeasurable
    ‖f‖ (Filter.Eventually.of_forall hbound)

/-- Send a bounded real function on the physical plane to its complex-valued torus `L²`
periodization. -/
noncomputable def torusBCFToLp (L : ℝ) :
    (ℂ →ᵇ ℝ) →ₗ[ℝ] Lp ℂ 2 (volume : Measure GFFUnitTorus2) where
  toFun f := (memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)
  map_add' f g := by
    apply Lp.ext
    have hadd :
        ⇑((memLp_torusBCFFunction L f).toLp (torusBCFFunction L f) +
          (memLp_torusBCFFunction L g).toLp (torusBCFFunction L g)) =ᵐ[
            (volume : Measure GFFUnitTorus2)]
          (↑((memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)) +
            ↑((memLp_torusBCFFunction L g).toLp (torusBCFFunction L g))) :=
      Lp.coeFn_add _ _
    filter_upwards [(memLp_torusBCFFunction L (f + g)).coeFn_toLp,
      (memLp_torusBCFFunction L f).coeFn_toLp,
      (memLp_torusBCFFunction L g).coeFn_toLp, hadd] with x hsum hf hg hadd
    calc
      (memLp_torusBCFFunction L (f + g)).toLp
          (torusBCFFunction L (f + g)) x = torusBCFFunction L (f + g) x := hsum
      _ = torusBCFFunction L f x + torusBCFFunction L g x := by
        simp [torusBCFFunction]
      _ = ((memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)) x +
          ((memLp_torusBCFFunction L g).toLp (torusBCFFunction L g)) x := by
        rw [← hf, ← hg]
      _ = ((memLp_torusBCFFunction L f).toLp (torusBCFFunction L f) +
          (memLp_torusBCFFunction L g).toLp (torusBCFFunction L g)) x := by
        exact hadd.symm
  map_smul' c f := by
    apply Lp.ext
    have hsmulLp :
        ⇑(c • (memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)) =ᵐ[
          (volume : Measure GFFUnitTorus2)]
        c • ↑((memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)) :=
      Lp.coeFn_smul c _
    filter_upwards [(memLp_torusBCFFunction L (c • f)).coeFn_toLp,
      (memLp_torusBCFFunction L f).coeFn_toLp, hsmulLp] with x hsmul hf hsmulLp
    calc
      (memLp_torusBCFFunction L (c • f)).toLp
          (torusBCFFunction L (c • f)) x = torusBCFFunction L (c • f) x := hsmul
      _ = c • torusBCFFunction L f x := by
        simp [torusBCFFunction]
      _ = c • ((memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)) x := by
        rw [← hf]
      _ = (c • (memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)) x := by
        exact hsmulLp.symm

theorem norm_torusBCFToLp_le (L : ℝ) (f : ℂ →ᵇ ℝ) :
    ‖torusBCFToLp L f‖ ≤ ‖f‖ := by
  change ‖(memLp_torusBCFFunction L f).toLp (torusBCFFunction L f)‖ ≤ ‖f‖
  rw [Lp.norm_toLp]
  have hbound : ∀ᵐ x ∂(volume : Measure GFFUnitTorus2),
      ‖torusBCFFunction L f x‖ ≤ ‖f‖ :=
    Filter.Eventually.of_forall fun x => by
      simp only [torusBCFFunction, Complex.norm_real]
      exact f.norm_coe_le_norm (torusBoxPoint L x)
  have hnorm := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
    (measurable_torusBCFFunction L f).aestronglyMeasurable hbound
  have hprob : (volume : Measure GFFUnitTorus2) Set.univ = 1 := by simp
  rw [hprob] at hnorm
  have hnorm' : eLpNorm (torusBCFFunction L f) 2
      (volume : Measure GFFUnitTorus2) ≤ ENNReal.ofReal ‖f‖ := by
    simpa using hnorm
  calc
    (eLpNorm (torusBCFFunction L f) 2 (volume : Measure GFFUnitTorus2)).toReal ≤
        (ENNReal.ofReal ‖f‖).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm'
    _ = ‖f‖ := ENNReal.toReal_ofReal (norm_nonneg _)

/-- The bounded-function periodization operator is continuous, with operator norm at most one. -/
noncomputable def torusBCFToLpCLM (L : ℝ) :
    (ℂ →ᵇ ℝ) →L[ℝ] Lp ℂ 2 (volume : Measure GFFUnitTorus2) :=
  (torusBCFToLp L).mkContinuous 1 (by
    intro f
    simpa using norm_torusBCFToLp_le L f)

/-- The periodization of a test, bundled as a continuous linear map. -/
noncomputable def torusPeriodizationLpCLM (L : ℝ) :
    TestFn →L[ℝ] Lp ℂ 2 (volume : Measure GFFUnitTorus2) :=
  (torusBCFToLpCLM L).comp (TestFunction.toBoundedContinuousFunctionCLM ℝ)

@[simp]
theorem torusPeriodizationLpCLM_apply (L : ℝ) (f : TestFn) :
    torusPeriodizationLpCLM L f = torusPeriodizationLp L f := by
  change (memLp_torusBCFFunction L (f : ℂ →ᵇ ℝ)).toLp
      (torusBCFFunction L (f : ℂ →ᵇ ℝ)) =
    (memLp_torusPeriodizationFunction L f).toLp
      (torusPeriodizationFunction L f)
  apply Lp.ext
  filter_upwards [(memLp_torusPeriodizationFunction L f).coeFn_toLp,
    (memLp_torusBCFFunction L (f : ℂ →ᵇ ℝ)).coeFn_toLp] with x h₁ h₂
  calc
    (memLp_torusBCFFunction L (f : ℂ →ᵇ ℝ)).toLp
        (torusBCFFunction L (f : ℂ →ᵇ ℝ)) x =
        torusBCFFunction L (f : ℂ →ᵇ ℝ) x := h₂
    _ = torusPeriodizationFunction L f x := rfl
    _ = (memLp_torusPeriodizationFunction L f).toLp
        (torusPeriodizationFunction L f) x := h₁.symm

end DOZZ

end
