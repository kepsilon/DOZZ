/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusLocalDistribution

/-!
# DOZZ.GFF.TorusFourierTestApprox

Cutoff Fourier partial sums for a compactly supported test on one of the concrete torus boxes.
These approximants are used to identify the samplewise local Fourier functional with the G4
isonormal evaluation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open Set Metric
open scoped ENNReal InnerProductSpace Topology lp

namespace DOZZ

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure GFFUnitTorus2) := by
  infer_instance

/-- The real `L²` Fourier term for one coefficient of a periodized test. -/
noncomputable def torusRealFourierTerm (L : ℝ) (f : TestFn) (k : Fin 2 → ℤ) :
    Lp ℝ 2 (volume : Measure GFFUnitTorus2) :=
  torusFourierRealPartCLM
    (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k •
      UnitAddTorus.mFourierLp 2 k)

/-- A finite real Fourier sum in the normalized torus `L²` space. -/
noncomputable def torusRealFourierPartialSum (L : ℝ) (f : TestFn)
    (s : Finset (Fin 2 → ℤ)) : Lp ℝ 2 (volume : Measure GFFUnitTorus2) :=
  s.sum fun k => torusRealFourierTerm L f k

/-- The real Fourier partial sums converge in `L²` to the real part of the periodized test. -/
theorem torusRealFourierPartialSum_tendsto (L : ℝ) (f : TestFn) :
    Tendsto (torusRealFourierPartialSum L f) atTop
      (𝓝 (torusFourierRealPartCLM (torusPeriodizationLp L f))) := by
  exact hasSum_torusPeriodization_realFourier L f

/-- The compactly supported test obtained by multiplying the finite real Fourier sum by the
chosen smooth cutoff. -/
noncomputable def equatorLocalFourierPartialTest (R L : ℝ) (hR : 0 < R)
    (f : TestFn) (s : Finset (Fin 2 → ℤ)) : TestFn :=
  s.sum fun k =>
    (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re •
        localTorusCosTest R L hR k -
      (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im •
        localTorusSinTest R L hR k

theorem equatorLocalFourierPartialTest_apply (R L : ℝ) (hR : 0 < R)
    (f : TestFn) (s : Finset (Fin 2 → ℤ)) (z : ℂ) :
    equatorLocalFourierPartialTest R L hR f s z =
      s.sum fun k =>
        ((UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re *
            localTorusCosTest R L hR k z -
          (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im *
            localTorusSinTest R L hR k z) := by
  simp [equatorLocalFourierPartialTest, smul_eq_mul]

/-- The common Haar mode limit agrees almost everywhere with the G4 evaluation of the
unnormalized cutoff cosine mode, after undoing the Sobolev weight. -/
theorem ae_equatorHaarCommonEval_cosScale (r : ℕ) (k : Fin 2 → ℤ) :
    (fun ω => equatorHaarCommonEval (gffLocalCosSobolevModeTest r k) ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => (torusSobolevWeight k)⁻¹ *
        equatorFieldL2 (localTorusCosTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) ω) := by
  have hmode := ae_equatorHaarCommonEval_localMode (r, Sum.inl k)
  have hfield : equatorFieldL2 (gffLocalCosSobolevModeTest r k) =
      (torusSobolevWeight k)⁻¹ • equatorFieldL2
        (localTorusCosTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) := by
    simp [gffLocalCosSobolevModeTest, map_smul]
  have hcoe : (fun ω => equatorFieldL2 (gffLocalCosSobolevModeTest r k) ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => (torusSobolevWeight k)⁻¹ * equatorFieldL2
        (localTorusCosTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) ω) := by
    rw [hfield]
    filter_upwards [Lp.coeFn_smul (torusSobolevWeight k)⁻¹
      (equatorFieldL2 (localTorusCosTest (gffLocalModeRadius r)
        (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k))] with ω hω
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hω
  simpa only [gffLocalSobolevModeTest] using hmode.trans hcoe

/-- The sine version of `ae_equatorHaarCommonEval_cosScale`. -/
theorem ae_equatorHaarCommonEval_sinScale (r : ℕ) (k : Fin 2 → ℤ) :
    (fun ω => equatorHaarCommonEval (gffLocalSinSobolevModeTest r k) ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => (torusSobolevWeight k)⁻¹ *
        equatorFieldL2 (localTorusSinTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) ω) := by
  have hmode := ae_equatorHaarCommonEval_localMode (r, Sum.inr k)
  have hfield : equatorFieldL2 (gffLocalSinSobolevModeTest r k) =
      (torusSobolevWeight k)⁻¹ • equatorFieldL2
        (localTorusSinTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) := by
    simp [gffLocalSinSobolevModeTest, map_smul]
  have hcoe : (fun ω => equatorFieldL2 (gffLocalSinSobolevModeTest r k) ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => (torusSobolevWeight k)⁻¹ * equatorFieldL2
        (localTorusSinTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) ω) := by
    rw [hfield]
    filter_upwards [Lp.coeFn_smul (torusSobolevWeight k)⁻¹
      (equatorFieldL2 (localTorusSinTest (gffLocalModeRadius r)
        (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k))] with ω hω
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hω
  simpa only [gffLocalSobolevModeTest] using hmode.trans hcoe

/-- A finite local Fourier evaluation is almost everywhere the G4 evaluation of the corresponding
cutoff Fourier test. -/
theorem ae_equatorLocalFourierPartialEval_eq_equatorFieldL2
    (r : ℕ) (f : TestFn) (s : Finset (Fin 2 → ℤ))
    (hsupp : Function.support f ⊆
      ball (0 : ℂ) (gffLocalModeRadius r - 1)) :
    (fun ω => equatorLocalFourierPartialEval r f s ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => equatorFieldL2
        (equatorLocalFourierPartialTest (gffLocalModeRadius r)
          (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) f s) ω) := by
  classical
  let R := gffLocalModeRadius r
  let L := gffLocalModeBoxSide r
  have hL : 0 < L := by
    dsimp [L, gffLocalModeBoxSide, gffLocalModeRadius]
    positivity
  have hRbox : gffLocalModeRadius r - 1 + 2 < gffLocalModeBoxSide r / 2 := by
    dsimp [gffLocalModeRadius, gffLocalModeBoxSide]
    ring_nf
    linarith
  have hcoords : ∀ᵐ ω ∂GaussianFields.scaleSpaceWhiteNoiseMeasure 2,
      ∀ k : Fin 2 → ℤ,
        equatorHaarCommonEval (gffLocalCosSobolevModeTest r k) ω =
          (torusSobolevWeight k)⁻¹ * equatorFieldL2
            (localTorusCosTest (gffLocalModeRadius r)
              (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) ω ∧
        equatorHaarCommonEval (gffLocalSinSobolevModeTest r k) ω =
          (torusSobolevWeight k)⁻¹ * equatorFieldL2
            (localTorusSinTest (gffLocalModeRadius r)
              (gffLocalModeBoxSide r) (gffLocalModeRadius_pos r) k) ω := by
    filter_upwards [ae_all_iff.mpr (fun k =>
      ae_equatorHaarCommonEval_cosScale r k),
      ae_all_iff.mpr (fun k =>
      ae_equatorHaarCommonEval_sinScale r k)] with ω hcos hsin
    intro k
    constructor
    · exact hcos k
    · exact hsin k
  let term : (Fin 2 → ℤ) → TestFn := fun k =>
    (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re •
        localTorusCosTest R L (gffLocalModeRadius_pos r) k -
      (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im •
        localTorusSinTest R L (gffLocalModeRadius_pos r) k
  have hsumLp : equatorFieldL2 (s.sum term) = s.sum (fun k => equatorFieldL2 (term k)) := by
    simp only [map_sum]
  have hsumAE : (fun ω => equatorFieldL2 (s.sum term) ω) =ᵐ[
      GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => s.sum fun k => equatorFieldL2 (term k) ω) := by
    filter_upwards [Lp.coeFn_finsetSum s (fun k => equatorFieldL2 (term k))] with ω hω
    simpa only [hsumLp, Finset.sum_apply] using hω
  have htermAE (k : Fin 2 → ℤ) :
      (fun ω => equatorFieldL2 (term k) ω) =ᵐ[
        GaussianFields.scaleSpaceWhiteNoiseMeasure 2]
      (fun ω => (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re *
          equatorFieldL2 (localTorusCosTest R L (gffLocalModeRadius_pos r) k) ω -
        (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im *
          equatorFieldL2 (localTorusSinTest R L (gffLocalModeRadius_pos r) k) ω) := by
    let a := (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).re
    let b := (UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k).im
    have hmap : equatorFieldL2 (term k) =
        a • equatorFieldL2 (localTorusCosTest R L (gffLocalModeRadius_pos r) k) -
          b • equatorFieldL2 (localTorusSinTest R L (gffLocalModeRadius_pos r) k) := by
      simp [term, a, b, map_sub, map_smul]
    rw [hmap]
    filter_upwards [Lp.coeFn_sub
        (a • equatorFieldL2 (localTorusCosTest R L (gffLocalModeRadius_pos r) k))
        (b • equatorFieldL2 (localTorusSinTest R L (gffLocalModeRadius_pos r) k)),
      Lp.coeFn_smul a
        (equatorFieldL2 (localTorusCosTest R L (gffLocalModeRadius_pos r) k)),
      Lp.coeFn_smul b
        (equatorFieldL2 (localTorusSinTest R L (gffLocalModeRadius_pos r) k))] with ω hsub hcos hsin
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using
      hsub.trans (congrArg₂ (fun x y : ℝ => x - y) hcos hsin)
  filter_upwards [hcoords, hsumAE,
    ae_all_iff.mpr fun k => htermAE k] with ω hω hsum hterm
  change s.sum (fun k =>
    (torusH2WeightedFourierCoeffCLM L f k).re *
        equatorHaarCommonEval (gffLocalCosSobolevModeTest r k) ω -
      (torusH2WeightedFourierCoeffCLM L f k).im *
        equatorHaarCommonEval (gffLocalSinSobolevModeTest r k) ω) =
    equatorFieldL2 (s.sum term) ω
  rw [hsum]
  apply Finset.sum_congr rfl
  intro k hk
  have hwpos : 0 < torusSobolevWeight k := by
    dsimp [torusSobolevWeight]
    positivity
  have hcoeff := torusH2WeightedFourierCoeffCLM_apply L
    (gffLocalModeRadius r - 1) hL hRbox f hsupp k
  rw [hcoeff]
  have hcos := hω k |>.1
  have hsin := hω k |>.2
  have hcosScale : equatorHaarCommonEval
      (gffLocalCosSobolevModeTest r k) ω =
        (torusSobolevWeight k)⁻¹ *
          equatorFieldL2 (localTorusCosTest R L (gffLocalModeRadius_pos r) k) ω := by
    exact hcos
  have hsinScale : equatorHaarCommonEval
      (gffLocalSinSobolevModeTest r k) ω =
        (torusSobolevWeight k)⁻¹ *
          equatorFieldL2 (localTorusSinTest R L (gffLocalModeRadius_pos r) k) ω := by
    exact hsin
  rw [hcosScale, hsinScale]
  rw [hterm k]
  rw [Complex.real_smul]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  field_simp [ne_of_gt hwpos]
  ring

end DOZZ

end
