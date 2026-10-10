/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusFourierEmbedding
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Complex.Norm

/-!
# DOZZ.GFF.LocalFourierEstimates

Fourier integration by parts estimates for the scaled compactly supported tests in a torus box.
-/

@[expose] public section

open MeasureTheory
open Set Metric
open scoped FourierTransform InnerProductSpace Topology

namespace DOZZ

/-- Rescale a compactly supported test from a physical box to the unit square. -/
noncomputable def gffUnitBoxFunction (L : ℝ) (f : TestFn) : ℂ → ℝ :=
  fun z => f (L • z)

theorem gffUnitBoxFunction_contDiff (L : ℝ) (f : TestFn) :
    ContDiff ℝ (↑(⊤ : ENat)) (gffUnitBoxFunction L f) := by
  unfold gffUnitBoxFunction
  exact f.contDiff.comp (contDiff_const_smul L)

theorem gffUnitBoxFunction_hasCompactSupport (L : ℝ) (hL : L ≠ 0) (f : TestFn) :
    HasCompactSupport (gffUnitBoxFunction L f) := by
  exact f.hasCompactSupport.comp_smul hL

/-- The derivative of a smooth compactly supported complex function in a fixed direction is
compactly supported and smooth. -/
noncomputable def complexDirectionalDerivative (f : ℂ → ℂ) (v : ℂ) : ℂ → ℂ :=
  fun z => (fderiv ℝ f z) v

theorem complexDirectionalDerivative_contDiff {f : ℂ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ENat)) f)
    (v : ℂ) : ContDiff ℝ (↑(⊤ : ENat)) (complexDirectionalDerivative f v) := by
  unfold complexDirectionalDerivative
  have hfOn : ContDiffOn ℝ (↑(⊤ : ENat)) f Set.univ := contDiffOn_univ.mpr hf
  have hfdOn : ContDiffOn ℝ (↑(⊤ : ENat)) (fderiv ℝ f) Set.univ :=
    hfOn.fderiv_of_isOpen isOpen_univ (by simp)
  have hfd : ContDiff ℝ (↑(⊤ : ENat)) (fderiv ℝ f) := contDiffOn_univ.mp hfdOn
  exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp hfd

theorem complexDirectionalDerivative_hasCompactSupport {f : ℂ → ℂ}
    (hf : HasCompactSupport f) (v : ℂ) :
    HasCompactSupport (complexDirectionalDerivative f v) := by
  unfold complexDirectionalDerivative
  exact hf.fderiv_apply (𝕜 := ℝ) v

private theorem realInnerComplex_eq (z w : ℂ) :
    ⟪z, w⟫_ℝ = z.re * w.re + z.im * w.im := by
  simp [Complex.mul_re]
  ring

private theorem complexFourier_integrable {f : ℂ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ENat)) f)
    (hcompact : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hcompact

/-- Integration by parts for the Fourier integral in a fixed direction. -/
theorem fourier_complexDirectionalDerivative {f : ℂ → ℂ}
    (hf : ContDiff ℝ (↑(⊤ : ENat)) f) (hcompact : HasCompactSupport f) (v w : ℂ) :
    𝓕 (complexDirectionalDerivative f v) w =
      (2 * Real.pi * Complex.I * ((innerSL ℝ) w v : ℂ)) * 𝓕 f w := by
  let df : ℂ → ℂ →L[ℝ] ℂ := fun z => fderiv ℝ f z
  have hfOn : ContDiffOn ℝ (↑(⊤ : ENat)) f Set.univ := contDiffOn_univ.mpr hf
  have hdfOn : ContDiffOn ℝ (↑(⊤ : ENat)) (fderiv ℝ f) Set.univ :=
    hfOn.fderiv_of_isOpen isOpen_univ (by simp)
  have hdf : ContDiff ℝ (↑(⊤ : ENat)) (fderiv ℝ f) := contDiffOn_univ.mp hdfOn
  have hdfcont : Continuous df := hdf.continuous
  have hdfcompact : HasCompactSupport df := hcompact.fderiv (𝕜 := ℝ)
  have hdfint : Integrable df := hdfcont.integrable_of_hasCompactSupport hdfcompact
  have hfint : Integrable f := complexFourier_integrable hf hcompact
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  have htransform := Real.fourier_fderiv (E := ℂ) hfint hdiff hdfint
  have happly := congrArg (fun T : ℂ →L[ℝ] ℂ => T v) (congrFun htransform w)
  rw [Real.fourier_continuousLinearMap_apply hdfint] at happly
  have hcoords : (innerSL ℝ) w v = w.re * v.re + w.im * v.im := by
    rw [innerSL_apply_apply, realInnerComplex_eq]
  simp only [VectorFourier.fourierSMulRight_apply, neg_apply,
    smul_eq_mul] at happly
  rw [hcoords] at happly
  rw [Complex.real_smul] at happly
  rw [hcoords]
  convert happly using 1
  · rfl
  · push_cast
    ring

/-- Repeated directional derivatives, used to obtain rapid decay of the local Fourier
coefficients from compact support and smoothness. -/
noncomputable def complexDirectionalDerivativeIterate (v : ℂ) :
    ℕ → (ℂ → ℂ) → ℂ → ℂ
  | 0, f => f
  | n + 1, f => complexDirectionalDerivative
      (complexDirectionalDerivativeIterate v n f) v

theorem complexDirectionalDerivativeIterate_contDiff (v : ℂ) (n : ℕ)
    {f : ℂ → ℂ} (hf : ContDiff ℝ (↑(⊤ : ENat)) f) :
    ContDiff ℝ (↑(⊤ : ENat)) (complexDirectionalDerivativeIterate v n f) := by
  induction n with
  | zero => simpa [complexDirectionalDerivativeIterate] using hf
  | succ n ih =>
      simpa [complexDirectionalDerivativeIterate] using
        complexDirectionalDerivative_contDiff ih v

theorem complexDirectionalDerivativeIterate_hasCompactSupport (v : ℂ) (n : ℕ)
    {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (complexDirectionalDerivativeIterate v n f) := by
  induction n with
  | zero => simpa [complexDirectionalDerivativeIterate] using hf
  | succ n ih =>
      simpa [complexDirectionalDerivativeIterate] using
        complexDirectionalDerivative_hasCompactSupport ih v


/-- The real two-torus monomial is the ordinary Euclidean Fourier character on its representative
square. -/
private theorem unitTorus_mFourier_neg_eq_exp (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (-2 * Real.pi * Complex.I * (k 0 : ℝ) * x 0) *
        Complex.exp (-2 * Real.pi * Complex.I * (k 1 : ℝ) * x 1) := by
  rw [UnitAddTorus.mFourier_neg]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Fin.prod_univ_two,
    fourier_coe_apply]
  rw [map_mul]
  rw [← Complex.exp_conj, ← Complex.exp_conj]
  congr 1 <;> simp [map_mul, map_ofNat]

/-- A test function restricted to the unit square and scaled from a physical box of side `L`. -/
noncomputable def gffUnitBoxComplexFunction (L : ℝ) (f : TestFn) : ℂ → ℂ :=
  fun z => (gffUnitBoxFunction L f z : ℂ)

theorem gffUnitBoxComplexFunction_contDiff (L : ℝ) (f : TestFn) :
    ContDiff ℝ (↑(⊤ : ENat)) (gffUnitBoxComplexFunction L f) := by
  unfold gffUnitBoxComplexFunction
  exact Complex.ofRealCLM.contDiff.comp (gffUnitBoxFunction_contDiff L f)

theorem gffUnitBoxComplexFunction_hasCompactSupport (L : ℝ) (hL : L ≠ 0)
    (f : TestFn) : HasCompactSupport (gffUnitBoxComplexFunction L f) := by
  apply (gffUnitBoxFunction_hasCompactSupport L hL f).mono
  intro z hz
  change ((gffUnitBoxFunction L f z : ℝ) : ℂ) ≠ 0 at hz
  intro hzero
  apply hz
  exact_mod_cast hzero

/-- Scaling a physical directional derivative back to the unit box contributes the expected
factor `L⁻¹`. -/
theorem gffUnitBoxComplexFunction_directionalDerivative (L : ℝ) (hL : L ≠ 0)
    (f : TestFn) (v z : ℂ) :
    gffUnitBoxComplexFunction L (directionalDerivativeTest f v) z =
      (L : ℂ)⁻¹ * complexDirectionalDerivative
        (gffUnitBoxComplexFunction L f) v z := by
  have hderiv :
      fderiv ℝ (fun y : ℂ => ((f (L • y) : ℝ) : ℂ)) z =
        (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp
          (L • fderiv ℝ (f : ℂ → ℝ) (L • z)) := by
    change fderiv ℝ (Complex.ofReal ∘ (fun y : ℂ => f (L • y))) z = _
    rw [fderiv_comp]
    · rw [show fderiv ℝ Complex.ofReal (f (L • z)) = Complex.ofRealCLM from by
          change fderiv ℝ (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) _ = _
          exact ContinuousLinearMap.fderiv _]
      rw [fderiv_comp_smul]
    · exact Complex.differentiable_ofReal.differentiableAt
    · exact (f.contDiff.differentiable (by simp)).differentiableAt.comp z
        (by fun_prop)
  change ((fderiv ℝ (f : ℂ → ℝ) (L • z)) v : ℂ) =
    (L : ℂ)⁻¹ * (fderiv ℝ (gffUnitBoxComplexFunction L f) z) v
  rw [show fderiv ℝ (gffUnitBoxComplexFunction L f) z =
      fderiv ℝ (fun y : ℂ => ((f (L • y) : ℝ) : ℂ)) z by rfl, hderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofRealCLM_apply]
  have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  field_simp [hL']
  rw [← Complex.ofReal_mul]

/-- A physical derivative rescaled by the box side so that it becomes a unit-box derivative. -/
noncomputable def unitBoxDirectionalDerivativeTest (L : ℝ) (f : TestFn) (v : ℂ) : TestFn :=
  L • directionalDerivativeTest f v

theorem support_unitBoxDirectionalDerivativeTest_subset (L R : ℝ) (f : TestFn)
    (v : ℂ) (hf : Function.support f ⊆ ball (0 : ℂ) R) :
    Function.support (unitBoxDirectionalDerivativeTest L f v) ⊆
      ball (0 : ℂ) (R + 1) := by
  have htsupp : tsupport f ⊆ closedBall (0 : ℂ) R := by
    change closure (Function.support f) ⊆ closedBall (0 : ℂ) R
    exact (closure_mono hf).trans closure_ball_subset_closedBall
  have hderiv : Function.support (directionalDerivativeTest f v) ⊆ tsupport f := by
    calc
      Function.support (directionalDerivativeTest f v) ⊆
          tsupport (directionalDerivativeTest f v) := subset_tsupport _
      _ ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ v
  intro z hz
  have hz' : z ∈ Function.support (directionalDerivativeTest f v) := by
    by_contra hn
    have hzero : directionalDerivativeTest f v z = 0 := by
      simpa [Function.mem_support] using hn
    apply hz
    simp [unitBoxDirectionalDerivativeTest, hzero]
  have hzball : z ∈ closedBall (0 : ℂ) R := htsupp (hderiv hz')
  exact closedBall_subset_ball (by linarith) hzball

theorem gffUnitBoxComplexFunction_unitBoxDirectionalDerivativeTest
    (L : ℝ) (hL : L ≠ 0) (f : TestFn) (v z : ℂ) :
    gffUnitBoxComplexFunction L (unitBoxDirectionalDerivativeTest L f v) z =
      complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
  rw [unitBoxDirectionalDerivativeTest]
  calc
    gffUnitBoxComplexFunction L (L • directionalDerivativeTest f v) z =
        (L : ℂ) * gffUnitBoxComplexFunction L (directionalDerivativeTest f v) z := by
      simp [gffUnitBoxComplexFunction, gffUnitBoxFunction, Complex.real_smul]
    _ = complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v z := by
      rw [gffUnitBoxComplexFunction_directionalDerivative L hL]
      have hL' : (L : ℂ) ≠ 0 := by exact_mod_cast hL
      field_simp [hL']

/-- If a physical test is supported in a ball strictly smaller than half the box width, its
scaled representative is supported inside the centered fundamental square. -/
theorem gffUnitBoxComplexFunction_support_subset_centeredBox
    (L R : ℝ) (hL : 0 < L) (hRL : R < L / 2)
    (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) R) :
    Function.support (gffUnitBoxComplexFunction L f) ⊆
      {z : ℂ | z.re ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ) ∧
        z.im ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)} := by
  intro z hz
  have hval : gffUnitBoxFunction L f z ≠ 0 := by
    intro hzero
    apply hz
    simp [gffUnitBoxComplexFunction, hzero]
  have hscaled : L • z ∈ Function.support f := by
    change f (L • z) ≠ 0
    exact_mod_cast hval
  have hzball : L • z ∈ ball (0 : ℂ) R := hf hscaled
  have hnorm : ‖L • z‖ < R := by
    simpa [Metric.mem_ball, dist_zero_right] using hzball
  have hnormz : ‖z‖ < R / L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL] at hnorm
    apply (lt_div_iff₀ hL).2
    simpa [mul_comm] using hnorm
  have hsmall : R / L < 1 / 2 := by
    apply (div_lt_iff₀ hL).2
    nlinarith [hRL]
  have hre : |z.re| < 1 / 2 := by
    exact (Complex.abs_re_le_norm z).trans_lt (hnormz.trans hsmall)
  have him : |z.im| < 1 / 2 := by
    exact (Complex.abs_im_le_norm z).trans_lt (hnormz.trans hsmall)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · linarith [abs_lt.mp hre]
  · linarith [abs_lt.mp hre]
  · linarith [abs_lt.mp him]
  · linarith [abs_lt.mp him]

private def centeredUnitBox : Set (Fin 2 → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)}

private theorem measurableSet_centeredUnitBox : MeasurableSet centeredUnitBox := by
  have hEq : centeredUnitBox =
      ⋂ i : Fin 2, {x : Fin 2 → ℝ | x i ∈ Set.Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ)} := by
    ext x
    simp [centeredUnitBox]
    norm_num
  rw [hEq]
  exact MeasurableSet.iInter fun i : Fin 2 =>
    measurableSet_Ioc.preimage (measurable_pi_apply (X := fun _ : Fin 2 => ℝ) i)

/-- A compactly supported function whose support lies in a measurable set has the same total
integral as its integral over that set. -/
private theorem integral_eq_setIntegral_of_support_subset_box {α : Type*}
    [MeasurableSpace α] [CompleteSpace ℂ] {μ : Measure α} {s : Set α}
    (hs : MeasurableSet s) {F : α → ℂ} (hF : Function.support F ⊆ s) :
    (∫ x, F x ∂μ) = ∫ x in s, F x ∂μ := by
  calc
    (∫ x, F x ∂μ) = ∫ x, s.indicator F x ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ s
      · simp [hx]
      · have hzero : F x = 0 := by
          by_contra hn
          exact hx (hF hn)
        simp [hx, hzero]
    _ = ∫ x in s, F x ∂μ := by rw [integral_indicator (μ := μ) hs]

private theorem unitTorus_mFourier_neg_eq_exp_dot
    (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) :
    UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) =
      Complex.exp (-2 * Real.pi * Complex.I *
        ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) := by
  rw [unitTorus_mFourier_neg_eq_exp]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

noncomputable def unitTorusFourierFrequency (k : Fin 2 → ℤ) : ℂ :=
  (k 0 : ℂ) + (k 1 : ℂ) * Complex.I

theorem innerSL_unitTorusFourierFrequency
    (z : ℂ) (k : Fin 2 → ℤ) :
    (innerSL ℝ) z (unitTorusFourierFrequency k) =
      z.re * (k 0 : ℝ) + z.im * (k 1 : ℝ) := by
  rw [innerSL_apply_apply, realInnerComplex_eq]
  simp [unitTorusFourierFrequency, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im]

theorem unitTorusFourierFrequency_innerSL
    (k : Fin 2 → ℤ) (z : ℂ) :
    (innerSL ℝ) (unitTorusFourierFrequency k) z =
      z.re * (k 0 : ℝ) + z.im * (k 1 : ℝ) := by
  rw [innerSL_apply_apply, realInnerComplex_eq]
  simp [unitTorusFourierFrequency, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im] ; ring

private noncomputable def unitTorusFourierIntegrand
    (L : ℝ) (f : TestFn) (k : Fin 2 → ℤ) (x : Fin 2 → ℝ) : ℂ :=
  Complex.exp (-2 * Real.pi * Complex.I *
    ((k 0 : ℝ) * x 0 + (k 1 : ℝ) * x 1)) *
      gffUnitBoxComplexFunction L f (Complex.measurableEquivPi.symm x)

private theorem unitTorusFourierIntegrand_measurableEquivPi
    (L : ℝ) (f : TestFn) (k : Fin 2 → ℤ) (z : ℂ) :
      Complex.exp
        (↑(-2 * Real.pi * ((innerSL ℝ) z (unitTorusFourierFrequency k))) *
          Complex.I) * gffUnitBoxComplexFunction L f z =
      unitTorusFourierIntegrand L f k (Complex.measurableEquivPi z) := by
  unfold unitTorusFourierIntegrand
  rw [Complex.measurableEquivPi.symm_apply_apply z]
  congr 1
  rw [innerSL_unitTorusFourierFrequency]
  simp [Complex.measurableEquivPi_apply]
  ring_nf

private theorem support_unitTorusFourierIntegrand_subset_box
    (L R : ℝ) (hL : 0 < L) (hRL : R < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (k : Fin 2 → ℤ) :
    Function.support (unitTorusFourierIntegrand L f k) ⊆ centeredUnitBox := by
  intro x hx
  have hscaled : gffUnitBoxComplexFunction L f
      (Complex.measurableEquivPi.symm x) ≠ 0 := by
    intro hzero
    apply hx
    have hzero' : gffUnitBoxComplexFunction L f
        (x 0 + x 1 * Complex.I) = 0 := by
      simpa only [Complex.measurableEquivPi_symm_apply] using hzero
    simp [unitTorusFourierIntegrand, hzero']
  have hz : Complex.measurableEquivPi.symm x ∈
      Function.support (gffUnitBoxComplexFunction L f) := hscaled
  rcases gffUnitBoxComplexFunction_support_subset_centeredBox L R hL hRL f hf hz with
    ⟨hre, him⟩
  change ∀ i : Fin 2, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)
  intro i
  fin_cases i
  · change x 0 ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)
    constructor
    · simpa [Complex.measurableEquivPi_symm_apply] using hre.1
    · have hupper : x 0 ≤ 1 / 2 := by
        simpa [Complex.measurableEquivPi_symm_apply] using hre.2
      norm_num at hupper ⊢
      linarith
  · change x 1 ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)
    constructor
    · simpa [Complex.measurableEquivPi_symm_apply] using him.1
    · have hupper : x 1 ≤ 1 / 2 := by
        simpa [Complex.measurableEquivPi_symm_apply] using him.2
      norm_num at hupper ⊢
      linarith

/-- A torus Fourier coefficient of a test supported inside the fundamental box is the ordinary
Fourier transform of its scaled compactly supported extension. -/
theorem torusPeriodizationCoeff_eq_fourier
    (L R : ℝ) (hL : 0 < L) (hRL : R < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
      𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) := by
  let E := Complex.measurableEquivPi
  let H := unitTorusFourierIntegrand L f k
  have hHsupport : Function.support H ⊆ centeredUnitBox :=
    support_unitTorusFourierIntegrand_subset_box L R hL hRL f hf k
  have hbox := torusPeriodizationCoeff_eq_boxIntegral L f k
  calc
    UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k =
        ∫ x in centeredUnitBox,
          UnitAddTorus.mFourier (-k) (fun i => (x i : UnitAddCircle)) •
            torusPeriodizationFunction L f (fun i => (x i : UnitAddCircle)) := by
      simpa [centeredUnitBox] using hbox
    _ = ∫ x in centeredUnitBox, H x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_centeredUnitBox] with x hx
      simp only [H, unitTorusFourierIntegrand, smul_eq_mul]
      rw [unitTorus_mFourier_neg_eq_exp_dot]
      congr 1
      have hx' : x ∈ {x : Fin 2 → ℝ |
          ∀ i, x i ∈ Set.Ioc (-1 / 2 : ℝ) ((-1 / 2 : ℝ) + 1)} := by
        simpa [centeredUnitBox] using hx
      have hrep := torusPeriodizationFunction_rep L f ⟨x, hx'⟩
      have hrep' : torusPeriodizationFunction L f
          (fun i => (x i : UnitAddCircle)) =
          ((f (Complex.equivRealProdCLM.symm (L * x 0, L * x 1)) : ℝ) : ℂ) := by
        simpa using hrep
      have hpoint : Complex.equivRealProdCLM.symm (L * x 0, L * x 1) =
          L • Complex.measurableEquivPi.symm x := by
        rw [Complex.equivRealProdCLM_symm_apply, Complex.measurableEquivPi_symm_apply]
        apply Complex.ext
        · simp [Complex.real_smul]
        · simp [Complex.real_smul]
      rw [hrep', hpoint]
      rfl
    _ = ∫ x, H x := by
      symm
      exact integral_eq_setIntegral_of_support_subset_box
        (μ := volume) measurableSet_centeredUnitBox hHsupport
    _ = 𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) := by
      symm
      calc
        𝓕 (gffUnitBoxComplexFunction L f) (unitTorusFourierFrequency k) =
            ∫ z, Complex.exp
              (↑(-2 * Real.pi * ((innerSL ℝ) z (unitTorusFourierFrequency k))) *
                Complex.I) * gffUnitBoxComplexFunction L f z := by
          rw [Real.fourier_eq']
          simp_rw [smul_eq_mul]
          apply integral_congr_ae
          filter_upwards [] with z
          congr 1
        _ = ∫ z, H (E z) := by
          apply integral_congr_ae
          filter_upwards [] with z
          simpa [H, E] using
            unitTorusFourierIntegrand_measurableEquivPi L f k z
        _ = ∫ x, H x := (Complex.volume_preserving_equiv_pi).integral_comp' H

/-- Differentiating a test in a physical coordinate multiplies its unit-torus Fourier
coefficient by the corresponding frequency. -/
theorem torusPeriodizationCoeff_unitBoxDirectionalDerivative
    (L R : ℝ) (hL : 0 < L) (hRbox : R + 1 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (v : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodizationLp L (unitBoxDirectionalDerivativeTest L f v)) k =
      (2 * Real.pi * Complex.I *
        ((innerSL ℝ) (unitTorusFourierFrequency k) v : ℂ)) *
        UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  have hf' : Function.support f ⊆ ball (0 : ℂ) (R + 1) :=
    hf.trans (ball_subset_ball (by linarith))
  have hdf' := support_unitBoxDirectionalDerivativeTest_subset L R f v hf
  have hfun : gffUnitBoxComplexFunction L (unitBoxDirectionalDerivativeTest L f v) =
      complexDirectionalDerivative (gffUnitBoxComplexFunction L f) v := by
    funext z
    exact gffUnitBoxComplexFunction_unitBoxDirectionalDerivativeTest L
      (ne_of_gt hL) f v z
  rw [torusPeriodizationCoeff_eq_fourier L (R + 1) hL hRbox
    (unitBoxDirectionalDerivativeTest L f v) hdf' k]
  rw [hfun]
  rw [fourier_complexDirectionalDerivative
    (gffUnitBoxComplexFunction_contDiff L f)
    (gffUnitBoxComplexFunction_hasCompactSupport L (ne_of_gt hL) f)
    v (unitTorusFourierFrequency k)]
  rw [← torusPeriodizationCoeff_eq_fourier L (R + 1) hL hRbox f hf' k]

/-- Two unit-box derivatives multiply the torus coefficient by the squared frequency. -/
theorem torusPeriodizationCoeff_unitBoxDirectionalDerivative_twice
    (L R : ℝ) (hL : 0 < L) (hRbox : R + 2 < L / 2) (f : TestFn)
    (hf : Function.support f ⊆ ball (0 : ℂ) R) (v : ℂ) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (torusPeriodizationLp L
          (unitBoxDirectionalDerivativeTest L
            (unitBoxDirectionalDerivativeTest L f v) v)) k =
      (2 * Real.pi * Complex.I *
        ((innerSL ℝ) (unitTorusFourierFrequency k) v : ℂ)) ^ 2 *
        UnitAddTorus.mFourierCoeff (torusPeriodizationLp L f) k := by
  have hf1 := support_unitBoxDirectionalDerivativeTest_subset L R f v hf
  have hone := torusPeriodizationCoeff_unitBoxDirectionalDerivative
    L (R + 1) hL (by linarith) (unitBoxDirectionalDerivativeTest L f v)
    hf1 v k
  have hzero := torusPeriodizationCoeff_unitBoxDirectionalDerivative
    L R hL (by linarith) f hf v k
  rw [hone, hzero]
  ring

end DOZZ

end
