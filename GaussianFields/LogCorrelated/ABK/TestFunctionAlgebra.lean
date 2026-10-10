/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Covariance

/-!
# GaussianFields.LogCorrelated/ABK/TestFunctionAlgebra

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields


/-! ## Pointwise algebraic structure on mean-zero test functions -/

namespace MeanZeroTestFunction

instance {d : Nat} : Zero (MeanZeroTestFunction d) where
  zero :=
    { toFun := 0
      continuous := continuous_zero
      hasCompactSupport := HasCompactSupport.zero
      integrable := integrable_zero (α := Vec d) (ε' := ℝ)
        (μ := (volume : Measure (Vec d)))
      memLp_two := MemLp.zero
      integral_eq_zero := integral_zero (Vec d) ℝ }

instance {d : Nat} : Add (MeanZeroTestFunction d) where
  add ψ φ :=
    { toFun := fun x => ψ x + φ x
      continuous := ψ.continuous.add φ.continuous
      hasCompactSupport := ψ.hasCompactSupport.add φ.hasCompactSupport
      integrable := ψ.integrable.add φ.integrable
      memLp_two := ψ.memLp_two.add φ.memLp_two
      integral_eq_zero := by
        rw [integral_add ψ.integrable φ.integrable, ψ.integral_eq_zero,
          φ.integral_eq_zero, add_zero] }

instance {d : Nat} : Neg (MeanZeroTestFunction d) where
  neg ψ :=
    { toFun := fun x => -ψ x
      continuous := ψ.continuous.neg
      hasCompactSupport := ψ.hasCompactSupport.neg
      integrable := ψ.integrable.neg
      memLp_two := ψ.memLp_two.neg
      integral_eq_zero := by
        rw [integral_neg, ψ.integral_eq_zero, neg_zero] }

instance {d : Nat} : SMul ℝ (MeanZeroTestFunction d) where
  smul c ψ :=
    { toFun := fun x => c • ψ.toFun x
      continuous := ψ.continuous.const_smul c
      hasCompactSupport := by
        have hfun : (fun x : Vec d => c • ψ.toFun x) =
            (fun _ : Vec d => c) • ψ.toFun := by
          funext x
          exact (Pi.smul_apply' x (fun _ : Vec d => c) ψ.toFun).symm
        rw [hfun]
        exact ψ.hasCompactSupport.smul_left (f := fun _ : Vec d => c)
      integrable := by
        simpa only [smul_eq_mul] using ψ.integrable.const_mul c
      memLp_two := ψ.memLp_two.const_smul c
      integral_eq_zero := by
        rw [integral_smul, ψ.integral_eq_zero, smul_zero] }

@[simp]
theorem zero_apply {d : Nat} (x : Vec d) :
    (0 : MeanZeroTestFunction d) x = 0 := rfl

@[simp]
theorem add_apply {d : Nat} (ψ φ : MeanZeroTestFunction d) (x : Vec d) :
    (ψ + φ) x = ψ x + φ x := rfl

@[simp]
theorem neg_apply {d : Nat} (ψ : MeanZeroTestFunction d) (x : Vec d) :
    (-ψ) x = -ψ x := rfl

@[simp]
theorem smul_apply {d : Nat} (c : ℝ) (ψ : MeanZeroTestFunction d) (x : Vec d) :
    (c • ψ) x = c • ψ x := rfl

instance {d : Nat} : AddCommGroup (MeanZeroTestFunction d) where
  add_assoc ψ φ χ := by
    ext x
    simp [add_assoc]
  zero_add ψ := by
    ext x
    simp
  add_zero ψ := by
    ext x
    simp
  add_comm ψ φ := by
    ext x
    simp [add_comm]
  neg_add_cancel ψ := by
    ext x
    simp
  nsmul := nsmulRec
  zsmul := zsmulRec

instance {d : Nat} : Module ℝ (MeanZeroTestFunction d) where
  one_smul ψ := by
    ext x
    simp
  mul_smul a b ψ := by
    ext x
    simp [mul_assoc]
  smul_zero a := by
    ext x
    simp
  smul_add a ψ φ := by
    ext x
    simp [mul_add]
  add_smul a b ψ := by
    ext x
    simp [add_mul]
  zero_smul ψ := by
    ext x
    simp

end MeanZeroTestFunction

/-! ## Linearity of the ABK spatial convolution -/

theorem abkSpatialConvolution_add {d : Nat} (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    abkSpatialConvolution ζ (ψ + φ) r y =
      abkSpatialConvolution ζ ψ r y + abkSpatialConvolution ζ φ r y := by
  unfold abkSpatialConvolution
  rw [← integral_add (integrable_abkSpatialConvolution_integrand ζ ψ r y)
    (integrable_abkSpatialConvolution_integrand ζ φ r y)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [mul_add]

theorem abkSpatialConvolution_smul {d : Nat} (ζ : ABKCutoff d) (c : ℝ)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    abkSpatialConvolution ζ (c • ψ) r y = c * abkSpatialConvolution ζ ψ r y := by
  unfold abkSpatialConvolution
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp only [MeanZeroTestFunction.smul_apply, smul_eq_mul]
  ring

theorem abkSpatialConvolution_neg {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    abkSpatialConvolution ζ (-ψ) r y = -abkSpatialConvolution ζ ψ r y := by
  unfold abkSpatialConvolution
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp

theorem abkSpatialConvolution_zero {d : Nat} (ζ : ABKCutoff d) (r : ℝ)
    (y : Vec d) :
    abkSpatialConvolution ζ (0 : MeanZeroTestFunction d) r y = 0 := by
  unfold abkSpatialConvolution
  simp

/-! ## Linearity of the deterministic ABK kernels -/

theorem abkLogKernelProd_add {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d) :
    abkLogKernelProd normalization ζ (ψ + φ) =
      abkLogKernelProd normalization ζ ψ + abkLogKernelProd normalization ζ φ := by
  funext p
  by_cases hp : 0 < p.1
  · simp [abkLogKernelProd, hp, abkSpatialConvolution_add, mul_add]
  · simp [abkLogKernelProd, hp]

theorem abkLogKernelProd_smul {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (c : ℝ) (ψ : MeanZeroTestFunction d) :
    abkLogKernelProd normalization ζ (c • ψ) =
      c • abkLogKernelProd normalization ζ ψ := by
  funext p
  by_cases hp : 0 < p.1
  · simp only [abkLogKernelProd, ite_eq_left hp, abkSpatialConvolution_smul,
      Pi.smul_apply, smul_eq_mul]
    ring
  · simp [abkLogKernelProd, hp]

theorem abkLogKernelProd_neg {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) :
    abkLogKernelProd normalization ζ (-ψ) =
      -abkLogKernelProd normalization ζ ψ := by
  funext p
  by_cases hp : 0 < p.1
  · simp [abkLogKernelProd, hp, abkSpatialConvolution_neg]
  · simp [abkLogKernelProd, hp]

theorem abkLogKernelProd_zero {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d) :
    abkLogKernelProd normalization ζ (0 : MeanZeroTestFunction d) =
      (0 : ℝ × Vec d → ℝ) := by
  funext p
  by_cases hp : 0 < p.1
  · simp [abkLogKernelProd, hp, abkSpatialConvolution_zero]
  · simp [abkLogKernelProd, hp]

theorem abkLogKernel_add {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d) :
    abkLogKernel normalization ζ (ψ + φ) =
      abkLogKernel normalization ζ ψ + abkLogKernel normalization ζ φ := by
  funext z
  simp [abkLogKernel, abkLogKernelProd_add]

theorem abkLogKernel_smul {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (c : ℝ) (ψ : MeanZeroTestFunction d) :
    abkLogKernel normalization ζ (c • ψ) =
      c • abkLogKernel normalization ζ ψ := by
  funext z
  simp [abkLogKernel, abkLogKernelProd_smul]

theorem abkLogKernel_neg {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) :
    abkLogKernel normalization ζ (-ψ) = -abkLogKernel normalization ζ ψ := by
  funext z
  simp [abkLogKernel, abkLogKernelProd_neg]

theorem abkLogKernel_zero {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d) :
    abkLogKernel normalization ζ (0 : MeanZeroTestFunction d) =
      (0 : ScaleSpace d → ℝ) := by
  funext z
  simp [abkLogKernel, abkLogKernelProd_zero]

/-! ## Linearity of the `L²` kernel vectors -/

theorem abkLogKernelLp_add {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d)))
    (hsum :
      MemLp (abkLogKernelProd normalization ζ (ψ + φ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogKernelLp normalization ζ (ψ + φ) hsum =
      abkLogKernelLp normalization ζ ψ hψ +
        abkLogKernelLp normalization ζ φ hφ := by
  unfold abkLogKernelLp
  rw [← MemLp.toLp_add]
  exact MemLp.toLp_congr _ _
    (Filter.EventuallyEq.of_eq (abkLogKernel_add normalization ζ ψ φ))

theorem abkLogKernelLp_smul {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (c : ℝ) (ψ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hsmul :
      MemLp (abkLogKernelProd normalization ζ (c • ψ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogKernelLp normalization ζ (c • ψ) hsmul =
      c • abkLogKernelLp normalization ζ ψ hψ := by
  unfold abkLogKernelLp
  rw [← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr _ _
    (Filter.EventuallyEq.of_eq (abkLogKernel_smul normalization ζ c ψ))

theorem abkLogKernelLp_neg {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hneg :
      MemLp (abkLogKernelProd normalization ζ (-ψ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogKernelLp normalization ζ (-ψ) hneg =
      -abkLogKernelLp normalization ζ ψ hψ := by
  unfold abkLogKernelLp
  rw [← MemLp.toLp_neg]
  exact MemLp.toLp_congr _ _
    (Filter.EventuallyEq.of_eq (abkLogKernel_neg normalization ζ ψ))

theorem abkLogKernelLp_zero {d : Nat} (normalization : ℝ) (ζ : ABKCutoff d)
    (hzero :
      MemLp (abkLogKernelProd normalization ζ (0 : MeanZeroTestFunction d)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogKernelLp normalization ζ (0 : MeanZeroTestFunction d) hzero = 0 := by
  unfold abkLogKernelLp
  calc
    (memLp_abkLogKernel_of_prod hzero).toLp
        (abkLogKernel normalization ζ (0 : MeanZeroTestFunction d)) =
        (MemLp.zero :
            MemLp (0 : ScaleSpace d → ℝ) 2
              (volume : Measure (ScaleSpace d))).toLp
          (0 : ScaleSpace d → ℝ) :=
      MemLp.toLp_congr _ _
        (Filter.EventuallyEq.of_eq (abkLogKernel_zero normalization ζ))
    _ = 0 := MemLp.toLp_zero _

/-! ## Linearity of the ABK field, general normalization -/

theorem abkLogCorrelatedFieldL2_add {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hφ :
      MemLp (abkLogKernelProd normalization ζ φ) 2
        (volume : Measure (ℝ × Vec d)))
    (hsum :
      MemLp (abkLogKernelProd normalization ζ (ψ + φ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogCorrelatedFieldL2 normalization ζ (ψ + φ) hsum =
      abkLogCorrelatedFieldL2 normalization ζ ψ hψ +
        abkLogCorrelatedFieldL2 normalization ζ φ hφ := by
  unfold abkLogCorrelatedFieldL2
  rw [abkLogKernelLp_add normalization ζ ψ φ hψ hφ hsum,
    (scaleSpaceWhiteNoiseL2 d).map_add]

theorem abkLogCorrelatedFieldL2_smul {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (c : ℝ) (ψ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hsmul :
      MemLp (abkLogKernelProd normalization ζ (c • ψ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogCorrelatedFieldL2 normalization ζ (c • ψ) hsmul =
      c • abkLogCorrelatedFieldL2 normalization ζ ψ hψ := by
  unfold abkLogCorrelatedFieldL2
  rw [abkLogKernelLp_smul normalization ζ c ψ hψ hsmul,
    (scaleSpaceWhiteNoiseL2 d).map_smul]

theorem abkLogCorrelatedFieldL2_neg {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d)
    (hψ :
      MemLp (abkLogKernelProd normalization ζ ψ) 2
        (volume : Measure (ℝ × Vec d)))
    (hneg :
      MemLp (abkLogKernelProd normalization ζ (-ψ)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogCorrelatedFieldL2 normalization ζ (-ψ) hneg =
      -abkLogCorrelatedFieldL2 normalization ζ ψ hψ := by
  unfold abkLogCorrelatedFieldL2
  rw [abkLogKernelLp_neg normalization ζ ψ hψ hneg,
    (scaleSpaceWhiteNoiseL2 d).map_neg]

theorem abkLogCorrelatedFieldL2_zero {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d)
    (hzero :
      MemLp (abkLogKernelProd normalization ζ (0 : MeanZeroTestFunction d)) 2
        (volume : Measure (ℝ × Vec d))) :
    abkLogCorrelatedFieldL2 normalization ζ (0 : MeanZeroTestFunction d)
        hzero = 0 := by
  unfold abkLogCorrelatedFieldL2
  rw [abkLogKernelLp_zero normalization ζ hzero,
    (scaleSpaceWhiteNoiseL2 d).map_zero]

/-! ## Linearity of the canonically normalized ABK field -/

theorem abkLogCorrelatedFieldL2Canonical_add {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    abkLogCorrelatedFieldL2Canonical hd ζ (ψ + φ) =
      abkLogCorrelatedFieldL2Canonical hd ζ ψ +
        abkLogCorrelatedFieldL2Canonical hd ζ φ := by
  unfold abkLogCorrelatedFieldL2Canonical
  exact abkLogCorrelatedFieldL2_add (abkNormalization ζ) ζ ψ φ
    (memLp_abkLogKernelProd_canonical hd ζ ψ)
    (memLp_abkLogKernelProd_canonical hd ζ φ)
    (memLp_abkLogKernelProd_canonical hd ζ (ψ + φ))

theorem abkLogCorrelatedFieldL2Canonical_smul {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (c : ℝ) (ψ : MeanZeroTestFunction d) :
    abkLogCorrelatedFieldL2Canonical hd ζ (c • ψ) =
      c • abkLogCorrelatedFieldL2Canonical hd ζ ψ := by
  unfold abkLogCorrelatedFieldL2Canonical
  exact abkLogCorrelatedFieldL2_smul (abkNormalization ζ) ζ c ψ
    (memLp_abkLogKernelProd_canonical hd ζ ψ)
    (memLp_abkLogKernelProd_canonical hd ζ (c • ψ))

theorem abkLogCorrelatedFieldL2Canonical_neg {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    abkLogCorrelatedFieldL2Canonical hd ζ (-ψ) =
      -abkLogCorrelatedFieldL2Canonical hd ζ ψ := by
  unfold abkLogCorrelatedFieldL2Canonical
  exact abkLogCorrelatedFieldL2_neg (abkNormalization ζ) ζ ψ
    (memLp_abkLogKernelProd_canonical hd ζ ψ)
    (memLp_abkLogKernelProd_canonical hd ζ (-ψ))

theorem abkLogCorrelatedFieldL2Canonical_zero {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) :
    abkLogCorrelatedFieldL2Canonical hd ζ (0 : MeanZeroTestFunction d) = 0 := by
  unfold abkLogCorrelatedFieldL2Canonical
  exact abkLogCorrelatedFieldL2_zero (abkNormalization ζ) ζ
    (memLp_abkLogKernelProd_canonical hd ζ (0 : MeanZeroTestFunction d))

/-- The canonical ABK field evaluation, packaged as a genuine `ℝ`-linear map on the
test-function vector space. -/
@[expose]
noncomputable def abkLogCorrelatedFieldL2CanonicalLinearMap {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) :
    MeanZeroTestFunction d →ₗ[ℝ] Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d) where
  toFun ψ := abkLogCorrelatedFieldL2Canonical hd ζ ψ
  map_add' ψ φ := abkLogCorrelatedFieldL2Canonical_add hd ζ ψ φ
  map_smul' c ψ := abkLogCorrelatedFieldL2Canonical_smul hd ζ c ψ

@[simp]
theorem abkLogCorrelatedFieldL2CanonicalLinearMap_apply {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    abkLogCorrelatedFieldL2CanonicalLinearMap hd ζ ψ =
      abkLogCorrelatedFieldL2Canonical hd ζ ψ :=
  rfl

/-! ## Finite linear combinations are single white-noise evaluations -/

/-- A finite linear combination of canonical ABK field evaluations is itself the white-noise
evaluation of the corresponding linear combination of deterministic kernels. -/
theorem sum_smul_abkLogCorrelatedFieldL2Canonical_eq_whiteNoise {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (ψ : ι → MeanZeroTestFunction d) :
    ∑ i ∈ s, c i • abkLogCorrelatedFieldL2Canonical hd ζ (ψ i) =
      scaleSpaceWhiteNoiseL2 d
        (∑ i ∈ s,
          c i • abkLogKernelLp (abkNormalization ζ) ζ (ψ i)
            (memLp_abkLogKernelProd_canonical hd ζ (ψ i))) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(scaleSpaceWhiteNoiseL2 d).map_smul]
  rfl

/-- Exact Gaussianity of finite linear combinations of canonical ABK field evaluations: the law
is centered Gaussian with variance the squared `L²(Ω)` norm of the combination. -/
theorem map_sum_smul_abkLogCorrelatedFieldL2Canonical_eq_gaussianReal {d : Nat}
    (hd : 0 < d) (ζ : ABKCutoff d) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (ψ : ι → MeanZeroTestFunction d) :
    Measure.map
        (∑ i ∈ s, c i • abkLogCorrelatedFieldL2Canonical hd ζ (ψ i) :
          Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d))
        (scaleSpaceWhiteNoiseMeasure d) =
      ProbabilityTheory.gaussianReal 0
        (Real.toNNReal
          (‖(∑ i ∈ s, c i • abkLogCorrelatedFieldL2Canonical hd ζ (ψ i) :
              Lp ℝ 2 (scaleSpaceWhiteNoiseMeasure d))‖ ^ (2 : Nat))) := by
  rw [sum_smul_abkLogCorrelatedFieldL2Canonical_eq_whiteNoise hd ζ s c ψ,
    (scaleSpaceWhiteNoiseL2 d).norm_map]
  exact map_scalarWhiteNoiseL2_eq_gaussianReal _

end GaussianFields

end
