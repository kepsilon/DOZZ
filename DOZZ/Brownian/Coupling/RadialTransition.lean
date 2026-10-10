/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.GaussianRadius
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Rotation and the radial Gaussian transition

The Cartesian Gaussian heat law is invariant under every real linear isometry. Reflecting a
positive starting vector onto the first axis reduces its norm transition to cylindrical integration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical RealInnerProductSpace

namespace DOZZ.Proofs

/-- The actual centered three-dimensional Gaussian increment law on Euclidean space. -/
noncomputable def radialGaussianVectorMeasure (t : ℝ≥0) : Measure (EuclideanSpace ℝ (Fin 3)) :=
  (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)).map (WithLp.toLp 2)

instance isProbabilityMeasure_radialGaussianVectorMeasure (t : ℝ≥0) :
    IsProbabilityMeasure (radialGaussianVectorMeasure t) :=
by
  unfold radialGaussianVectorMeasure
  exact (Measure.isProbabilityMeasure_map_iff (PiLp.continuous_toLp 2 _).measurable.aemeasurable).mpr inferInstance

/-- Cartesian density of the centered vector law in its Euclidean carrier. -/
theorem lintegral_radialGaussianVectorMeasure (t : ℝ≥0) (ht : 0 < t)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ w, f w ∂radialGaussianVectorMeasure t) =
      ∫⁻ w, (ENNReal.ofReal (radialGaussianConstant t) *
        ENNReal.ofReal (Real.exp (-‖w‖ ^ 2 / (2 * (t : ℝ))))) * f w := by
  have hpdf : Measurable (fun z : Fin 3 → ℝ => ∏ i, gaussianPDF 0 t (z i)) := by
    exact Finset.measurable_prod Finset.univ (fun i _ =>
      (measurable_gaussianPDF _ _).comp (measurable_pi_apply i))
  rw [radialGaussianVectorMeasure, lintegral_map hf (PiLp.continuous_toLp 2 _).measurable,
    pi_gaussianReal_withDensity _ t ht.ne',
    lintegral_withDensity_eq_lintegral_mul volume hpdf (show Measurable (fun z : Fin 3 → ℝ => f (WithLp.toLp 2 z)) from hf.comp (PiLp.continuous_toLp 2 _).measurable)]
  have hproduct (z : Fin 3 → ℝ) : (∏ i, gaussianPDF 0 t (z i)) =
      ENNReal.ofReal (radialGaussianConstant t) * ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 z‖ ^ 2 / (2 * (t : ℝ)))) := by
    simpa using three_gaussianPDF_product 0 t ht.ne' z
  simp_rw [Pi.mul_apply, hproduct]
  exact (PiLp.volume_preserving_toLp (Fin 3)).lintegral_comp
    (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) =>
      (ENNReal.ofReal (radialGaussianConstant t) *
        ENNReal.ofReal (Real.exp (-‖w‖ ^ 2 / (2 * (t : ℝ))))) * f w) from
      (measurable_const.mul (by fun_prop)).mul hf)

/-- Rotations and reflections preserve the actual centered Gaussian law. -/
theorem radialGaussianVectorMeasure_map_isometry (t : ℝ≥0) (ht : 0 < t)
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)) :
    (radialGaussianVectorMeasure t).map L = radialGaussianVectorMeasure t := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf L.continuous.measurable,
    lintegral_radialGaussianVectorMeasure t ht _ (show Measurable (fun w => f (L w)) from hf.comp L.continuous.measurable),
    lintegral_radialGaussianVectorMeasure t ht f hf]
  have hm : Measurable (fun w : EuclideanSpace ℝ (Fin 3) =>
      (ENNReal.ofReal (radialGaussianConstant t) *
        ENNReal.ofReal (Real.exp (-‖w‖ ^ 2 / (2 * (t : ℝ))))) * f w) :=
    (measurable_const.mul (by fun_prop)).mul hf
  have h := L.measurePreserving.lintegral_comp hm
  simpa only [L.norm_map] using h

/-- The nonnegative first-axis vector of a given radius. -/
noncomputable def radialAxisVector (x : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => if i = 0 then x else 0)

/-- Its Euclidean norm is exactly the absolute radius. -/
theorem norm_radialAxisVector (x : ℝ) : ‖radialAxisVector x‖ = |x| := by
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, sq_abs]
  simp [radialAxisVector]

/-- A Householder reflection sends every vector to the positive longitudinal axis. -/
theorem exists_radialAxisIsometry (z : EuclideanSpace ℝ (Fin 3)) :
    ∃ L : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3),
      L z = radialAxisVector ‖z‖ := by
  refine ⟨Submodule.reflection (ℝ ∙ (z - radialAxisVector ‖z‖))ᗮ, ?_⟩
  apply Submodule.reflection_sub
  rw [norm_radialAxisVector, abs_of_nonneg (norm_nonneg _)]

/-- Rotating the mean preserves every norm test, as an identity of actual Gaussian integrals. -/
theorem lintegral_radialGaussian_rotate_mean (z : EuclideanSpace ℝ (Fin 3))
    (t : ℝ≥0) (ht : 0 < t) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ‖z + w‖ ∂radialGaussianVectorMeasure t) =
      ∫⁻ w, F ‖radialAxisVector ‖z‖ + w‖ ∂radialGaussianVectorMeasure t := by
  obtain ⟨L, hL⟩ := exists_radialAxisIsometry z
  calc
    _ = ∫⁻ w, F ‖radialAxisVector ‖z‖ + L w‖ ∂radialGaussianVectorMeasure t := by
      apply lintegral_congr
      intro w
      rw [← hL, ← map_add, L.norm_map]
    _ = _ := by
      rw [← lintegral_map (show Measurable (fun w => F ‖radialAxisVector ‖z‖ + w‖) from
        hF.comp (continuous_const.add continuous_id).norm.measurable) L.continuous.measurable,
        radialGaussianVectorMeasure_map_isometry t ht L]

/-- Axis translation of the centered Cartesian Gaussian gives the actual independent shifted law. -/
theorem radialGaussianVectorMeasure_axis_add_map (x : ℝ) (t : ℝ≥0) :
    (radialGaussianVectorMeasure t).map (fun w => radialAxisVector x + w) =
      (Measure.pi (fun i : Fin 3 => gaussianReal (if i = 0 then x else 0) t)).map (WithLp.toLp 2) := by
  let shift := fun z : Fin 3 → ℝ => fun i => z i + (if i = 0 then x else 0)
  have hshift : Measurable shift := measurable_pi_iff.mpr fun i => (measurable_pi_apply i).add_const _
  have hpi : (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)).map shift =
      Measure.pi (fun i : Fin 3 => gaussianReal (if i = 0 then x else 0) t) := by
    change (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)).map
      (fun z i => z i + (if i = 0 then x else 0)) = _
    rw [Measure.pi_map_pi (f := fun i u => u + (if i = 0 then x else 0))
      (fun _ => (measurable_id.add_const _).aemeasurable)]
    congr 1
    funext i
    simpa using gaussianReal_map_add_const (μ := 0) (v := t) (if i = 0 then x else 0)
  rw [← hpi, radialGaussianVectorMeasure,
    Measure.map_map (PiLp.continuous_toLp 2 _).measurable hshift,
    Measure.map_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => radialAxisVector x + w) from
      (continuous_const.add continuous_id).measurable) (PiLp.continuous_toLp 2 _).measurable]
  congr 1
  funext z
  apply WithLp.ofLp_injective
  funext i
  exact add_comm _ _

/-- The ordinary Brownian Gaussian increment has the exact BES(3) norm kernel from every nonzero vector. -/
theorem lintegral_radialGaussian_transition (z : EuclideanSpace ℝ (Fin 3)) (hz : z ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ‖z + w‖ ∂radialGaussianVectorMeasure t) =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveTransitionDensity 0 t ‖z‖ y) := by
  rw [lintegral_radialGaussian_rotate_mean z t ht F hF]
  rw [← lintegral_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖) from hF.comp continuous_norm.measurable) (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => radialAxisVector ‖z‖ + w) from
      (continuous_const.add continuous_id).measurable),
    radialGaussianVectorMeasure_axis_add_map, lintegral_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖) from hF.comp continuous_norm.measurable)
      (PiLp.continuous_toLp 2 _).measurable]
  exact lintegral_three_gaussian_axis_transition ‖z‖ (norm_pos_iff.mpr hz) t ht F hF

/-- Isotropic Gaussian heat density on the actual Euclidean carrier. -/
noncomputable def radialGaussianVectorDensity (t : ℝ≥0) (w : EuclideanSpace ℝ (Fin 3)) : ℝ≥0∞ :=
  ENNReal.ofReal (radialGaussianConstant t) *
    ENNReal.ofReal (Real.exp (-‖w‖ ^ 2 / (2 * (t : ℝ))))

/-- The heat density is measurable, including external spatial parameters. -/
theorem measurable_radialGaussianVectorDensity (t : ℝ≥0) :
    Measurable (radialGaussianVectorDensity t) := by
  unfold radialGaussianVectorDensity
  fun_prop

/-- The centered vector law is exactly the Euclidean heat-density measure. -/
theorem radialGaussianVectorMeasure_eq_withDensity (t : ℝ≥0) (ht : 0 < t) :
    radialGaussianVectorMeasure t = (volume : Measure (EuclideanSpace ℝ (Fin 3))).withDensity
      (radialGaussianVectorDensity t) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_radialGaussianVectorMeasure t ht f hf,
    lintegral_withDensity_eq_lintegral_mul volume (measurable_radialGaussianVectorDensity t) hf]
  rfl

/-- The isotropic heat density is even. -/
theorem radialGaussianVectorDensity_neg (t : ℝ≥0) (w : EuclideanSpace ℝ (Fin 3)) :
    radialGaussianVectorDensity t (-w) = radialGaussianVectorDensity t w := by
  simp only [radialGaussianVectorDensity, norm_neg]

/-- Heat-density symmetry keeps the two actual vector operands. -/
theorem radialGaussianVectorDensity_sub_comm (t : ℝ≥0) (z w : EuclideanSpace ℝ (Fin 3)) :
    radialGaussianVectorDensity t (z - w) = radialGaussianVectorDensity t (w - z) := by
  rw [← neg_sub w z, radialGaussianVectorDensity_neg]

/-- Joint spatial measurability of the translated heat density. -/
theorem measurable_radialGaussianVectorDensity_sub (t : ℝ≥0) :
    Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      radialGaussianVectorDensity t (p.2 - p.1)) :=
  (measurable_radialGaussianVectorDensity t).comp (measurable_snd.sub measurable_fst)

/-- Translating the actual Gaussian increment gives the literal heat kernel from the chosen start. -/
theorem radialGaussianVectorMeasure_add_map_eq_density (z : EuclideanSpace ℝ (Fin 3))
    (t : ℝ≥0) (ht : 0 < t) :
    (radialGaussianVectorMeasure t).map (fun w => z + w) =
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).withDensity
        (fun w => radialGaussianVectorDensity t (w - z)) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (show Measurable (fun w => z + w) from (continuous_const.add continuous_id).measurable),
    lintegral_radialGaussianVectorMeasure t ht _ (show Measurable (fun w => f (z + w)) from
      hf.comp (continuous_const.add continuous_id).measurable),
    lintegral_withDensity_eq_lintegral_mul volume
      (show Measurable (fun w => radialGaussianVectorDensity t (w - z)) from
        (measurable_radialGaussianVectorDensity t).comp (measurable_id.sub_const z)) hf]
  have hm : Measurable (fun w => radialGaussianVectorDensity t (w - z) * f w) :=
    ((measurable_radialGaussianVectorDensity t).comp (measurable_id.sub_const z)).mul hf
  have h := (measurePreserving_add_left (volume : Measure (EuclideanSpace ℝ (Fin 3))) z).lintegral_comp hm
  simpa only [add_sub_cancel_left, radialGaussianVectorDensity, Pi.mul_apply] using h

/-- Radial heat convolution depends only on the radius of the starting vector. -/
noncomputable def radialHeatConvolution (t : ℝ≥0) (F : ℝ → ℝ≥0∞)
    (z : EuclideanSpace ℝ (Fin 3)) : ℝ≥0∞ :=
  ∫⁻ w, F ‖z + w‖ ∂radialGaussianVectorMeasure t

/-- The actual convolution is measurable in the starting vector. -/
theorem measurable_radialHeatConvolution (t : ℝ≥0) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (radialHeatConvolution t F) := by
  exact Measurable.lintegral_prod_right (hF.comp (continuous_fst.add continuous_snd).norm.measurable)


/-- Starting at zero gives the exact Maxwell entrance instead of the singular positive-start formula. -/
theorem radialHeatConvolution_zero (t : ℝ≥0) (ht : 0 < t)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    radialHeatConvolution t F 0 =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveEntranceDensity 0 t y) := by
  rw [radialHeatConvolution, radialGaussianVectorMeasure,
    lintegral_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖0 + w‖) from
      hF.comp (continuous_const.add continuous_id).norm.measurable)]
  · simp only [zero_add]
    rw [lintegral_three_gaussian_radial_zero F hF t ht, lintegral_entranceDensity_Ioi]
  · exact (PiLp.continuous_toLp 2 _).measurable

/-- Equal starting radii give exactly the same radial heat convolution. -/
theorem radialHeatConvolution_eq_of_norm_eq (t : ℝ≥0) (ht : 0 < t)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (z w : EuclideanSpace ℝ (Fin 3)) (hzw : ‖z‖ = ‖w‖) :
    radialHeatConvolution t F z = radialHeatConvolution t F w := by
  unfold radialHeatConvolution
  rw [lintegral_radialGaussian_rotate_mean z t ht F hF,
    lintegral_radialGaussian_rotate_mean w t ht F hF, hzw]

/-- Cartesian heat convolution of a radial profile is its actual Gaussian radial convolution. -/
theorem lintegral_radial_heat_density (t : ℝ≥0) (ht : 0 < t)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (z : EuclideanSpace ℝ (Fin 3)) :
    (∫⁻ w, radialGaussianVectorDensity t (w - z) * F ‖w‖) = radialHeatConvolution t F z := by
  change (∫⁻ w, ((fun w => radialGaussianVectorDensity t (w - z)) *
    (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖)) w) = _
  rw [← lintegral_withDensity_eq_lintegral_mul volume
    (show Measurable (fun w => radialGaussianVectorDensity t (w - z)) from
      (measurable_radialGaussianVectorDensity t).comp (measurable_id.sub_const z))
    (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖) from hF.comp continuous_norm.measurable),
    ← radialGaussianVectorMeasure_add_map_eq_density z t ht,
    lintegral_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖) from hF.comp continuous_norm.measurable)
      (show Measurable (fun w => z + w) from (continuous_const.add continuous_id).measurable)]
  rfl

/-- The same convolution uses the reversed heat density pointwise. -/
theorem lintegral_radial_heat_density_reverse (t : ℝ≥0) (ht : 0 < t)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) (z : EuclideanSpace ℝ (Fin 3)) :
    (∫⁻ w, radialGaussianVectorDensity t (z - w) * F ‖w‖) = radialHeatConvolution t F z := by
  calc
    _ = ∫⁻ w, radialGaussianVectorDensity t (w - z) * F ‖w‖ := by
      apply lintegral_congr
      intro w
      rw [radialGaussianVectorDensity_sub_comm t z w]
    _ = _ := lintegral_radial_heat_density t ht F hF z

/-- Cartesian Brownian increment kernel, written with the explicit translated Gaussian density. -/
noncomputable def radialGaussianIncrementKernel (t : ℝ≥0) :
    Kernel (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  (Kernel.const _ (volume : Measure (EuclideanSpace ℝ (Fin 3)))).withDensity
    (fun z w => radialGaussianVectorDensity t (w - z))

/-- Every positive-time kernel fiber is the actual translated independent Gaussian increment law. -/
theorem radialGaussianIncrementKernel_apply (t : ℝ≥0) (ht : 0 < t) (z : EuclideanSpace ℝ (Fin 3)) :
    radialGaussianIncrementKernel t z =
      (radialGaussianVectorMeasure t).map (fun w => z + w) := by
  rw [radialGaussianIncrementKernel, Kernel.withDensity_apply _
    (measurable_radialGaussianVectorDensity_sub t), Kernel.const_apply,
    radialGaussianVectorMeasure_add_map_eq_density z t ht]

/-- The explicit Cartesian increment kernel is Markov at each positive elapsed time. -/
theorem isMarkovKernel_radialGaussianIncrementKernel (t : ℝ≥0) (ht : 0 < t) :
    IsMarkovKernel (radialGaussianIncrementKernel t) := by
  constructor
  intro z
  rw [radialGaussianIncrementKernel_apply t ht z]
  exact (Measure.isProbabilityMeasure_map_iff
    (show AEMeasurable (fun w : EuclideanSpace ℝ (Fin 3) => z + w) (radialGaussianVectorMeasure t) from
      (continuous_const.add continuous_id).measurable.aemeasurable)).mpr inferInstance

/-- Norm tests of a Cartesian increment fiber give the exact zero-drift radial transition. -/
theorem radialGaussianIncrementKernel_lintegral_norm (t : ℝ≥0) (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin 3)) (hz : z ≠ 0) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ‖w‖ ∂radialGaussianIncrementKernel t z) =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveTransitionDensity 0 t ‖z‖ y) := by
  rw [radialGaussianIncrementKernel_apply t ht z,
    lintegral_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖) from hF.comp continuous_norm.measurable)
      (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => z + w) from
        (continuous_const.add continuous_id).measurable)]
  exact lintegral_radialGaussian_transition z hz t ht F hF

/-- At the origin the Cartesian increment fiber gives the exact Maxwell entrance kernel. -/
theorem radialGaussianIncrementKernel_lintegral_norm_zero (t : ℝ≥0) (ht : 0 < t)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, F ‖w‖ ∂radialGaussianIncrementKernel t 0) =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveEntranceDensity 0 t y) := by
  rw [radialGaussianIncrementKernel_apply t ht 0,
    lintegral_map (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => F ‖w‖) from hF.comp continuous_norm.measurable)
      (show Measurable (fun w : EuclideanSpace ℝ (Fin 3) => (0 : EuclideanSpace ℝ (Fin 3)) + w) from
        (continuous_const.add continuous_id).measurable)]
  exact radialHeatConvolution_zero t ht F hF

/-- The Cartesian-to-radial kernel equality is an actual pushforward equality for every nonzero start. -/
theorem radialGaussianIncrementKernel_map_norm (t : ℝ≥0) (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin 3)) (hz : z ≠ 0) :
    (radialGaussianIncrementKernel t z).map (fun w => ‖w‖) =
      conditionedPositiveTransitionMeasure 0 t ‖z‖ := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF continuous_norm.measurable,
    radialGaussianIncrementKernel_lintegral_norm t ht z hz F hF,
    conditionedPositiveTransitionMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (show Measurable (fun y : ℝ => ENNReal.ofReal (conditionedPositiveTransitionDensity 0 t ‖z‖ y)) from
        ((measurable_conditionedPositiveTransitionDensity_pair 0 t).comp
          (measurable_const.prodMk measurable_id)).ennreal_ofReal) hF]
  apply lintegral_congr
  intro y
  exact mul_comm _ _


/-- The elapsed-time variance of an actual Brownian increment. -/
theorem brownianIncrement_nndist (s dt : ℝ≥0) : nndist ((s + dt : ℝ≥0) : ℝ) (s : ℝ) = dt := by
  apply NNReal.eq
  rw [coe_nndist, Real.dist_eq, NNReal.coe_add, add_sub_cancel_left]
  exact abs_of_nonneg dt.property

/-- The shared three-dimensional Wiener source has the independent product Gaussian increment law. -/
theorem wienerTriple_increment_hasLaw (s dt : ℝ≥0) :
    HasLaw (fun V : BrownianTriple => fun i : Fin 3 => V i (s + dt) - V i s)
      (Measure.pi (fun _ : Fin 3 => gaussianReal 0 dt)) wienerTripleMeasure := by
  have hindep := wienerTriple_coordinatePaths_independent.comp
    (fun _ p => p (s + dt) - p s)
    (fun _ => (ContinuousMap.measurable_eval _).sub (ContinuousMap.measurable_eval _))
  apply hindep.hasLaw_pi
  intro i
  have h : HasLaw (fun V : BrownianTriple => V i (s + dt) - V i s)
      (gaussianReal 0 (nndist ((s + dt : ℝ≥0) : ℝ) (s : ℝ))) wienerTripleMeasure :=
    (wienerTriple_coordinate_isBrownian i).hasLaw_sub (s + dt) s
  rw [brownianIncrement_nndist s dt] at h
  exact h



/-- Actual vector evaluations have the same centered Gaussian law as the increment kernel. -/
theorem wienerTriple_vectorEval_hasLaw (t : ℝ≥0) :
    HasLaw (fun V : BrownianTriple => WithLp.toLp 2 (fun i : Fin 3 => V i t))
      (radialGaussianVectorMeasure t) wienerTripleMeasure := by
  have hmap : HasLaw (WithLp.toLp 2 : (Fin 3 → ℝ) → EuclideanSpace ℝ (Fin 3))
      (radialGaussianVectorMeasure t) (Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)) :=
    ⟨(PiLp.continuous_toLp 2 _).measurable.aemeasurable, rfl⟩
  exact hmap.comp (wienerTriple_eval_hasLaw t)


/-- Every Cartesian kernel event retains the original translated density. -/
theorem radialGaussianIncrementKernel_apply_set (t : ℝ≥0) (z : EuclideanSpace ℝ (Fin 3))
    (S : Set (EuclideanSpace ℝ (Fin 3))) (hS : MeasurableSet S) :
    radialGaussianIncrementKernel t z S = ∫⁻ w in S, radialGaussianVectorDensity t (w - z) := by
  rw [radialGaussianIncrementKernel, Kernel.withDensity_apply _
    (measurable_radialGaussianVectorDensity_sub t), Kernel.const_apply, withDensity_apply _ hS]


end DOZZ.Proofs
