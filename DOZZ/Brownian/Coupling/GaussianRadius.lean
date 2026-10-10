/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Coupling.CylindricalIntegral
public import DOZZ.Brownian.WienerExists
public import DOZZ.Brownian.ConditionedEntranceProbability
public import DOZZ.Brownian.ConditionedFDDMeasure
public import DOZZ.GMC.FiniteGaussianTilt

/-!
# Gaussian radial entrance law

Apply the cylindrical weighted radial identity to the explicit three-coordinate Gaussian density.
The resulting measure is the literal entrance density `DOZZ.conditionedPositiveEntranceDensity`,
including the zero-drift endpoint.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Independent scalar Gaussians have the product of their scalar Lebesgue densities. -/
theorem pi_gaussianReal_withDensity {n : ℕ} (m : Fin n → ℝ) (t : ℝ≥0) (ht : t ≠ 0) :
    Measure.pi (fun i => gaussianReal (m i) t) =
      (volume : Measure (Fin n → ℝ)).withDensity (fun z => ∏ i, gaussianPDF (m i) t (z i)) := by
  apply Measure.pi_eq
  intro S hS
  rw [withDensity_apply _ (MeasurableSet.univ_pi hS)]
  rw [← lintegral_indicator (MeasurableSet.univ_pi hS)]
  let f : Fin n → ℝ → ℝ≥0∞ := fun i => (S i).indicator (gaussianPDF (m i) t)
  have hf (i : Fin n) : Measurable (f i) := (measurable_gaussianPDF _ _).indicator (hS i)
  have hpoint (z : Fin n → ℝ) :
      (univ.pi S).indicator (fun z => ∏ i, gaussianPDF (m i) t (z i)) z = ∏ i, f i (z i) := by
    by_cases hz : ∀ i, z i ∈ S i
    · simp [f, Set.mem_univ_pi.mpr hz, hz]
    · obtain ⟨i, hi⟩ := not_forall.mp hz
      have hz' : z ∉ univ.pi S := fun h => hi (Set.mem_univ_pi.mp h i)
      have hzero : ∏ j, f j (z j) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [f, hi])
      simp [hz', hzero]
  simp_rw [hpoint]
  rw [volume_pi, lintegral_pi_prod_fin n ℝ volume f hf]
  apply Finset.prod_congr rfl
  intro i hi
  rw [gaussianReal_of_var_ne_zero _ ht, withDensity_apply _ (hS i)]
  exact lintegral_indicator (hS i) _

/-- Normalizing constant of the three-dimensional Gaussian heat density. -/
noncomputable def radialGaussianConstant (t : ℝ) : ℝ := (Real.sqrt (2 * Real.pi * t))⁻¹ ^ 3

/-- Product Gaussian density with a longitudinal mean, written using the Euclidean radius. -/
theorem three_gaussianPDF_product (a : ℝ) (t : ℝ≥0) (ht : t ≠ 0) (z : Fin 3 → ℝ) :
    (∏ i, gaussianPDF (if i = 0 then a * (t : ℝ) else 0) t (z i)) =
      ENNReal.ofReal (radialGaussianConstant t) *
        ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 z‖ ^ 2 / (2 * (t : ℝ)) -
          a ^ 2 * (t : ℝ) / 2)) * ENNReal.ofReal (Real.exp (a * z 0)) := by
  have hsq := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
  have hnorm : ‖WithLp.toLp 2 z‖ ^ 2 = (z 0) ^ 2 + ((z 1) ^ 2 + (z 2) ^ 2) := by
    simpa [Fin.sum_univ_succ] using hsq
  have htr : (t : ℝ) ≠ 0 := by exact_mod_cast ht
  simp only [Fin.prod_univ_three, Fin.isValue, Fin.reduceEq, ite_true, ite_false,
    gaussianPDF, gaussianPDFReal, sub_zero]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by first | positivity | (unfold radialGaussianConstant; positivity)), ← ENNReal.ofReal_mul (by first | positivity | (unfold radialGaussianConstant; positivity))]
  congr 1
  have heq : -(z 0 - a * (t : ℝ)) ^ 2 / (2 * (t : ℝ)) +
      (-(z 1) ^ 2 / (2 * (t : ℝ)) + -(z 2) ^ 2 / (2 * (t : ℝ))) =
      -‖WithLp.toLp 2 z‖ ^ 2 / (2 * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2 + a * z 0 := by
    rw [hnorm]
    field_simp
    ring
  simp only [radialGaussianConstant]
  calc
    _ = (Real.sqrt (2 * Real.pi * (t : ℝ)))⁻¹ ^ 3 *
        Real.exp (-(z 0 - a * (t : ℝ)) ^ 2 / (2 * (t : ℝ)) +
          (-(z 1) ^ 2 / (2 * (t : ℝ)) + -(z 2) ^ 2 / (2 * (t : ℝ)))) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ = _ := by rw [heq, Real.exp_add]; ring

/-- The radial angular factor changes the cubic Gaussian constant into `2/(t sqrt(2πt))`. -/
theorem radialGaussianConstant_angular {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi) * radialGaussianConstant t = 2 / (t * Real.sqrt (2 * Real.pi * t)) := by
  have hs : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr (by positivity)
  have hsq := Real.sq_sqrt (show 0 ≤ 2 * Real.pi * t by positivity)
  unfold radialGaussianConstant
  generalize Real.sqrt (2 * Real.pi * t) = r at *
  field_simp
  nlinarith only [hsq]

/-- The explicit entrance-density coefficient equals the Gaussian angular normalizer. -/
theorem radialGaussianConstant_eq_entranceCoefficient {t : ℝ} (ht : 0 < t) :
    (4 * Real.pi) * radialGaussianConstant t = Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) := by
  rw [radialGaussianConstant_angular ht]
  have hpower : t ^ (3 / 2 : ℝ) = t * Real.sqrt t := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add ht, Real.rpow_one, Real.sqrt_eq_rpow]
  have hroot : Real.sqrt (2 / Real.pi) = 2 / Real.sqrt (2 * Real.pi) := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
    field_simp [Real.sqrt_ne_zero'.mpr (by positivity)]
    rw [Real.sq_sqrt (by positivity)]
  rw [hroot, Real.rpow_neg ht.le, hpower, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  field_simp

/-- Entrance weight extracted from the Gaussian radial integral at positive drift. -/
theorem entranceDensity_eq_radialGaussian {a t y : ℝ} (ha : 0 < a) (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity a t y =
      ((4 * Real.pi) * radialGaussianConstant t) *
        Real.exp (-y ^ 2 / (2 * t) - a ^ 2 * t / 2) * (y * Real.sinh (a * y) / a) := by
  rw [radialGaussianConstant_eq_entranceCoefficient ht, conditionedPositiveEntranceDensity]
  simp only [ha.le, ht, hy, and_self, ite_true, ha.ne', ite_false]
  ring

/-- The same angular normalizer identifies the Maxwell endpoint. -/
theorem entranceDensity_zero_eq_radialGaussian {t y : ℝ} (ht : 0 < t) (hy : 0 < y) :
    conditionedPositiveEntranceDensity 0 t y =
      ((4 * Real.pi) * radialGaussianConstant t) * Real.exp (-y ^ 2 / (2 * t)) * y ^ 2 := by
  rw [conditionedPositiveEntranceDensity_zero_eq_heat ht hy, radialGaussianConstant_angular ht]
  simp only [brownianHeatDensity, ht, ite_true]
  ring

/-- Radial tests of the actual product Gaussian have the explicit entrance density at positive drift. -/
theorem lintegral_three_gaussian_radial_pos (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (a : ℝ) (ha : 0 < a) (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ z, F ‖WithLp.toLp 2 z‖ ∂Measure.pi (fun i : Fin 3 =>
      gaussianReal (if i = 0 then a * (t : ℝ) else 0) t)) =
      ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (conditionedPositiveEntranceDensity a t y) := by
  have htr : 0 < (t : ℝ) := ht
  have hpdf : Measurable (fun z : Fin 3 → ℝ =>
      ∏ i, gaussianPDF (if i = 0 then a * (t : ℝ) else 0) t (z i)) := by
    exact Finset.measurable_prod Finset.univ (fun i _ =>
      (measurable_gaussianPDF _ _).comp (measurable_pi_apply i))
  have hnorm : Measurable (fun z : Fin 3 → ℝ => F ‖WithLp.toLp 2 z‖) :=
    hF.comp (PiLp.continuous_toLp 2 _).norm.measurable
  let G := fun y => F y * ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ)) - a ^ 2 * (t : ℝ) / 2))
  have hG : Measurable G := hF.mul (by fun_prop)
  rw [pi_gaussianReal_withDensity _ t ht.ne',
    lintegral_withDensity_eq_lintegral_mul volume hpdf hnorm]
  simp_rw [Pi.mul_apply, three_gaussianPDF_product a t ht.ne']
  calc
    _ = ENNReal.ofReal (radialGaussianConstant t) *
        ∫⁻ z : Fin 3 → ℝ, G ‖WithLp.toLp 2 z‖ * ENNReal.ofReal (Real.exp (a * z 0)) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      dsimp only [G]
      ring
    _ = ENNReal.ofReal (radialGaussianConstant t) * (ENNReal.ofReal (4 * Real.pi) *
        ∫⁻ y in Ioi (0 : ℝ), G y * ENNReal.ofReal (y * Real.sinh (a * y) / a)) := by
      rw [lintegral_three_radial_exp G hG a ha.ne']
    _ = ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (conditionedPositiveEntranceDensity a t y) := by
      rw [← mul_assoc, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only [G]
      conv_rhs => rw [entranceDensity_eq_radialGaussian ha htr hy]
      conv_rhs => rw [ENNReal.ofReal_mul (by first | positivity | (unfold radialGaussianConstant; positivity)),
        ENNReal.ofReal_mul (by first | positivity | (unfold radialGaussianConstant; positivity)),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi)]
      ring

/-- Maxwell endpoint of the same product-Gaussian radial identity. -/
theorem lintegral_three_gaussian_radial_zero (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ z, F ‖WithLp.toLp 2 z‖ ∂Measure.pi (fun _ : Fin 3 => gaussianReal 0 t)) =
      ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (conditionedPositiveEntranceDensity 0 t y) := by
  have hpdf : Measurable (fun z : Fin 3 → ℝ => ∏ i, gaussianPDF 0 t (z i)) := by
    exact Finset.measurable_prod Finset.univ (fun i _ =>
      (measurable_gaussianPDF _ _).comp (measurable_pi_apply i))
  have hnorm : Measurable (fun z : Fin 3 → ℝ => F ‖WithLp.toLp 2 z‖) :=
    hF.comp (PiLp.continuous_toLp 2 _).norm.measurable
  let G := fun y => F y * ENNReal.ofReal (Real.exp (-y ^ 2 / (2 * (t : ℝ))))
  have hG : Measurable G := hF.mul (by fun_prop)
  have hproduct (z : Fin 3 → ℝ) : (∏ i, gaussianPDF 0 t (z i)) =
      ENNReal.ofReal (radialGaussianConstant t) * ENNReal.ofReal (Real.exp (-‖WithLp.toLp 2 z‖ ^ 2 / (2 * (t : ℝ)))) := by
    simpa using three_gaussianPDF_product 0 t ht.ne' z
  rw [pi_gaussianReal_withDensity _ t ht.ne',
    lintegral_withDensity_eq_lintegral_mul volume hpdf hnorm]
  simp_rw [Pi.mul_apply, hproduct]
  calc
    _ = ENNReal.ofReal (radialGaussianConstant t) * ∫⁻ z : Fin 3 → ℝ, G ‖WithLp.toLp 2 z‖ := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro z
      dsimp only [G]
      ring
    _ = ENNReal.ofReal (radialGaussianConstant t) * (ENNReal.ofReal (4 * Real.pi) *
        ∫⁻ y in Ioi (0 : ℝ), G y * ENNReal.ofReal (y ^ 2)) := by
      rw [lintegral_three_radial_zero G hG]
    _ = ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (conditionedPositiveEntranceDensity 0 t y) := by
      rw [← mul_assoc, ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro y hy
      dsimp only [G]
      conv_rhs => rw [entranceDensity_zero_eq_radialGaussian (t := (t : ℝ)) (show 0 < (t : ℝ) from ht) hy]
      conv_rhs => rw [ENNReal.ofReal_mul (by first | positivity | (unfold radialGaussianConstant; positivity)),
        ENNReal.ofReal_mul (by first | positivity | (unfold radialGaussianConstant; positivity)),
        ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi)]
      ring

/-- The exact entrance integral for every nonnegative drift, including zero. -/
theorem lintegral_three_gaussian_radial (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (a : ℝ) (ha : 0 ≤ a) (t : ℝ≥0) (ht : 0 < t) :
    (∫⁻ z, F ‖WithLp.toLp 2 z‖ ∂Measure.pi (fun i : Fin 3 =>
      gaussianReal (if i = 0 then a * (t : ℝ) else 0) t)) =
      ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (conditionedPositiveEntranceDensity a t y) := by
  rcases ha.eq_or_lt with rfl | hapos
  · simpa using lintegral_three_gaussian_radial_zero F hF t ht
  · exact lintegral_three_gaussian_radial_pos F hF a hapos t ht

/-- The entrance density has no mass at nonpositive radii. -/
theorem entranceDensity_eq_zero_of_nonpositive (a t y : ℝ) (hy : y ≤ 0) :
    conditionedPositiveEntranceDensity a t y = 0 := by
  simp [conditionedPositiveEntranceDensity, not_lt.mpr hy]

/-- The restricted radial integral equals the full literal entrance-density integral. -/
theorem lintegral_entranceDensity_Ioi (F : ℝ → ℝ≥0∞) (a t : ℝ) :
    (∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (conditionedPositiveEntranceDensity a t y)) =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveEntranceDensity a t y) := by
  apply setLIntegral_eq_of_support_subset
  intro y hy
  by_contra hpos
  have hy0 : y ≤ 0 := le_of_not_gt hpos
  exact hy (by simp [entranceDensity_eq_zero_of_nonpositive a t y hy0])

/-- Gaussian norm pushforward equals the actual entrance-density measure. -/
theorem three_gaussian_norm_map_eq_entrance (a : ℝ) (ha : 0 ≤ a) (t : ℝ≥0) (ht : 0 < t) :
    (Measure.pi (fun i : Fin 3 => gaussianReal (if i = 0 then a * (t : ℝ) else 0) t)).map
      (fun z => ‖WithLp.toLp 2 z‖) = conditionedPositiveEntranceMeasure a t := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_map hF (PiLp.continuous_toLp 2 _).norm.measurable,
    lintegral_three_gaussian_radial F hF a ha t ht, lintegral_entranceDensity_Ioi]
  rw [conditionedPositiveEntranceMeasure, lintegral_withDensity_eq_lintegral_mul volume
    (measurable_conditionedPositiveEntranceDensity_arg a t).ennreal_ofReal hF]
  apply lintegral_congr
  intro y
  exact mul_comm _ _

/-- The GFF-derived unconditional radial path has the exact entrance marginal at every positive time. -/
theorem rogersPitmanWienerMeasure_eval_eq_entrance (a : ℝ) (ha : 0 ≤ a)
    (t : ℝ≥0) (ht : 0 < t) :
    (rogersPitmanWienerMeasure a).map (fun p => p t) = conditionedPositiveEntranceMeasure a t := by
  rw [rogersPitmanWienerMeasure_eval_map, three_gaussian_norm_map_eq_entrance a ha t ht]


/-- Reflection gives the negative conditioned entrance marginal on the original path carrier. -/
theorem negativeRogersPitmanWienerMeasure_eval_eq_entrance (a : ℝ) (ha : 0 ≤ a)
    (t : ℝ≥0) (ht : 0 < t) :
    (negativeRogersPitmanWienerMeasure a).map (fun p => p t) =
      (conditionedPositiveEntranceMeasure a t).map Neg.neg := by
  have hnorm : Measurable (fun z : Fin 3 → ℝ => ‖WithLp.toLp 2 z‖) :=
    (PiLp.continuous_toLp 2 _).norm.measurable
  rw [← rogersPitmanWienerMeasure_eval_eq_entrance a ha t ht,
    rogersPitmanWienerMeasure, negativeRogersPitmanWienerMeasure,
    rogersPitmanEntranceMeasure, negativeRogersPitmanEntranceMeasure]
  rw [Measure.map_map (ContinuousMap.measurable_eval t) (measurable_negativeRogersPitmanPath a),
    Measure.map_map (ContinuousMap.measurable_eval t) (measurable_rogersPitmanPath a),
    Measure.map_map measurable_neg ((ContinuousMap.measurable_eval t).comp (measurable_rogersPitmanPath a))]
  rfl

/-- An axis-centered Gaussian norm has the zero-drift BES(3) transition law from its positive mean. -/
theorem three_gaussian_axis_norm_map_eq_transition (x : ℝ) (hx : 0 < x)
    (t : ℝ≥0) (ht : 0 < t) :
    (Measure.pi (fun i : Fin 3 => gaussianReal (if i = 0 then x else 0) t)).map
      (fun z => ‖WithLp.toLp 2 z‖) = conditionedPositiveTransitionMeasure 0 t x := by
  have htr : 0 < (t : ℝ) := ht
  have ha : 0 < x / (t : ℝ) := div_pos hx htr
  have hmean : x / (t : ℝ) * (t : ℝ) = x := div_mul_cancel₀ _ htr.ne'
  have h := three_gaussian_norm_map_eq_entrance (x / (t : ℝ)) ha.le t ht
  rw [hmean] at h
  rw [h, conditionedPositiveEntranceMeasure, conditionedPositiveTransitionMeasure]
  apply withDensity_congr_ae
  filter_upwards [] with y
  by_cases hy : 0 < y
  · rw [conditionedPositiveEntranceDensity_eq_zeroDriftTransition ha htr hy, hmean]
  · rw [entranceDensity_eq_zero_of_nonpositive _ _ _ (le_of_not_gt hy)]
    simp [conditionedPositiveTransitionDensity, hy]

/-- Nonnegative tests for the axis-centered Gaussian BES(3) transition. -/
theorem lintegral_three_gaussian_axis_transition (x : ℝ) (hx : 0 < x)
    (t : ℝ≥0) (ht : 0 < t) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z, F ‖WithLp.toLp 2 z‖ ∂Measure.pi (fun i : Fin 3 =>
      gaussianReal (if i = 0 then x else 0) t)) =
      ∫⁻ y, F y * ENNReal.ofReal (conditionedPositiveTransitionDensity 0 t x y) := by
  rw [← lintegral_map hF (PiLp.continuous_toLp 2 _).norm.measurable,
    three_gaussian_axis_norm_map_eq_transition x hx t ht, conditionedPositiveTransitionMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (show Measurable (fun y : ℝ => ENNReal.ofReal (conditionedPositiveTransitionDensity 0 t x y)) from
        ((measurable_conditionedPositiveTransitionDensity_pair 0 t).comp
          (measurable_const.prodMk measurable_id)).ennreal_ofReal) hF]
  apply lintegral_congr
  intro y
  exact mul_comm _ _

/-- The reflected path's entrance tests retain the literal signed state. -/
theorem negativeRogersPitmanWienerMeasure_lintegral_eval (a : ℝ) (ha : 0 ≤ a)
    (t : ℝ≥0) (ht : 0 < t) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (p t) ∂negativeRogersPitmanWienerMeasure a) =
      ∫⁻ y, F (-y) * ENNReal.ofReal (conditionedPositiveEntranceDensity a t y) := by
  rw [← lintegral_map hF (ContinuousMap.measurable_eval t),
    negativeRogersPitmanWienerMeasure_eval_eq_entrance a ha t ht,
    lintegral_map hF measurable_neg, conditionedPositiveEntranceMeasure,
    lintegral_withDensity_eq_lintegral_mul volume
      (measurable_conditionedPositiveEntranceDensity_arg a t).ennreal_ofReal
      (show Measurable (fun y : ℝ => F (-y)) from hF.comp measurable_neg)]
  apply lintegral_congr
  intro y
  exact mul_comm _ _

/-- The exact Gaussian radial entrance law is absolutely continuous at every positive time. -/
theorem rogersPitmanWienerMeasure_eval_absolutelyContinuous (a : ℝ) (ha : 0 ≤ a)
    (t : ℝ≥0) (ht : 0 < t) :
    (rogersPitmanWienerMeasure a).map (fun p => p t) ≪ (volume : Measure ℝ) := by
  rw [rogersPitmanWienerMeasure_eval_eq_entrance a ha t ht, conditionedPositiveEntranceMeasure]
  exact withDensity_absolutelyContinuous _ _


/-- Probability one is supported at strictly positive entrance radii. -/
theorem rogersPitmanWienerMeasure_eval_positive (a : ℝ) (ha : 0 ≤ a)
    (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ y ∂(rogersPitmanWienerMeasure a).map (fun p => p t), 0 < y := by
  rw [rogersPitmanWienerMeasure_eval_eq_entrance a ha t ht, conditionedPositiveEntranceMeasure]
  rw [ae_withDensity_iff (measurable_conditionedPositiveEntranceDensity_arg a t).ennreal_ofReal]
  filter_upwards [] with y
  intro hy
  by_contra hpos
  exact hy (by simp [entranceDensity_eq_zero_of_nonpositive a t y (le_of_not_gt hpos)])



/-- The raw independent Gaussian coordinates already realize the entrance law. -/
theorem rogersPitmanVectorAt_norm_hasLaw (a : ℝ) (ha : 0 ≤ a) (t : ℝ≥0) (ht : 0 < t) :
    HasLaw (fun V : BrownianTriple => ‖rogersPitmanVectorAt a V t‖)
      (conditionedPositiveEntranceMeasure a t) wienerTripleMeasure := by
  have hmap : HasLaw (fun z : Fin 3 → ℝ => ‖WithLp.toLp 2 z‖)
      (conditionedPositiveEntranceMeasure a t)
      (Measure.pi (fun i : Fin 3 => gaussianReal (if i = 0 then a * (t : ℝ) else 0) t)) :=
    ⟨(PiLp.continuous_toLp 2 _).norm.measurable.aemeasurable,
      three_gaussian_norm_map_eq_entrance a ha t ht⟩
  exact hmap.comp (wienerTriple_drifted_eval_hasLaw a t)




end DOZZ.Proofs
