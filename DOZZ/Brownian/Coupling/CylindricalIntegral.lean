/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Cylindrical integration for three-dimensional radial tests

Use the ordinary complex-plane polar formula on the transverse plane. The remaining substitution
`y = sqrt(x² + ρ²)` and Tonelli reduce a radial exponential tilt to a one-dimensional integral.
The origin and zero-tilt endpoint are retained explicitly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology Classical

namespace DOZZ.Proofs

/-- Radius after fixing the longitudinal coordinate and the transverse radius. -/
noncomputable def cylindricalRadius (x ρ : ℝ) : ℝ := Real.sqrt (x ^ 2 + ρ ^ 2)

theorem continuous_cylindricalRadius (x : ℝ) : Continuous (cylindricalRadius x) := by
  unfold cylindricalRadius
  fun_prop

theorem cylindricalRadius_pos (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < cylindricalRadius x ρ := by
  apply Real.sqrt_pos.2
  nlinarith only [sq_nonneg x, sq_pos_of_pos hρ]

theorem cylindricalRadius_sq (x ρ : ℝ) : (cylindricalRadius x ρ) ^ 2 = x ^ 2 + ρ ^ 2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg x) (sq_nonneg ρ))

theorem abs_lt_cylindricalRadius (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    |x| < cylindricalRadius x ρ := by
  have hpos := cylindricalRadius_pos x hρ
  have hsquare := cylindricalRadius_sq x ρ
  nlinarith only [sq_abs x, sq_pos_of_pos hρ, abs_nonneg x, hpos, hsquare]

theorem strictMonoOn_cylindricalRadius (x : ℝ) :
    StrictMonoOn (cylindricalRadius x) (Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  have hsa := cylindricalRadius_sq x a
  have hsb := cylindricalRadius_sq x b
  have hpa := cylindricalRadius_pos x ha
  have hpb := cylindricalRadius_pos x hb
  nlinarith only [ha, hb, hab, hsa, hsb, hpa, hpb]

/-- Every radius greater than the longitudinal magnitude has a unique positive transverse radius. -/
theorem cylindricalRadius_image_Ioi (x : ℝ) : cylindricalRadius x '' Ioi 0 = Ioi |x| := by
  ext y
  constructor
  · rintro ⟨ρ, hρ, rfl⟩
    exact abs_lt_cylindricalRadius x hρ
  · intro hy
    change |x| < y at hy
    have hypos : 0 < y := (abs_nonneg x).trans_lt hy
    have hsq : 0 < y ^ 2 - x ^ 2 := by
      nlinarith only [hy, abs_nonneg x, sq_abs x]
    refine ⟨Real.sqrt (y ^ 2 - x ^ 2), Real.sqrt_pos.2 hsq, ?_⟩
    unfold cylindricalRadius
    rw [Real.sq_sqrt hsq.le]
    have heq : x ^ 2 + (y ^ 2 - x ^ 2) = y ^ 2 := by ring
    rw [heq, Real.sqrt_sq hypos.le]

/-- The cylindrical radial substitution has derivative `ρ / sqrt(x²+ρ²)`. -/
theorem hasDerivAt_cylindricalRadius (x : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (cylindricalRadius x) (ρ / cylindricalRadius x ρ) ρ := by
  have hnonzero : x ^ 2 + ρ ^ 2 ≠ 0 := by
    have hpos : 0 < x ^ 2 + ρ ^ 2 := by nlinarith only [sq_nonneg x, sq_pos_of_pos hρ]
    exact hpos.ne'
  have hder := (((hasDerivAt_id ρ).pow 2).const_add (x ^ 2)).sqrt hnonzero
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] at hder
  change HasDerivAt (cylindricalRadius x) (2 * ρ / (2 * cylindricalRadius x ρ)) ρ at hder
  convert hder using 1
  ring

/-- The one-dimensional Jacobian cancels the radial weight, including arbitrary nonnegative tests. -/
theorem lintegral_cylindricalRadius (x : ℝ) (F : ℝ → ℝ≥0∞) :
    (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ)) =
      ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y := by
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
    (fun ρ hρ => (hasDerivAt_cylindricalRadius x hρ).hasDerivWithinAt)
    (strictMonoOn_cylindricalRadius x).injOn (fun y => ENNReal.ofReal y * F y)
  rw [cylindricalRadius_image_Ioi] at hchange
  rw [hchange]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  have hy := cylindricalRadius_pos x hρ
  dsimp only
  rw [abs_of_pos (div_pos hρ hy), ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg hρ.le hy.le),
    div_mul_cancel₀ _ hy.ne']

/-- Ordinary complex-plane polar integration contributes the transverse angular factor `2π`. -/
theorem lintegral_complex_cylindricalRadius (x : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖)) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ) := by
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (cylindricalRadius x p.1)) :=
    measurable_fst.ennreal_ofReal.mul (hF.comp ((continuous_cylindricalRadius x).measurable.comp
      measurable_fst))
  calc
    _ = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal p.1 * F (cylindricalRadius x ‖Complex.polarCoord.symm p‖) :=
      (Complex.lintegral_comp_polarCoord_symm (fun w => F (cylindricalRadius x ‖w‖))).symm
    _ = ∫⁻ p : ℝ × ℝ in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * F (cylindricalRadius x p.1) := by
      apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [Complex.norm_polarCoord_symm, abs_of_pos hp.1]
    _ = ∫⁻ ρ in Ioi (0 : ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal ρ * F (cylindricalRadius x ρ) :=
      setLIntegral_prod _ hm.aemeasurable
    _ = (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal ρ * F (cylindricalRadius x ρ)) *
        ENNReal.ofReal (2 * Real.pi) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      have hlength : Real.pi - -Real.pi = 2 * Real.pi := by ring
      rw [hlength]
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = _ := mul_comm _ _

/-- After changing the positive transverse radius, only `y > |x|` remains. -/
theorem lintegral_complex_radial_section (x : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y := by
  rw [lintegral_complex_cylindricalRadius x F hF, lintegral_cylindricalRadius]

/-- The triangular longitudinal/radial region after the positive-radius substitution. -/
noncomputable def cylindricalStrip (F H : ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ :=
  if |p.1| < p.2 then ENNReal.ofReal p.2 * F p.2 * H p.1 else 0

theorem measurable_cylindricalStrip (F H : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hH : Measurable H) : Measurable (cylindricalStrip F H) := by
  exact ((measurable_snd.ennreal_ofReal.mul (hF.comp measurable_snd)).mul
    (hH.comp measurable_fst)).ite
      (measurableSet_lt (continuous_fst.abs.measurable) measurable_snd) measurable_const

/-- Vertical sections are exactly the radial tails `y > |x|`. -/
theorem lintegral_cylindricalStrip_right (F H : ℝ → ℝ≥0∞) (x : ℝ) :
    (∫⁻ y, cylindricalStrip F H (x, y)) =
      ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x := by
  rw [← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr
  intro y
  rfl

/-- Horizontal sections are the interval `(-y,y)` of longitudinal coordinates. -/
theorem lintegral_cylindricalStrip_left (F H : ℝ → ℝ≥0∞) (hH : Measurable H) (y : ℝ) :
    (∫⁻ x, cylindricalStrip F H (x, y)) =
      (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  calc
    _ = ∫⁻ x, (Ioo (-y) y).indicator (fun x => (ENNReal.ofReal y * F y) * H x) x := by
      apply lintegral_congr
      intro x
      simp only [cylindricalStrip, indicator, mem_Ioo, abs_lt]
    _ = ∫⁻ x in Ioo (-y) y, (ENNReal.ofReal y * F y) * H x :=
      lintegral_indicator measurableSet_Ioo _
    _ = _ := lintegral_const_mul _ hH

/-- Tonelli converts radial tails at fixed longitudinal coordinate into bounded longitudinal
intervals at fixed radius, with the positive-radius endpoint retained. -/
theorem lintegral_cylindrical_tails (F H : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hH : Measurable H) :
    (∫⁻ x, ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x) =
      ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  calc
    _ = ∫⁻ x, ∫⁻ y, cylindricalStrip F H (x, y) := by
      simp_rw [lintegral_cylindricalStrip_right]
    _ = ∫⁻ y, ∫⁻ x, cylindricalStrip F H (x, y) :=
      lintegral_lintegral_swap (measurable_cylindricalStrip F H hF hH).aemeasurable
    _ = ∫⁻ y, (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
      simp_rw [lintegral_cylindricalStrip_left F H hH]
    _ = _ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro y hy
      by_contra hpos
      have hy0 : y ≤ 0 := le_of_not_gt hpos
      have hempty : Ioo (-y) y = ∅ := Ioo_eq_empty_of_le (by linarith only [hy0])
      apply hy
      simp only [hempty, Measure.restrict_empty, lintegral_zero_measure, mul_zero]

/-- Cylindrical integration on `ℝ × ℂ`: an arbitrary longitudinal weight is integrated on each
radial cross-section, without spherical coordinates or an angular disintegration theorem. -/
theorem lintegral_radial_longitudinal (F H : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hH : Measurable H) :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖) * H p.1) =
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) * ∫⁻ x in Ioo (-y) y, H x := by
  have hradius : Continuous (fun p : ℝ × ℂ => cylindricalRadius p.1 ‖p.2‖) := by
    unfold cylindricalRadius
    fun_prop
  have hmeas : Measurable (fun p : ℝ × ℂ => F (cylindricalRadius p.1 ‖p.2‖) * H p.1) :=
    (hF.comp hradius.measurable).mul (hH.comp measurable_fst)
  have hsection (x : ℝ) :
      (∫⁻ w : ℂ, F (cylindricalRadius x ‖w‖) * H x) =
        ENNReal.ofReal (2 * Real.pi) *
          ∫⁻ y in Ioi |x|, ENNReal.ofReal y * F y * H x := by
    rw [lintegral_mul_const _ (show Measurable (fun w : ℂ => F (cylindricalRadius x ‖w‖)) from
      hF.comp ((continuous_cylindricalRadius x).comp continuous_norm).measurable)]
    rw [lintegral_complex_radial_section x F hF]
    rw [lintegral_mul_const _ (show Measurable (fun y : ℝ => ENNReal.ofReal y * F y) from
      measurable_id.ennreal_ofReal.mul hF), mul_assoc]
  rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
  simp_rw [hsection]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_cylindrical_tails F H hF hH]

/-- Explicit longitudinal exponential integral, allowing either sign of the tilt. -/
theorem integral_exp_longitudinal (c y : ℝ) (hc : c ≠ 0) (hy : 0 ≤ y) :
    (∫ x in Ioo (-y) y, Real.exp (c * x)) = 2 * Real.sinh (c * y) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith only [hy]),
    intervalIntegral.integral_comp_mul_left Real.exp hc, integral_exp]
  rw [Real.sinh_eq]
  simp only [smul_eq_mul, mul_neg]
  ring

/-- The exponential is integrable on every bounded longitudinal section. -/
theorem integrableOn_exp_longitudinal (c y : ℝ) :
    IntegrableOn (fun x : ℝ => Real.exp (c * x)) (Ioo (-y) y) := by
  have hcont : Continuous (fun x : ℝ => Real.exp (c * x)) := by fun_prop
  exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

/-- Nonnegative integral version of the longitudinal tilt calculation. -/
theorem lintegral_exp_longitudinal (c y : ℝ) (hc : c ≠ 0) (hy : 0 ≤ y) :
    (∫⁻ x in Ioo (-y) y, ENNReal.ofReal (Real.exp (c * x))) =
      ENNReal.ofReal (2 * Real.sinh (c * y) / c) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_longitudinal c y)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)),
    integral_exp_longitudinal c y hc hy]


/-- The longitudinal tilt average is nonnegative for either sign of nonzero drift. -/
theorem sinh_div_nonneg_longitudinal (c y : ℝ) (hc : c ≠ 0) (hy : 0 ≤ y) :
    0 ≤ Real.sinh (c * y) / c := by
  have h : 0 ≤ ∫ x in Ioo (-y) y, Real.exp (c * x) :=
    integral_nonneg (fun x => (Real.exp_pos _).le)
  rw [integral_exp_longitudinal c y hc hy] at h
  have heq : 2 * Real.sinh (c * y) / c = 2 * (Real.sinh (c * y) / c) := by ring
  rw [heq] at h
  linarith only [h]

/-- Weighted radial identity in cylindrical coordinates. This is valid also for infinite tests. -/
theorem lintegral_radial_exp (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖) * ENNReal.ofReal (Real.exp (c * p.1))) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ),
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
  have hH : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (c * x))) := by fun_prop
  rw [lintegral_radial_longitudinal F _ hF hH]
  have hsection : (∫⁻ y in Ioi (0 : ℝ), (ENNReal.ofReal y * F y) *
      ∫⁻ x in Ioo (-y) y, ENNReal.ofReal (Real.exp (c * x))) =
      ENNReal.ofReal (2 : ℝ) * ∫⁻ y in Ioi (0 : ℝ),
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    rw [lintegral_exp_longitudinal c y hc hy.le]
    have hn := sinh_div_nonneg_longitudinal c y hc hy.le
    have heq : 2 * Real.sinh (c * y) / c = 2 * (Real.sinh (c * y) / c) := by ring
    have heq' : y * Real.sinh (c * y) / c = y * (Real.sinh (c * y) / c) := by ring
    rw [heq, heq', ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_mul hy.le]
    ring
  rw [hsection, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 2
  ring

/-- Zero tilt gives the ordinary three-dimensional radial weight `4πy²`. -/
theorem lintegral_radial_zero (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ × ℂ, F (cylindricalRadius p.1 ‖p.2‖)) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
  have h := lintegral_radial_longitudinal F (fun _ => 1) hF measurable_const
  simp only [mul_one, lintegral_const, one_mul, Measure.restrict_apply_univ,
    Real.volume_Ioo] at h
  rw [h]
  have hsection : (∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal y * F y * ENNReal.ofReal (y - -y)) =
      ENNReal.ofReal (2 : ℝ) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    have heq : y - -y = 2 * y := by ring
    rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), pow_two,
      ENNReal.ofReal_mul hy.le]
    ring
  rw [hsection, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 2
  ring

/-- The longitudinal/transverse coordinate equivalence for the actual three-real carrier. -/
noncomputable def cylindricalCoordinates : (Fin 3 → ℝ) ≃ᵐ (ℝ × ℂ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) Complex.measurableEquivPi.symm)

/-- Cylindrical coordinates preserve three-dimensional Lebesgue volume. -/
theorem cylindricalCoordinates_measurePreserving : MeasurePreserving cylindricalCoordinates := by
  exact ((MeasurePreserving.id (volume : Measure ℝ)).prod
    Complex.volume_preserving_equiv_pi.symm).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0)

/-- The longitudinal component is the first Cartesian component. -/
theorem cylindricalCoordinates_fst (z : Fin 3 → ℝ) : (cylindricalCoordinates z).1 = z 0 := rfl

/-- Cartesian Euclidean norm equals the cylindrical radius. -/
theorem cylindricalCoordinates_radius (z : Fin 3 → ℝ) :
    cylindricalRadius (cylindricalCoordinates z).1 ‖(cylindricalCoordinates z).2‖ =
      ‖WithLp.toLp 2 z‖ := by
  have hsq := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 z)
  have hcomplex : ‖(cylindricalCoordinates z).2‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2 := by
    change ‖Complex.measurableEquivPi.symm (Fin.tail z)‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Fin.tail, pow_two]
  have heq : (z 0) ^ 2 + ‖(cylindricalCoordinates z).2‖ ^ 2 = ‖WithLp.toLp 2 z‖ ^ 2 := by
    rw [hcomplex]
    simpa [Fin.sum_univ_succ, add_assoc] using hsq.symm
  rw [cylindricalRadius, cylindricalCoordinates_fst, heq, Real.sqrt_sq (norm_nonneg _)]

/-- Nonnegative integrals transport directly to the three-real Cartesian carrier. -/
theorem lintegral_cylindricalCoordinates (f : ℝ × ℂ → ℝ≥0∞) :
    (∫⁻ z : Fin 3 → ℝ, f (cylindricalCoordinates z)) = ∫⁻ p : ℝ × ℂ, f p :=
  cylindricalCoordinates_measurePreserving.lintegral_comp_emb
    cylindricalCoordinates.measurableEmbedding f

/-- Weighted radial identity on the exact Euclidean three-coordinate carrier. -/
theorem lintegral_three_radial_exp (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (c : ℝ) (hc : c ≠ 0) :
    (∫⁻ z : Fin 3 → ℝ, F ‖WithLp.toLp 2 z‖ * ENNReal.ofReal (Real.exp (c * z 0))) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ),
        F y * ENNReal.ofReal (y * Real.sinh (c * y) / c) := by
  rw [← lintegral_radial_exp F hF c hc]
  rw [← lintegral_cylindricalCoordinates]
  apply lintegral_congr
  intro z
  rw [cylindricalCoordinates_radius, cylindricalCoordinates_fst]

/-- The Maxwell radial integration formula on the same Cartesian carrier. -/
theorem lintegral_three_radial_zero (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ z : Fin 3 → ℝ, F ‖WithLp.toLp 2 z‖) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ y in Ioi (0 : ℝ), F y * ENNReal.ofReal (y ^ 2) := by
  rw [← lintegral_radial_zero F hF, ← lintegral_cylindricalCoordinates]
  apply lintegral_congr
  intro z
  rw [cylindricalCoordinates_radius]

/-- Completing the square for a Gaussian mean on the longitudinal axis. -/
theorem cylindrical_gaussian_exponent (a t x ρ : ℝ) (ht : t ≠ 0) :
    -((x - a * t) ^ 2 + ρ ^ 2) / (2 * t) =
      -(cylindricalRadius x ρ) ^ 2 / (2 * t) - a ^ 2 * t / 2 + a * x := by
  rw [cylindricalRadius_sq]
  field_simp
  ring

/-- The drifted Gaussian exponential separates into a radial weight and longitudinal tilt. -/
theorem cylindrical_gaussian_weight (a t x ρ : ℝ) (ht : t ≠ 0) :
    ENNReal.ofReal (Real.exp (-((x - a * t) ^ 2 + ρ ^ 2) / (2 * t))) =
      ENNReal.ofReal (Real.exp (-(cylindricalRadius x ρ) ^ 2 / (2 * t) - a ^ 2 * t / 2)) *
        ENNReal.ofReal (Real.exp (a * x)) := by
  rw [cylindrical_gaussian_exponent a t x ρ ht, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]


end DOZZ.Proofs
