/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Convolution

/-!
# GaussianFields ABK convolution bounds

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- A uniformly bounded square-integrable function supported in a finite Euclidean ball has its
`L²` mass bounded by `M^2` times the volume of that ball. -/
theorem integral_norm_sq_le_measure_mul_of_abs_le_of_support_subset {d : Nat}
    {f : Vec d → ℝ} {M A : ℝ}
    (hf_int : Integrable (fun y : Vec d => (f y) ^ (2 : Nat))
      (volume : Measure (Vec d)))
    (hM_nonneg : 0 ≤ M) (hA_nonneg : 0 ≤ A)
    (hpoint : ∀ y : Vec d, |f y| ≤ M)
    (hsupport : Function.support f ⊆ {y : Vec d | euclideanNorm y ≤ A}) :
    ∫ y : Vec d, ‖(f y) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d)) ≤
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal * M ^ (2 : Nat) := by
  let S : Set (Vec d) := {y : Vec d | euclideanNorm y ≤ A}
  have hS_meas : MeasurableSet S := measurableSet_euclideanClosedBall A
  have hS_finite : (volume : Measure (Vec d)) S ≠ ∞ := by
    have hvol_le : (volume : Measure (Vec d)) S ≤ ENNReal.ofReal ((2 * A) ^ d) :=
      volume_euclideanClosedBall_le hA_nonneg
    exact (hvol_le.trans_lt ENNReal.ofReal_lt_top).ne
  have hconst_int :
      Integrable (S.indicator fun _ : Vec d => M ^ (2 : Nat))
        (volume : Measure (Vec d)) := by
    exact (integrableOn_const (C := M ^ (2 : Nat)) (μ := volume) hS_finite).integrable_indicator
      hS_meas
  have hpointwise :
      (fun y : Vec d => ‖(f y) ^ (2 : Nat)‖) ≤ᶠ[ae (volume : Measure (Vec d))]
        S.indicator (fun _ : Vec d => M ^ (2 : Nat)) := by
    filter_upwards with y
    by_cases hyS : y ∈ S
    · have hsq_nonneg : 0 ≤ (f y) ^ (2 : Nat) := sq_nonneg (f y)
      have hsq_le : (f y) ^ (2 : Nat) ≤ M ^ (2 : Nat) := by
        exact sq_le_sq.2 (by simpa [abs_of_nonneg hM_nonneg] using hpoint y)
      rw [Set.indicator_of_mem hyS, Real.norm_eq_abs, abs_of_nonneg hsq_nonneg]
      exact hsq_le
    · have hfy_zero : f y = 0 := by
        by_contra hne
        exact hyS (hsupport hne)
      rw [Set.indicator_of_notMem hyS, hfy_zero]
      simp
  calc
    ∫ y : Vec d, ‖(f y) ^ (2 : Nat)‖ ∂(volume : Measure (Vec d))
        ≤ ∫ y : Vec d, S.indicator (fun _ : Vec d => M ^ (2 : Nat)) y
            ∂(volume : Measure (Vec d)) :=
          integral_mono_ae hf_int.norm hconst_int hpointwise
    _ = ((volume : Measure (Vec d)) S).toReal * M ^ (2 : Nat) := by
          rw [integral_indicator_const, MeasureTheory.measureReal_def, smul_eq_mul]
          exact hS_meas

/-- A uniformly bounded integrable function supported in a measurable finite set has integral
bounded by `M` times the set volume. -/
theorem abs_integral_le_measure_mul_of_abs_le_of_support_subset {d : Nat}
    {f : Vec d → ℝ} {M : ℝ} {S : Set (Vec d)}
    (hf_int : Integrable f (volume : Measure (Vec d)))
    (hS_meas : MeasurableSet S)
    (hS_finite : (volume : Measure (Vec d)) S ≠ ∞)
    (hpoint : ∀ y : Vec d, |f y| ≤ M)
    (hsupport : Function.support f ⊆ S) :
    |∫ y : Vec d, f y ∂(volume : Measure (Vec d))| ≤
      ((volume : Measure (Vec d)) S).toReal * M := by
  have hconst_int :
      Integrable (S.indicator fun _ : Vec d => M)
        (volume : Measure (Vec d)) := by
    exact (integrableOn_const (C := M) (μ := volume) hS_finite).integrable_indicator hS_meas
  have hpointwise :
      (fun y : Vec d => ‖f y‖) ≤ᶠ[ae (volume : Measure (Vec d))]
        S.indicator (fun _ : Vec d => M) := by
    filter_upwards with y
    by_cases hyS : y ∈ S
    · rw [Set.indicator_of_mem hyS, Real.norm_eq_abs]
      exact hpoint y
    · have hfy_zero : f y = 0 := by
        by_contra hne
        exact hyS (hsupport hne)
      rw [Set.indicator_of_notMem hyS, hfy_zero]
      simp
  calc
    |∫ y : Vec d, f y ∂(volume : Measure (Vec d))|
        = ‖∫ y : Vec d, f y ∂(volume : Measure (Vec d))‖ := by
          rw [Real.norm_eq_abs]
    _ ≤ ∫ y : Vec d, ‖f y‖ ∂(volume : Measure (Vec d)) :=
          norm_integral_le_integral_norm f
    _ ≤ ∫ y : Vec d, S.indicator (fun _ : Vec d => M) y
          ∂(volume : Measure (Vec d)) :=
          integral_mono_ae hf_int.norm hconst_int hpointwise
    _ = ((volume : Measure (Vec d)) S).toReal * M := by
          rw [integral_indicator_const, MeasureTheory.measureReal_def, smul_eq_mul]
          exact hS_meas

/-- Small-scale pointwise bound: compact support and boundedness of `ψ`, together with the cutoff
support, give `|ζ_r * ψ| = O(r^d)`. -/
theorem abs_abkSpatialConvolution_le_small {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r y, 0 < r →
      |abkSpatialConvolution ζ ψ r y| ≤ C * r ^ d := by
  rcases exists_abs_meanZeroTestFunction_le ψ with ⟨B, hB_nonneg, hB⟩
  refine ⟨B * 2 ^ d, mul_nonneg hB_nonneg (pow_nonneg zero_le_two d), ?_⟩
  intro r y hr
  let S : Set (Vec d) := Metric.closedBall y r
  have hS_meas : MeasurableSet S := measurableSet_closedBall
  have hS_finite : (volume : Measure (Vec d)) S ≠ ∞ := by
    rw [Real.volume_pi_closedBall y hr.le, Fintype.card_fin]
    exact ENNReal.ofReal_ne_top
  let F : Vec d → ℝ := fun x => abkScaledCutoff ζ r (y - x) * ψ x
  have hpoint : ∀ x : Vec d, |F x| ≤ B := by
    intro x
    have hz_nonneg : 0 ≤ abkScaledCutoff ζ r (y - x) := ζ.nonneg _
    have hz_le_one : abkScaledCutoff ζ r (y - x) ≤ 1 := ζ.le_one _
    calc
      |F x| = |abkScaledCutoff ζ r (y - x) * ψ x| := rfl
      _ = |abkScaledCutoff ζ r (y - x)| * |ψ x| := abs_mul _ _
      _ = abkScaledCutoff ζ r (y - x) * |ψ x| := by rw [abs_of_nonneg hz_nonneg]
      _ ≤ 1 * B := mul_le_mul hz_le_one (hB x) (abs_nonneg (ψ x)) zero_le_one
      _ = B := by ring
  have hsupport : Function.support F ⊆ S := by
    intro x hx
    have hcut_ne : abkScaledCutoff ζ r (y - x) ≠ 0 := by
      intro hzero
      exact hx (by simp [F, hzero])
    have hnorm : euclideanNorm (y - x) ≤ r :=
      euclideanNorm_le_of_abkScaledCutoff_ne_zero ζ hr hcut_ne
    have hdist : dist x y ≤ r := by
      calc
        dist x y = ‖x - y‖ := dist_eq_norm x y
        _ ≤ euclideanNorm (x - y) := norm_le_euclideanNorm (x - y)
        _ = euclideanNorm (y - x) := euclideanNorm_sub_comm x y
        _ ≤ r := hnorm
    simpa [S, Metric.mem_closedBall] using hdist
  have hbound :=
    abs_integral_le_measure_mul_of_abs_le_of_support_subset
      (f := F) (M := B) (S := S)
      (integrable_abkSpatialConvolution_integrand ζ ψ r y)
      hS_meas hS_finite hpoint hsupport
  have hvol_real : ((volume : Measure (Vec d)) S).toReal = (2 * r) ^ d := by
    rw [Real.volume_pi_closedBall y hr.le, Fintype.card_fin]
    rw [ENNReal.toReal_ofReal]
    exact pow_nonneg (mul_nonneg zero_le_two hr.le) d
  calc
    |abkSpatialConvolution ζ ψ r y| = |∫ x : Vec d, F x ∂(volume : Measure (Vec d))| := rfl
    _ ≤ ((volume : Measure (Vec d)) S).toReal * B := hbound
    _ = (2 * r) ^ d * B := by rw [hvol_real]
    _ = (B * 2 ^ d) * r ^ d := by
          rw [mul_pow]
          ring

/-- Small-scale spatial square estimate: `‖ζ_r * ψ‖₂² = O(r^{2d})`.  After multiplying by the
ABK prefactor `r^{-(d+1)}`, this becomes the small-scale `O(r^{d-1})` integrand. -/
theorem integral_norm_sq_abkSpatialConvolution_le_small {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) →
      (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d))) ≤ C * r ^ (2 * d) := by
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨R, hR_nonneg, hψ_support⟩
  rcases abs_abkSpatialConvolution_le_small ζ ψ with ⟨M, hM_nonneg, hpoint⟩
  let A : ℝ := (d : ℝ) * (R + 1)
  let V : ℝ := (2 * A) ^ d
  refine ⟨V * M ^ (2 : Nat), mul_nonneg ?_ (sq_nonneg M), ?_⟩
  · exact pow_nonneg
      (mul_nonneg zero_le_two
        (mul_nonneg (Nat.cast_nonneg d) (add_nonneg hR_nonneg zero_le_one))) d
  intro r hr_pos hr_le_one hsection_int
  have hA_nonneg : 0 ≤ A :=
    mul_nonneg (Nat.cast_nonneg d) (add_nonneg hR_nonneg zero_le_one)
  have hsupport :
      Function.support (fun y : Vec d => abkSpatialConvolution ζ ψ r y) ⊆
        {y : Vec d | euclideanNorm y ≤ A} := by
    have hsupport_r :=
      support_abkSpatialConvolution_subset_euclideanClosedBall ζ ψ hψ_support hr_pos
    intro y hy
    have hy_r := hsupport_r hy
    have hrad_le : (d : ℝ) * (R + r) ≤ A := by
      dsimp [A]
      have hRr : R + r ≤ R + 1 := by linarith
      exact mul_le_mul_of_nonneg_left hRr (Nat.cast_nonneg d)
    exact hy_r.trans hrad_le
  have hbasic :=
    integral_norm_sq_le_measure_mul_of_abs_le_of_support_subset
      (f := fun y : Vec d => abkSpatialConvolution ζ ψ r y)
      (M := M * r ^ d) (A := A)
      hsection_int
      (mul_nonneg hM_nonneg (pow_nonneg hr_pos.le d))
      hA_nonneg
      (fun y => hpoint r y hr_pos)
      hsupport
  have hvol_real_le :
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal ≤ V := by
    have hvol_le :
        (volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A} ≤
          ENNReal.ofReal V := by
      simpa [V] using volume_euclideanClosedBall_le (d := d) hA_nonneg
    have hV_nonneg : 0 ≤ V := by
      exact pow_nonneg (mul_nonneg zero_le_two hA_nonneg) d
    simpa [ENNReal.toReal_ofReal hV_nonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol_le
  have hmass_le :
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal *
          (M * r ^ d) ^ (2 : Nat) ≤
        V * (M * r ^ d) ^ (2 : Nat) := by
    exact mul_le_mul_of_nonneg_right hvol_real_le (sq_nonneg (M * r ^ d))
  calc
    (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d)))
        ≤ ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal *
            (M * r ^ d) ^ (2 : Nat) := hbasic
    _ ≤ V * (M * r ^ d) ^ (2 : Nat) := hmass_le
    _ = (V * M ^ (2 : Nat)) * r ^ (2 * d) := by
          calc
            V * (M * r ^ d) ^ (2 : Nat) = V * M ^ (2 : Nat) * (r ^ d) ^ (2 : Nat) := by
              ring
            _ = (V * M ^ (2 : Nat)) * r ^ (2 * d) := by
              rw [← pow_mul, Nat.mul_comm d 2]

/-- For large positive scales, the support ball from the ABK convolution has volume `O(r^d)`. -/
theorem volume_abkSupportBall_le_large {d : Nat} {R r : ℝ}
    (hR_nonneg : 0 ≤ R) (hr : 1 ≤ r) :
    volume {y : Vec d | euclideanNorm y ≤ (d : ℝ) * (R + r)} ≤
      ENNReal.ofReal (((2 * (d : ℝ) * (R + 1)) ^ d) * r ^ d) := by
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hA_nonneg : 0 ≤ (d : ℝ) * (R + r) :=
    mul_nonneg hd_nonneg (add_nonneg hR_nonneg hr_nonneg)
  have hRr : R + r ≤ (R + 1) * r := by
    nlinarith [mul_nonneg hR_nonneg (sub_nonneg.mpr hr)]
  have hbase_le :
      2 * ((d : ℝ) * (R + r)) ≤ (2 * (d : ℝ) * (R + 1)) * r := by
    nlinarith [hRr, hd_nonneg]
  have hbase_nonneg : 0 ≤ 2 * ((d : ℝ) * (R + r)) :=
    mul_nonneg zero_le_two hA_nonneg
  have hpow_le :
      (2 * ((d : ℝ) * (R + r))) ^ d ≤
        ((2 * (d : ℝ) * (R + 1)) * r) ^ d :=
    pow_le_pow_left₀ hbase_nonneg hbase_le d
  calc
    volume {y : Vec d | euclideanNorm y ≤ (d : ℝ) * (R + r)}
        ≤ ENNReal.ofReal ((2 * ((d : ℝ) * (R + r))) ^ d) :=
          volume_euclideanClosedBall_le hA_nonneg
    _ ≤ ENNReal.ofReal (((2 * (d : ℝ) * (R + 1)) * r) ^ d) :=
          ENNReal.ofReal_le_ofReal hpow_le
    _ = ENNReal.ofReal (((2 * (d : ℝ) * (R + 1)) ^ d) * r ^ d) := by
          rw [mul_pow]

/-- The large-scale ABK spatial square estimate following from mean-zero cancellation.  The bound
has the form `O(r^d |r|^{-2})`; after the kernel prefactor `r^{-(d+1)}` this is the ABK `O(r^-3)`
scale integrand. -/
theorem integral_norm_sq_abkSpatialConvolution_le_large {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) →
      (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d))) ≤ C * r ^ d * |r|⁻¹ ^ (2 : Nat) := by
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨R, hR_nonneg, hψ_support⟩
  rcases abs_abkSpatialConvolution_le_scaled_moment ζ ψ with ⟨L, hL_nonneg, hpoint⟩
  let J : ℝ := ∫ x : Vec d, euclideanNorm x * |ψ x|
  have hJ_nonneg : 0 ≤ J := by
    exact integral_nonneg fun x => mul_nonneg (euclideanNorm_nonneg x) (abs_nonneg (ψ x))
  let Cvol : ℝ := (2 * (d : ℝ) * (R + 1)) ^ d
  let C : ℝ := Cvol * (L * J) ^ (2 : Nat)
  have hCvol_nonneg : 0 ≤ Cvol := by
    exact pow_nonneg
      (mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg d))
        (add_nonneg hR_nonneg zero_le_one)) d
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg hCvol_nonneg (sq_nonneg (L * J))
  refine ⟨C, hC_nonneg, ?_⟩
  intro r hr hsection_int
  have hr_nonneg : 0 ≤ r := le_trans zero_le_one hr
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let A : ℝ := (d : ℝ) * (R + r)
  have hA_nonneg : 0 ≤ A :=
    mul_nonneg (Nat.cast_nonneg d) (add_nonneg hR_nonneg hr_nonneg)
  have hsupport :
      Function.support (fun y : Vec d => abkSpatialConvolution ζ ψ r y) ⊆
        {y : Vec d | euclideanNorm y ≤ A} := by
    simpa [A] using support_abkSpatialConvolution_subset_euclideanClosedBall ζ ψ
      hψ_support hr_pos
  have hM_nonneg : 0 ≤ L * |r|⁻¹ * J :=
    mul_nonneg (mul_nonneg hL_nonneg (inv_nonneg.mpr (abs_nonneg r))) hJ_nonneg
  have hbasic :=
    integral_norm_sq_le_measure_mul_of_abs_le_of_support_subset
      (f := fun y : Vec d => abkSpatialConvolution ζ ψ r y)
      (M := L * |r|⁻¹ * J) (A := A)
      hsection_int hM_nonneg hA_nonneg (hpoint r) hsupport
  have hvol_le :
      (volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A} ≤
        ENNReal.ofReal (Cvol * r ^ d) := by
    simpa [A, Cvol] using volume_abkSupportBall_le_large (d := d) (R := R) (r := r)
      hR_nonneg hr
  have hvol_real_le :
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal ≤
        Cvol * r ^ d := by
    have hfinite : ENNReal.ofReal (Cvol * r ^ d) ≠ ∞ := ENNReal.ofReal_ne_top
    have hnonneg : 0 ≤ Cvol * r ^ d :=
      mul_nonneg hCvol_nonneg (pow_nonneg hr_nonneg d)
    simpa [ENNReal.toReal_ofReal hnonneg] using ENNReal.toReal_mono hfinite hvol_le
  have hmass_le :
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal *
          (L * |r|⁻¹ * J) ^ (2 : Nat) ≤
        (Cvol * r ^ d) * (L * |r|⁻¹ * J) ^ (2 : Nat) := by
    exact mul_le_mul_of_nonneg_right hvol_real_le (sq_nonneg (L * |r|⁻¹ * J))
  calc
    (∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d)))
        ≤ ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ A}).toReal *
            (L * |r|⁻¹ * J) ^ (2 : Nat) := hbasic
    _ ≤ (Cvol * r ^ d) * (L * |r|⁻¹ * J) ^ (2 : Nat) := hmass_le
    _ = C * r ^ d * |r|⁻¹ ^ (2 : Nat) := by
          simp [C, Cvol, abs_of_nonneg hr_nonneg]
          ring_nf

/-- The large-scale ABK power count:
`r^{-(d+1)} r^d r^{-2} = r^{-3}`. -/
theorem abk_largeScale_power_identity {d : Nat} {r : ℝ} (hr : 0 < r) :
    (r ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) * r ^ d * (|r|⁻¹) ^ (2 : Nat) =
      r ^ (-3 : ℝ) := by
  have hr_nonneg : 0 ≤ r := hr.le
  let a : ℝ := -(((d : ℝ) + 1) / 2)
  have hpref : (r ^ a) ^ (2 : Nat) = r ^ (-((d : ℝ) + 1)) := by
    calc
      (r ^ a) ^ (2 : Nat)
          = r ^ (a * ((2 : Nat) : ℝ)) :=
            (Real.rpow_mul_natCast hr_nonneg a 2).symm
      _ = r ^ (-((d : ℝ) + 1)) := by
            congr 1
            dsimp [a]
            ring
  have hinv : (|r|⁻¹) ^ (2 : Nat) = r ^ (-2 : ℝ) := by
    rw [abs_of_pos hr]
    rw [← Real.rpow_neg_one r]
    calc
      (r ^ (-1 : ℝ)) ^ (2 : Nat)
          = r ^ ((-1 : ℝ) * ((2 : Nat) : ℝ)) :=
            (Real.rpow_mul_natCast hr_nonneg (-1 : ℝ) 2).symm
      _ = r ^ (-2 : ℝ) := by
            congr 1
            ring
  have hnat : r ^ d = r ^ (d : ℝ) := by
    rw [Real.rpow_natCast]
  change (r ^ a) ^ (2 : Nat) * r ^ d * (|r|⁻¹) ^ (2 : Nat) = r ^ (-3 : ℝ)
  rw [hpref, hinv, hnat]
  rw [← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 1
  ring

/-- The small-scale ABK power count:
`r^{-(d+1)} r^{2d} = r^{d-1}`. -/
theorem abk_smallScale_power_identity {d : Nat} {r : ℝ} (hr : 0 < r) :
    (r ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) * r ^ (2 * d) =
      r ^ ((d : ℝ) - 1) := by
  have hr_nonneg : 0 ≤ r := hr.le
  let a : ℝ := -(((d : ℝ) + 1) / 2)
  have hpref : (r ^ a) ^ (2 : Nat) = r ^ (-((d : ℝ) + 1)) := by
    calc
      (r ^ a) ^ (2 : Nat)
          = r ^ (a * ((2 : Nat) : ℝ)) :=
            (Real.rpow_mul_natCast hr_nonneg a 2).symm
      _ = r ^ (-((d : ℝ) + 1)) := by
            congr 1
            dsimp [a]
            ring
  have hnat : r ^ (2 * d) = r ^ (((2 * d : Nat) : ℝ)) := by
    rw [Real.rpow_natCast]
  change (r ^ a) ^ (2 : Nat) * r ^ (2 * d) = r ^ ((d : ℝ) - 1)
  rw [hpref, hnat]
  rw [← Real.rpow_add hr]
  congr 1
  norm_num [Nat.cast_mul]
  ring

end GaussianFields

end
