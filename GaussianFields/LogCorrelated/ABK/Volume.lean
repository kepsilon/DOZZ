/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import GaussianFields.LogCorrelated.ABK.Constants

/-!
# GaussianFields.LogCorrelated/ABK/Volume

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- The Mathlib `EuclideanSpace` norm of `WithLp.toLp 2 x` is the project
Euclidean norm of `x`. -/
theorem norm_toLp_two_eq_euclideanNorm {d : Nat} (x : Vec d) :
    ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))‖ = euclideanNorm x := by
  rw [EuclideanSpace.norm_eq, euclideanNorm, euclideanNormSq_eq_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Real.norm_eq_abs, sq_abs]
  ring

/-- The ABK unit ball is the preimage of Mathlib's Euclidean unit ball under `toLp`. -/
theorem preimage_toLp_two_unitBall (d : Nat) :
    (fun x : Vec d => (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d))) ⁻¹'
        Metric.ball 0 (1 : ℝ) =
      abkUnitBall d := by
  ext x
  simp only [Set.mem_preimage, Metric.mem_ball, abkUnitBall, abkBall,
    Set.mem_ofPred_eq]
  rw [dist_eq_norm, sub_zero]
  rw [norm_toLp_two_eq_euclideanNorm]

/-- Exact Lebesgue volume of the ABK Euclidean unit ball, in `ENNReal` form. -/
theorem volume_abkUnitBall (d : Nat) (hd : 0 < d) :
    (volume : Measure (Vec d)) (abkUnitBall d) =
      ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [← preimage_toLp_two_unitBall d]
  rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
    measurableSet_ball.nullMeasurableSet]
  have hvol :=
    EuclideanSpace.volume_ball (Fin d) (0 : EuclideanSpace ℝ (Fin d)) (1 : ℝ)
  simpa [Fintype.card_fin] using hvol

/-- Exact real-valued volume of the ABK Euclidean unit ball. -/
theorem abkUnitBallVolume_eq_sqrt_pi_div_gamma (d : Nat) (hd : 0 < d) :
    abkUnitBallVolume d =
      Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have harg : 0 < (d : ℝ) / 2 + 1 := by positivity
  have hnonneg :
      0 ≤ Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
    exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) d)
      (Real.Gamma_pos_of_pos harg).le
  rw [abkUnitBallVolume, volume_abkUnitBall d hd]
  exact ENNReal.toReal_ofReal hnonneg

/-- Convert the power of `sqrt π` in the Euclidean ball volume to a real power of `π`. -/
theorem sqrt_pi_pow_eq_pi_rpow_half_mul (d : Nat) :
    Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  calc
    (Real.pi ^ (1 / (2 : ℝ))) ^ d
        = Real.pi ^ ((1 / (2 : ℝ)) * (d : ℝ)) := by
            rw [← Real.rpow_mul_natCast Real.pi_pos.le (1 / (2 : ℝ)) d]
    _ = Real.pi ^ ((d : ℝ) / 2) := by ring_nf

/-- Gamma-function form of the ABK covariance prefactor
`d |B_1| / (2π)^d`. -/
theorem abkLGFCovarianceConstant_eq_gammaFormula (d : Nat) (hd : 0 < d) :
    abkLGFCovarianceConstant d =
      2 ^ (1 - (d : ℝ)) * Real.pi ^ (-(d : ℝ) / 2) /
        Real.Gamma ((d : ℝ) / 2) := by
  let s : ℝ := (d : ℝ) / 2
  have hs_pos : 0 < s := by
    dsimp [s]
    positivity
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hgamma_ne : Real.Gamma s ≠ 0 :=
    (Real.Gamma_pos_of_pos hs_pos).ne'
  have hd_real_ne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hgamma : Real.Gamma ((d : ℝ) / 2 + 1) =
      ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by
    exact Real.Gamma_add_one hs_ne
  have htwo :
      2 ^ (1 - (d : ℝ)) = (2 : ℝ) / 2 ^ d := by
    calc
      2 ^ (1 - (d : ℝ))
          = (2 : ℝ) ^ (1 : ℝ) / (2 : ℝ) ^ (d : ℝ) :=
              Real.rpow_sub (by norm_num : (0 : ℝ) < 2) 1 (d : ℝ)
      _ = (2 : ℝ) / 2 ^ d := by rw [Real.rpow_one, Real.rpow_natCast]
  have hpi :
      Real.pi ^ (-(d : ℝ) / 2) =
        Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ d := by
    have hexp : -(d : ℝ) / 2 = (d : ℝ) / 2 - (d : ℝ) := by ring
    calc
      Real.pi ^ (-(d : ℝ) / 2)
          = Real.pi ^ ((d : ℝ) / 2 - (d : ℝ)) := by rw [hexp]
      _ = Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ (d : ℝ) :=
            Real.rpow_sub Real.pi_pos ((d : ℝ) / 2) (d : ℝ)
      _ = Real.pi ^ ((d : ℝ) / 2) / Real.pi ^ d := by rw [Real.rpow_natCast]
  rw [abkLGFCovarianceConstant, abkUnitBallVolume_eq_sqrt_pi_div_gamma d hd,
    sqrt_pi_pow_eq_pi_rpow_half_mul d, hgamma, mul_pow, htwo, hpi]
  field_simp [hd_real_ne, hgamma_ne, Real.pi_ne_zero, two_ne_zero]

/-- In two dimensions the ABK covariance prefactor is `1/(2π)`. -/
theorem abkLGFCovarianceConstant_two :
    abkLGFCovarianceConstant 2 = (2 * Real.pi)⁻¹ := by
  rw [abkLGFCovarianceConstant_eq_gammaFormula 2 (by norm_num)]
  norm_num
  rw [Real.rpow_neg_one]
  ring

/-- The ABK covariance prefactor is positive in positive dimension. -/
theorem abkLGFCovarianceConstant_pos (d : Nat) (hd : 0 < d) :
    0 < abkLGFCovarianceConstant d := by
  rw [abkLGFCovarianceConstant_eq_gammaFormula d hd]
  positivity

/-- The canonical ABK normalization radicand is nonnegative. -/
theorem abkNormalizationRadicand_nonneg {d : Nat} (ζ : ABKCutoff d) :
    0 ≤ abkNormalizationRadicand ζ := by
  have hvol : 0 ≤ abkUnitBallVolume d := by
    unfold abkUnitBallVolume
    exact ENNReal.toReal_nonneg
  have hnum : 0 ≤ (d : ℝ) * abkUnitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg d) hvol
  have hden : 0 ≤ abkM0 ζ * (2 * Real.pi) ^ d :=
    mul_nonneg (le_of_lt (abkM0_pos ζ))
      (le_of_lt (pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) d))
  unfold abkNormalizationRadicand
  exact div_nonneg hnum hden

/-- The canonical ABK normalization radicand is positive in positive dimension. -/
theorem abkNormalizationRadicand_pos {d : Nat} (hd : 0 < d) (ζ : ABKCutoff d) :
    0 < abkNormalizationRadicand ζ := by
  have hd_real : 0 < (d : ℝ) := by exact_mod_cast hd
  have hvol : 0 < abkUnitBallVolume d := by
    rw [abkUnitBallVolume_eq_sqrt_pi_div_gamma d hd]
    positivity
  have hnum : 0 < (d : ℝ) * abkUnitBallVolume d := mul_pos hd_real hvol
  have hden : 0 < abkM0 ζ * (2 * Real.pi) ^ d :=
    mul_pos (abkM0_pos ζ) (pow_pos (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos) d)
  unfold abkNormalizationRadicand
  exact div_pos hnum hden

/-- The Appendix A non-degeneracy constant `c_*` is positive for `d ≥ 2`. -/
theorem abkCStar_pos (d : Nat) (hd : 2 ≤ d) :
    0 < abkCStar d := by
  have hd_pos : 0 < d := lt_of_lt_of_le (by norm_num : 0 < 2) hd
  have hd_real_pos : 0 < (d : ℝ) := by exact_mod_cast hd_pos
  have hdm1_pos : 0 < (d : ℝ) - 1 := by
    have : (1 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hd)
    linarith
  have hratio : 0 < ((d : ℝ) - 1) / (d : ℝ) := div_pos hdm1_pos hd_real_pos
  have hcov : 0 < abkLGFCovarianceConstant d := abkLGFCovarianceConstant_pos d hd_pos
  have hlog : 0 < Real.log 3 := Real.log_pos (by norm_num : (1 : ℝ) < 3)
  rw [abkCStar]
  exact mul_pos (mul_pos hratio hcov) hlog

/-- The closed Gamma-function expression for the Appendix A non-degeneracy constant `c_*`. -/
theorem abkCStar_eq_gammaFormula (d : Nat) (hd : 0 < d) :
    abkCStar d = abkCStarGammaFormula d := by
  have hd_real_ne : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  have hgamma_ne : Real.Gamma ((d : ℝ) / 2) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity : 0 < (d : ℝ) / 2)).ne'
  rw [abkCStar, abkCStarGammaFormula, abkLGFCovarianceConstant_eq_gammaFormula d hd]
  field_simp [hd_real_ne, hgamma_ne]

end GaussianFields

end
