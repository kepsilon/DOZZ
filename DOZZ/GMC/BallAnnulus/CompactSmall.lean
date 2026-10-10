/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.BallScaling
public import DOZZ.GMC.Annulus.ReferenceIntensity

/-! Sharp two-sided bounds on small balls with arbitrary compact centers. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Reference scaling and uniform location transport give both sides at every real
subcritical order, including all inverse orders. -/
theorem gmc_compact_small_ball_twoSided_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (p : ℝ) (hp : p < 4 / γ ^ 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ r : ℝ, 0 < r → r ≤ 1/8 →
      ENNReal.ofReal (C⁻¹ * r ^ gmcScaleExponent γ p) ≤
        gmcMassMoment P M (Metric.ball z r) p ∧
      gmcMassMoment P M (Metric.ball z r) p ≤
        ENNReal.ofReal (C * r ^ gmcScaleExponent γ p) := by
  obtain ⟨B, hB, hnorm⟩ := hK.isBounded.exists_pos_norm_le
  let R := B+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.exp
    (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1+R))) / 2 * |p ^ 2-p|)) *
      ENNReal.ofReal ((1+R)^4) ^ |p|
  have hTtop : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top)
  have hTpos : 0 < T := by
    dsimp [T]
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    · intro hz
      rcases ENNReal.rpow_eq_zero_iff.mp hz with h | h
      · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne' h.1
      · exact ENNReal.ofReal_ne_top h.1
  let t := T.toReal
  have ht : 0 < t := ENNReal.toReal_pos hTpos.ne' hTtop
  have hT : T = ENNReal.ofReal t := (ENNReal.ofReal_toReal hTtop).symm
  obtain ⟨C, hC, hlocal⟩ := (gmc_local_twoSided_ball_scaling_iff
    P X hX γ hγ hγ2 M hM (1/8) p (by norm_num) (by norm_num)).mp
      ⟨gmc_reference_ball_moment_pos P X hX γ hγ hγ2 M hM (by norm_num) le_rfl p,
       gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM 0 (1/8)
         (by norm_num) le_rfl p hp⟩
  refine ⟨t*C, mul_pos ht hC, ?_⟩
  intro z hz r hr hr8
  have hzR : ‖z‖+r ≤ R := by dsimp [R]; linarith [hnorm z hz]
  have hzeroR : ‖(0 : ℂ)‖+r ≤ R := by simp only [norm_zero, zero_add]; dsimp [R]; linarith
  have hz0 := gmc_ball_moment_transfer P X hX γ hγ hγ2 M hM z 0 r R hr hr8 hR hzR hzeroR p hp
  have h0z := gmc_ball_moment_transfer P X hX γ hγ hγ2 M hM 0 z r R hr hr8 hR hzeroR hzR p hp
  change _ ≤ T * _ at hz0 h0z
  rw [hT] at hz0 h0z
  have href := hlocal 0 r hr hr8 (by simp only [norm_zero, zero_add]; linarith)
  constructor
  · have he : ENNReal.ofReal t⁻¹ * ENNReal.ofReal t = 1 := by
      rw [← ENNReal.ofReal_mul (inv_pos.mpr ht).le, inv_mul_cancel₀ ht.ne']
      norm_num
    calc
      ENNReal.ofReal ((t*C)⁻¹ * r ^ gmcScaleExponent γ p) =
          ENNReal.ofReal t⁻¹ * ENNReal.ofReal (C⁻¹ * r ^ gmcScaleExponent γ p) := by
            rw [← ENNReal.ofReal_mul (inv_pos.mpr ht).le]
            congr 1
            rw [mul_inv_rev]
            ring
      _ ≤ ENNReal.ofReal t⁻¹ * (ENNReal.ofReal t * gmcMassMoment P M (Metric.ball z r) p) :=
        mul_le_mul_of_nonneg_left (href.1.trans h0z) (by positivity)
      _ = _ := by rw [← mul_assoc, he, one_mul]
  · calc
      _ ≤ ENNReal.ofReal t * ENNReal.ofReal (C * r ^ gmcScaleExponent γ p) :=
        hz0.trans (mul_le_mul_of_nonneg_left href.2 (by positivity))
      _ = _ := by rw [← ENNReal.ofReal_mul ht.le]; congr 1; ring

end DOZZ.Proofs
end
