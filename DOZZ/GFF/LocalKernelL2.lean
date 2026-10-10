/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.CovarianceAlgebra
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# DOZZ.GFF.LocalKernelL2

The logarithmic diagonal singularity is square integrable locally in the plane. This is the
analytic input for the local L² Schur bound used by the G5 construction.
-/

@[expose] public section

open MeasureTheory Set Metric

namespace DOZZ

/-- The square of the planar logarithmic singularity is integrable on every ball.

Near zero, `|log r| r^(1/4)` is bounded, so the square is dominated by a constant times
`r^(-1/2)`, which is locally integrable in dimension two. Away from zero the same domination
follows from the elementary logarithm-versus-power bound. -/
theorem integrable_log_norm_sq_on_ball (R : ℝ) :
    IntegrableOn (fun z : ℂ => (Real.log ‖z‖) ^ 2) (ball (0 : ℂ) R) := by
  have hdim : 1 ≤ Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  have hα : (1 / 2 : ℝ) < Module.finrank ℝ ℂ := by rw [Complex.finrank_real_complex]; norm_num
  have hmeas : AEStronglyMeasurable (fun z : ℂ => (Real.log ‖z‖) ^ 2)
      (volume : Measure ℂ) := by
    exact (Real.measurable_log.comp measurable_norm).pow_const 2 |>.aestronglyMeasurable
  have hdecay : ∀ᵐ z ∂(volume : Measure ℂ).restrict (ball (0 : ℂ) R),
      ‖(Real.log ‖z‖) ^ 2‖ ≤ 16 * max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    rw [mem_ball_zero_iff] at hz
    have hz0 : ‖z‖ ≤ max R 1 := hz.le.trans (le_max_left R 1)
    by_cases hzsmall : ‖z‖ ≤ 1
    · by_cases hzzero : ‖z‖ = 0
      · simp [hzzero]
      · have hzNe : z ≠ 0 := by
          intro hz'
          apply hzzero
          simp [hz']
        have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hzNe
        have hrootpos : 0 < ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
        have hb := Real.abs_log_mul_self_rpow_lt ‖z‖ (1 / 4 : ℝ) hpos hzsmall
          (by norm_num : (0 : ℝ) < 1 / 4)
        have hmulAbs : |Real.log ‖z‖| * ‖z‖ ^ (1 / 4 : ℝ) ≤ 4 := by
          have hb' := hb.le
          rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos hpos _)] at hb'
          norm_num at hb' ⊢
          exact hb'
        have hpow : (‖z‖ ^ (1 / 4 : ℝ)) ^ 2 = ‖z‖ ^ (1 / 2 : ℝ) := by
          rw [pow_two, ← Real.rpow_add hpos]
          congr 1
          norm_num
        have hmul : (Real.log ‖z‖) ^ 2 * ‖z‖ ^ (1 / 2 : ℝ) ≤ 16 := by
          have hs := (sq_le_sq₀
            (by positivity : 0 ≤ |Real.log ‖z‖| * ‖z‖ ^ (1 / 4 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 4)).2 hmulAbs
          rw [mul_pow, sq_abs, hpow] at hs
          norm_num at hs
          exact hs
        have hsmall : (Real.log ‖z‖) ^ 2 ≤ 16 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
          calc
            (Real.log ‖z‖) ^ 2 ≤ 16 / ‖z‖ ^ (1 / 2 : ℝ) :=
              (le_div_iff₀ hrootpos).2 hmul
            _ = 16 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
              rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg z)]
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hsmall.trans (mul_le_mul_of_nonneg_right
          (by nlinarith [le_max_right R 1])
          (Real.rpow_pos_of_pos hpos _).le)
    · have hpos : 0 < ‖z‖ :=
        (by norm_num : (0 : ℝ) < 1).trans (lt_of_not_ge hzsmall)
      have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (le_of_not_ge hzsmall)
      have hl : Real.log ‖z‖ ≤ 4 * ‖z‖ ^ (1 / 4 : ℝ) := by
        have h := Real.log_le_rpow_div (norm_nonneg z)
          (by norm_num : (0 : ℝ) < 1 / 4)
        rw [div_eq_mul_inv, show (1 / 4 : ℝ)⁻¹ = 4 by norm_num] at h
        nlinarith
      have hpowmul : (‖z‖ ^ (1 / 4 : ℝ)) ^ 2 = ‖z‖ ^ (1 / 2 : ℝ) := by
        rw [pow_two, ← Real.rpow_add hpos]
        congr 1
        norm_num
      have hsq : (Real.log ‖z‖) ^ 2 ≤ 16 * ‖z‖ ^ (1 / 2 : ℝ) := by
        have hs := (sq_le_sq₀ hlog
          (by positivity : (0 : ℝ) ≤ 4 * ‖z‖ ^ (1 / 4 : ℝ))).2 hl
        rw [mul_pow, hpowmul] at hs
        nlinarith [hs]
      have hrootpos : 0 < ‖z‖ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hpos _
      have hrootmul : ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) = ‖z‖ := by
        calc
          _ = ‖z‖ ^ (1 / 2 + 1 / 2 : ℝ) := by rw [← Real.rpow_add hpos]
          _ = ‖z‖ := by norm_num [Real.rpow_one]
      have hpow : ‖z‖ ^ (1 / 2 : ℝ) ≤ max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
        calc
          ‖z‖ ^ (1 / 2 : ℝ) =
              ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) / ‖z‖ ^ (1 / 2 : ℝ) := by
            field_simp
          _ ≤ max R 1 / ‖z‖ ^ (1 / 2 : ℝ) := by
            have hz0' : ‖z‖ ^ (1 / 2 : ℝ) * ‖z‖ ^ (1 / 2 : ℝ) ≤ max R 1 := by
              rw [hrootmul]
              exact hz0
            exact div_le_div_of_nonneg_right hz0' hrootpos.le
          _ = max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by
            rw [div_eq_mul_inv, Real.rpow_neg (norm_nonneg z)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc
        (Real.log ‖z‖) ^ 2 ≤ 16 * ‖z‖ ^ (1 / 2 : ℝ) := hsq
        _ ≤ 16 * (max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = 16 * max R 1 * ‖z‖ ^ (-(1 / 2 : ℝ)) := by ring
  exact integrableOn_ball_of_norm_le_rpow hdim hα hdecay hmeas

private def subProdMap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 - p.2, p.2)

private def invSubProdMap (p : ℂ × ℂ) : ℂ × ℂ := (p.1 + p.2, p.2)

/-- The square of the difference-log singularity is integrable on the product of two bounded
balls. The measure-preserving shear `(x,y) ↦ (x-y,y)` reduces this to the one-variable result. -/
theorem integrable_log_norm_sub_sq_on_pair_ball (R : ℝ) :
    IntegrableOn (fun p : ℂ × ℂ => (Real.log ‖p.1 - p.2‖) ^ 2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let B : Set ℂ := ball 0 R
  let A : Set ℂ := ball 0 (2 * R)
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have hA : IntegrableOn (fun z : ℂ => (Real.log ‖z‖) ^ 2) A volume := by
    simpa [A] using integrable_log_norm_sq_on_ball (2 * R)
  have hBlt : volume B < ⊤ := by
    dsimp [B]
    exact measure_ball_lt_top
  have : IsFiniteMeasure (volume.restrict B) :=
    (MeasureTheory.isFiniteMeasure_restrict).2 hBlt.ne
  have hAprod : IntegrableOn (fun p : ℂ × ℂ => (Real.log ‖p.1‖) ^ 2)
      (A ×ˢ B) μ := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hA.comp_fst (volume.restrict B)
  have hsurj : Function.Surjective subProdMap := by
    intro p
    refine ⟨invSubProdMap p, ?_⟩
    ext <;> simp [subProdMap, invSubProdMap]
  have hrange : Set.range subProdMap = Set.univ := Set.range_eq_univ.mpr hsurj
  have hleft : Function.LeftInverse invSubProdMap subProdMap := by
    intro p
    ext <;> simp [subProdMap, invSubProdMap]
  have hTmeas : Measurable subProdMap := by
    change Measurable (fun p : ℂ × ℂ => (p.1 - p.2, p.2))
    exact (measurable_fst.sub measurable_snd).prodMk measurable_snd
  have hInvMeas : Measurable invSubProdMap := by
    change Measurable (fun p : ℂ × ℂ => (p.1 + p.2, p.2))
    exact (measurable_fst.add measurable_snd).prodMk measurable_snd
  have hRangeMeas : MeasurableSet (Set.range subProdMap) := by
    rw [hrange]
    exact MeasurableSet.univ
  have hT : MeasurableEmbedding subProdMap :=
    MeasurableEmbedding.of_measurable_inverse hTmeas hRangeMeas hInvMeas hleft
  have hMP : MeasurePreserving subProdMap μ μ := by
    dsimp [μ, subProdMap]
    exact MeasureTheory.measurePreserving_sub_prod _ _
  let S : Set (ℂ × ℂ) := B ×ˢ B
  have himage : subProdMap '' S ⊆ A ×ˢ B := by
    rintro q ⟨p, hp, rfl⟩
    rcases hp with ⟨hx, hy⟩
    change p.1 - p.2 ∈ A ∧ p.2 ∈ B
    constructor
    · rw [mem_ball_zero_iff] at hx hy ⊢
      calc
        ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
        _ < R + R := add_lt_add hx hy
        _ = 2 * R := by ring
    · exact hy
  have himageInt : IntegrableOn (fun q : ℂ × ℂ => (Real.log ‖q.1‖) ^ 2)
      (subProdMap '' S) μ := hAprod.mono_set himage
  have hpreimageInt : IntegrableOn
      ((fun q : ℂ × ℂ => (Real.log ‖q.1‖) ^ 2) ∘ subProdMap) S μ :=
    (hMP.integrableOn_image hT).mp himageInt
  have heq : (fun p : ℂ × ℂ => (Real.log ‖p.1‖) ^ 2) ∘ subProdMap =
      fun p : ℂ × ℂ => (Real.log ‖p.1 - p.2‖) ^ 2 := by
    funext p
    rfl
  have hpre' : IntegrableOn (fun p : ℂ × ℂ => (Real.log ‖p.1 - p.2‖) ^ 2) S μ := by
    simpa only [heq] using hpreimageInt
  simpa [B, S, μ] using hpre'

/-- The potential part of the covariance kernel is bounded on every ball, hence square integrable
on its product with itself. -/
theorem integrable_log_normPlus_sq_on_pair_ball (R : ℝ) :
    IntegrableOn (fun p : ℂ × ℂ => (Real.log (normPlus p.1)) ^ 2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let B : Set ℂ := ball 0 R
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have hcont : Continuous (fun z : ℂ => Real.log (normPlus z)) := by
    apply Continuous.log
    · exact continuous_const.max continuous_norm
    · intro z
      exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖z‖))
  have hball : IntegrableOn (fun z : ℂ => (Real.log (normPlus z)) ^ 2) B volume := by
    have hclosed : IntegrableOn (fun z : ℂ => (Real.log (normPlus z)) ^ 2)
        (closedBall (0 : ℂ) R) volume := by
      exact hcont.pow 2 |>.continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) R)
    exact hclosed.mono_set Metric.ball_subset_closedBall
  have hBlt : volume B < ⊤ := by
    dsimp [B]
    exact measure_ball_lt_top
  have : IsFiniteMeasure (volume.restrict B) :=
    (MeasureTheory.isFiniteMeasure_restrict).2 hBlt.ne
  have hprod : IntegrableOn (fun p : ℂ × ℂ => (Real.log (normPlus p.1)) ^ 2)
      (B ×ˢ B) μ := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hball.comp_fst (volume.restrict B)
  simpa [B, μ] using hprod

/-- The full pinned covariance kernel is square integrable on every bounded product box. -/
theorem integrable_gffKernel_sq_on_pair_ball (R : ℝ) :
    IntegrableOn (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let B : Set ℂ := ball 0 R
  let μ : Measure (ℂ × ℂ) := (volume : Measure ℂ).prod (volume : Measure ℂ)
  have hDiff := integrable_log_norm_sub_sq_on_pair_ball R
  have hPlus := integrable_log_normPlus_sq_on_pair_ball R
  have hPlusY : IntegrableOn (fun p : ℂ × ℂ => (Real.log (normPlus p.2)) ^ 2)
      (B ×ˢ B) μ := by
    simpa [B, μ, Function.comp_def, Prod.swap] using (integrable_log_normPlus_sq_on_pair_ball R).swap
  have hsum : IntegrableOn
      (fun p : ℂ × ℂ => 3 * ((Real.log ‖p.1 - p.2‖) ^ 2 +
        (Real.log (normPlus p.1)) ^ 2 + (Real.log (normPlus p.2)) ^ 2))
      (B ×ˢ B) μ := by
    change Integrable
      (fun p : ℂ × ℂ => 3 * ((Real.log ‖p.1 - p.2‖) ^ 2 +
        (Real.log (normPlus p.1)) ^ 2 + (Real.log (normPlus p.2)) ^ 2))
      (((volume : Measure ℂ).prod (volume : Measure ℂ)).restrict (B ×ˢ B))
    simpa [B, μ, add_assoc] using (hDiff.add (hPlus.add hPlusY)).const_mul 3
  have hmeas : AEStronglyMeasurable
      (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2) (μ.restrict (B ×ˢ B)) := by
    apply (show Measurable (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2) from ?_)
      |>.aestronglyMeasurable
    fun_prop [gffKernel, normPlus]
  have hkernel : IntegrableOn
      (fun p : ℂ × ℂ => (gffKernel p.1 p.2) ^ 2) (B ×ˢ B) μ := by
    rw [IntegrableOn]
    apply hsum.mono' hmeas
    filter_upwards with p
    let a : ℝ := -Real.log ‖p.1 - p.2‖
    let b : ℝ := Real.log (normPlus p.1)
    let c : ℝ := Real.log (normPlus p.2)
    have hkernelEq : gffKernel p.1 p.2 = a + b + c := by
      simp [a, b, c, gffKernel]
    have hsq : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
    calc
      ‖(gffKernel p.1 p.2) ^ 2‖ = (a + b + c) ^ 2 := by
        rw [hkernelEq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (a + b + c))]
      _ ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := hsq
      _ = 3 * ((Real.log ‖p.1 - p.2‖) ^ 2 +
          (Real.log (normPlus p.1)) ^ 2 + (Real.log (normPlus p.2)) ^ 2) := by
        simp [a, b, c]
  simpa [B, μ] using hkernel


end DOZZ

end
