/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarTaylorRemainder
public import DOZZ.Hypergeom.Planar.TaylorTail
public import DOZZ.Hypergeom.Planar.RadialCriteria
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact absolute-integrability criterion for the corrected Taylor kernel. -/

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology

namespace DOZZ.Proofs

private noncomputable def taylorQuarterTurnCircle : Circle :=
  ⟨Complex.I, by simp [Submonoid.unitSphere]⟩

private noncomputable def taylorQuarterTurn : ℂ ≃ₗᵢ[ℝ] ℂ :=
  rotation taylorQuarterTurnCircle

private noncomputable def taylorNeg : ℂ ≃ₗᵢ[ℝ] ℂ :=
  LinearIsometryEquiv.neg (R := ℝ)

private theorem taylorQuarterTurn_measurePreserving :
    MeasurePreserving taylorQuarterTurn volume volume :=
  LinearIsometryEquiv.measurePreserving taylorQuarterTurn

private theorem taylorNeg_measurePreserving :
    MeasurePreserving taylorNeg volume volume :=
  LinearIsometryEquiv.measurePreserving taylorNeg

private noncomputable def taylorNumerator (k : ℝ) (z u : ℂ) : ℝ :=
  ‖u - z‖ ^ k - ‖u‖ ^ k +
    (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re

private theorem taylorNumerator_pair (k : ℝ) (z u : ℂ) :
    taylorNumerator k z u + taylorNumerator k z (-u) =
      ‖u - z‖ ^ k + ‖u + z‖ ^ k - 2 * ‖u‖ ^ k := by
  have hshift : ‖-u - z‖ = ‖u + z‖ := by
    calc
      ‖-u - z‖ = ‖-(u + z)‖ := by congr 1; ring
      _ = ‖u + z‖ := norm_neg _
  have hlinear :
      (k / 2) * ‖u‖ ^ k * (z / u + star z / star u).re +
        (k / 2) * ‖u‖ ^ k * (z / -u + star z / star (-u)).re = 0 := by
    have hzdiv : z / -u = -(z / u) := by rw [div_neg]
    have hstardiv : star z / star (-u) = -(star z / star u) := by
      rw [star_neg, div_neg]
    rw [hzdiv, hstardiv]
    simp only [Complex.add_re, Complex.neg_re]
    ring
  unfold taylorNumerator
  rw [norm_neg, hshift]
  linear_combination hlinear

private theorem taylorNumerator_pair_abs_lower (k : ℝ) (hk : 0 < k)
    (z u : ℂ) (hz : z ≠ 0) (hu : ‖u‖ ≤ ‖z‖ / 4) :
    2 * ((3 * ‖z‖ / 4) ^ k - (‖z‖ / 4) ^ k) ≤
      |taylorNumerator k z u| + |taylorNumerator k z (-u)| := by
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have huNorm : 0 ≤ ‖u‖ := norm_nonneg u
  have hsmall : ‖u‖ ≤ ‖z‖ := by linarith only [hu, hzNorm]
  have hshift₁ : 3 * ‖z‖ / 4 ≤ ‖u - z‖ := by
    have h := norm_sub_norm_le z u
    rw [norm_sub_rev] at h
    linarith only [h, hu]
  have hshift₂ : 3 * ‖z‖ / 4 ≤ ‖u + z‖ := by
    have h := norm_sub_norm_le z (-u)
    rw [norm_neg] at h
    have hnorm : ‖z - -u‖ = ‖u + z‖ := by
      calc
        ‖z - -u‖ = ‖z + u‖ := by congr 1; ring
        _ = ‖u + z‖ := by rw [add_comm]
    rw [hnorm] at h
    linarith only [h, hu]
  have hbase₁ : 0 ≤ 3 * ‖z‖ / 4 := by positivity
  have hbase₂ : 0 ≤ ‖z‖ / 4 := by positivity
  have hbase_lt : ‖z‖ / 4 < 3 * ‖z‖ / 4 := by linarith only [hzNorm]
  have hpow₁ : (3 * ‖z‖ / 4) ^ k ≤ ‖u - z‖ ^ k :=
    Real.rpow_le_rpow hbase₁ hshift₁ hk.le
  have hpow₂ : (3 * ‖z‖ / 4) ^ k ≤ ‖u + z‖ ^ k :=
    Real.rpow_le_rpow hbase₁ hshift₂ hk.le
  have hpow₃ : ‖u‖ ^ k ≤ (‖z‖ / 4) ^ k :=
    Real.rpow_le_rpow huNorm hu hk.le
  have hpair := taylorNumerator_pair k z u
  have hpairLower :
      2 * ((3 * ‖z‖ / 4) ^ k - (‖z‖ / 4) ^ k) ≤
        taylorNumerator k z u + taylorNumerator k z (-u) := by
    rw [hpair]
    linarith only [hpow₁, hpow₂, hpow₃]
  calc
    2 * ((3 * ‖z‖ / 4) ^ k - (‖z‖ / 4) ^ k) ≤
        |taylorNumerator k z u + taylorNumerator k z (-u)| :=
      le_trans hpairLower (le_abs_self _)
    _ ≤ |taylorNumerator k z u| + |taylorNumerator k z (-u)| := abs_add_le _ _

private theorem taylor_norm_rpow_measurable (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) := by
  have hrepr : (fun u : ℂ => ‖u‖ ^ p) =
      fun u => if ‖u‖ = 0 then 0 ^ p else Real.exp (p * Real.log ‖u‖) := by
    funext u
    by_cases hu : ‖u‖ = 0
    · simp [hu]
    · rw [ite_eq_right hu,
        Real.rpow_def_of_pos (lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton 0) (by fun_prop)
  · exact measurable_const
  · fun_prop

private theorem taylorNumerator_linear (k : ℝ) (z u : ℂ) :
    taylorNumerator k z u =
      (‖u - z‖ ^ k - ‖u‖ ^ k) + k * ‖u‖ ^ k * (z / u).re := by
  unfold taylorNumerator
  have hstar : star z / star u = star (z / u) := by simp
  have hreal : (star z / star u).re = (z / u).re := by
    rw [hstar]
    rfl
  rw [Complex.add_re, hreal]
  ring

private def taylorLocalSector (z : ℂ) (δ : ℝ) : Set ℂ :=
  {u | ‖u‖ < δ ∧ ‖z / u‖ ^ 2 ≤ 2 * (z / u).re ^ 2}

private theorem taylorLocalSector_measurable (z : ℂ) (δ : ℝ) :
    MeasurableSet (taylorLocalSector z δ) := by
  have hnorm : Measurable (fun u : ℂ => ‖u‖) := by fun_prop
  have hleft : Measurable (fun u : ℂ => ‖z / u‖ ^ 2) := by fun_prop
  have hright : Measurable (fun u : ℂ => 2 * (z / u).re ^ 2) := by fun_prop
  exact (measurableSet_lt hnorm measurable_const).inter
    (measurableSet_le hleft hright)

private theorem taylor_local_sector_or_quarterTurn (z : ℂ) (δ : ℝ) {u : ℂ}
    (hu : u ≠ 0) (hδ : ‖u‖ < δ) :
    u ∈ taylorLocalSector z δ ∨
      u ∈ taylorQuarterTurn '' taylorLocalSector z δ := by
  let w : ℂ := z / u
  by_cases hsector : ‖w‖ ^ 2 ≤ 2 * w.re ^ 2
  · exact Or.inl ⟨hδ, by simpa [w] using hsector⟩
  · have hnorm : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp [Complex.normSq]
      ring
    have hIm : ‖w‖ ^ 2 ≤ 2 * w.im ^ 2 := by linarith only [not_le.mp hsector, hnorm]
    have hturn : taylorQuarterTurn.symm u = -Complex.I * u := by
      change (rotation taylorQuarterTurnCircle).symm u = _
      rw [rotation_symm, rotation_apply]
      rw [Circle.coe_inv_eq_conj]
      simp [taylorQuarterTurnCircle, Complex.conj_I]
    have hquot : z / (taylorQuarterTurn.symm u) = Complex.I * w := by
      rw [hturn]
      dsimp [w]
      field_simp [hu, Complex.I_ne_zero]
      ring_nf
      simp [Complex.I_sq]
    have hmem : taylorQuarterTurn.symm u ∈ taylorLocalSector z δ := by
      constructor
      · rw [hturn]
        simp [norm_neg]
        exact hδ
      · rw [hquot]
        simp [Complex.mul_re]
        exact hIm
    exact Or.inr ⟨taylorQuarterTurn.symm u, hmem, by simp⟩

private theorem taylor_local_exponent_gt_neg_two (k β : ℝ)
    (hk : 1 ≤ k) (z : ℂ) (hz : z ≠ 0)
    (hK : Integrable (DOZZ.planarTaylorRemainder k β z) volume) :
    β < 2 := by
  let A : ℝ := (3 * ‖z‖ / 4) ^ k - (‖z‖ / 4) ^ k
  let C : ℝ := 2 * A
  let δ : ℝ := ‖z‖ / 4
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hA : 0 < A := by
    dsimp [A]
    apply sub_pos.mpr
    apply Real.rpow_lt_rpow (by positivity) (by linarith only [hzNorm]) (by linarith only [hk])
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKneg : Integrable
      (fun u : ℂ => DOZZ.planarTaylorRemainder k β z (-u)) volume := by
    simpa [taylorNeg, Function.comp_def] using
      taylorNeg_measurePreserving.integrable_comp_of_integrable hK
  have hKpair : Integrable
      (fun u : ℂ => |DOZZ.planarTaylorRemainder k β z u| +
        |DOZZ.planarTaylorRemainder k β z (-u)|) volume := by
    exact hK.norm.add hKneg.norm
  have hmajor : IntegrableOn
      (fun u : ℂ => C⁻¹ * (|DOZZ.planarTaylorRemainder k β z u| +
        |DOZZ.planarTaylorRemainder k β z (-u)|)) (ball (0 : ℂ) δ) volume := by
    apply (integrableOn_univ.mpr (hKpair.const_mul C⁻¹)).mono_set
    exact Set.subset_univ _
  have hLocalRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ (-β))
      (ball (0 : ℂ) δ) volume := by
    apply hmajor.mono' (taylor_norm_rpow_measurable (-β)).aestronglyMeasurable
    have hzero : volume.restrict (ball (0 : ℂ) δ) {0} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton (0 : ℂ))]
      exact measure_mono_null Set.inter_subset_left (by simp)
    have huNe : ∀ᵐ u ∂volume.restrict (ball (0 : ℂ) δ), u ≠ 0 := by
      rw [ae_iff]
      simp [hzero]
    filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet, huNe]
      with u huBall huNe
    have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr huNe
    have huδ : ‖u‖ < δ := by
      simpa [Metric.mem_ball, dist_zero_right, Real.dist_eq] using huBall
    have hnum := taylorNumerator_pair_abs_lower k (lt_of_lt_of_le (by positivity) hk)
      z u hz (by dsimp [δ] at huδ ⊢; linarith)
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos huNorm β
    have hnumK₁ : |DOZZ.planarTaylorRemainder k β z u| =
        |taylorNumerator k z u| / ‖u‖ ^ β := by
      simp [DOZZ.planarTaylorRemainder, taylorNumerator, abs_div, abs_of_pos hden]
    have hnumK₂ : |DOZZ.planarTaylorRemainder k β z (-u)| =
        |taylorNumerator k z (-u)| / ‖u‖ ^ β := by
      simp [DOZZ.planarTaylorRemainder, taylorNumerator,
        abs_div, abs_of_pos hden]
    have hkernel : C * ‖u‖ ^ (-β) ≤
        |DOZZ.planarTaylorRemainder k β z u| +
          |DOZZ.planarTaylorRemainder k β z (-u)| := by
      have hrecip : ‖u‖ ^ (-β) = 1 / ‖u‖ ^ β := by
        rw [show -β = 0 - β by ring, Real.rpow_sub huNorm, Real.rpow_zero]
      rw [hnumK₁, hnumK₂]
      dsimp [C, A]
      calc
        2 * ((3 * ‖z‖ / 4) ^ k - (‖z‖ / 4) ^ k) * ‖u‖ ^ (-β) =
            (2 * ((3 * ‖z‖ / 4) ^ k - (‖z‖ / 4) ^ k)) / ‖u‖ ^ β := by
              rw [hrecip]
              ring
        _ ≤ (|taylorNumerator k z u| + |taylorNumerator k z (-u)|) /
            ‖u‖ ^ β := div_le_div_of_nonneg_right hnum hden.le
        _ = |taylorNumerator k z u| / ‖u‖ ^ β +
            |taylorNumerator k z (-u)| / ‖u‖ ^ β := by rw [add_div]
    have hpoint : ‖u‖ ^ (-β) ≤ C⁻¹ *
        (|DOZZ.planarTaylorRemainder k β z u| +
          |DOZZ.planarTaylorRemainder k β z (-u)|) := by
      have hdiv : ‖u‖ ^ (-β) ≤
          (|DOZZ.planarTaylorRemainder k β z u| +
            |DOZZ.planarTaylorRemainder k β z (-u)|) / C := by
        apply (le_div_iff₀ hC).2
        simpa [mul_comm] using hkernel
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) (-β))]
    exact hpoint
  have hexp := (integrableOn_norm_rpow_ball_iff (-β) δ hδ).1 hLocalRadial
  linarith

private theorem taylor_local_exponent_gt_k_minus_one (k β : ℝ)
    (hk : 0 < k) (hk₁ : k < 1) (z : ℂ) (hz : z ≠ 0)
    (hK : Integrable (DOZZ.planarTaylorRemainder k β z) volume) :
    β < k + 1 := by
  let B : ℝ := (2 * ‖z‖) ^ k + ‖z‖ ^ k
  let C : ℝ := k * ‖z‖ / 4
  let M : ℝ := B / C
  let p : ℝ := k - 1 - β
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have htrend : Tendsto (fun r : ℝ => r ^ (k - 1)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (by linarith)
  have hlarge : ∀ᶠ r : ℝ in 𝓝[>] 0, M < r ^ (k - 1) :=
    htrend.eventually (eventually_gt_atTop M)
  have hlarge' : ∀ᶠ r : ℝ in 𝓝 0, r ∈ Ioi 0 → M < r ^ (k - 1) :=
    eventually_nhdsWithin_iff.mp hlarge
  obtain ⟨δ₀, hδ₀, hδ₀ball⟩ := Metric.eventually_nhds_iff_ball.mp hlarge'
  let δ : ℝ := min δ₀ (‖z‖ / 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₀' : 0 < δ₀ := hδ₀
  have hδz : δ ≤ ‖z‖ / 2 := by dsimp [δ]; exact min_le_right _ _
  let S : Set ℂ := taylorLocalSector z δ
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    exact taylorLocalSector_measurable z δ
  have hKabs : Integrable (fun u : ℂ => |DOZZ.planarTaylorRemainder k β z u|) volume := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmajor : IntegrableOn (fun u : ℂ => C⁻¹ *
      |DOZZ.planarTaylorRemainder k β z u|) S volume := by
    apply (integrableOn_univ.mpr (hKabs.const_mul C⁻¹)).mono_set
    exact Set.subset_univ S
  have hSectorRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ p) S volume := by
    apply hmajor.mono' (taylor_norm_rpow_measurable p).aestronglyMeasurable
    have hzero : volume.restrict S {0} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton (0 : ℂ))]
      exact measure_mono_null Set.inter_subset_left (by simp)
    have huNe : ∀ᵐ u ∂volume.restrict S, u ≠ 0 := by
      rw [ae_iff]
      simp [hzero]
    filter_upwards [ae_restrict_mem hSmeas, huNe] with u hu huNe
    rcases hu with ⟨huδ, hsector⟩
    have hr : 0 < ‖u‖ := norm_pos_iff.mpr huNe
    have huδ₀ : dist ‖u‖ 0 < δ₀ := by
      have hnormlt : ‖u‖ < δ₀ := lt_of_lt_of_le huδ (le_trans (min_le_left _ _) le_rfl)
      simpa [Real.dist_eq, abs_of_pos (norm_pos_iff.mpr huNe)] using hnormlt
    have hpower : M < ‖u‖ ^ (k - 1) := hδ₀ball _ huδ₀ hr
    have hnormShift : ‖u - z‖ ≤ 2 * ‖z‖ := by
      calc
        ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ 2 * ‖z‖ := by linarith only [huδ, hδz, hzNorm]
    have hshiftPow : ‖u - z‖ ^ k ≤ (2 * ‖z‖) ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) hnormShift hk.le
    have huPow : ‖u‖ ^ k ≤ ‖z‖ ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) (by linarith only [huδ, hδz, hzNorm]) hk.le
    have hA : |‖u - z‖ ^ k - ‖u‖ ^ k| ≤ B := by
      calc
        abs (‖u - z‖ ^ k - ‖u‖ ^ k) ≤
          abs (‖u - z‖ ^ k) + abs (‖u‖ ^ k) := abs_sub _ _
        _ = ‖u - z‖ ^ k + ‖u‖ ^ k := by
          rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) k),
            abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) k)]
        _ ≤ B := by dsimp [B]; exact add_le_add hshiftPow huPow
    have hBpower : B < C * ‖u‖ ^ (k - 1) := by
      have htmp : B < ‖u‖ ^ (k - 1) * C := by
        apply (div_lt_iff₀ hC).1
        simpa [M] using hpower
      simpa [mul_comm] using htmp
    let w : ℂ := z / u
    have hw : ‖w‖ ^ 2 ≤ 2 * w.re ^ 2 := by simpa [w] using hsector
    have hnormw : ‖w‖ = ‖z‖ / ‖u‖ := by dsimp [w]; rw [norm_div]
    have hrealLower : ‖w‖ ≤ 2 * |w.re| := by
      have hsq : ‖w‖ ^ 2 ≤ 2 * |w.re| ^ 2 := by simpa [sq_abs] using hw
      by_contra h
      have hlt : 2 * |w.re| < ‖w‖ := lt_of_not_ge h
      have hsq' : (2 * |w.re|) ^ 2 < ‖w‖ ^ 2 :=
        (sq_lt_sq₀ (by positivity) (norm_nonneg w)).2 hlt
      linarith only [hsq, hsq', sq_nonneg |w.re|]
    have hrpow : ‖u‖ ^ (k - 1) = ‖u‖ ^ k / ‖u‖ := by
      simpa [Real.rpow_one] using (Real.rpow_sub hr k (1 : ℝ))
    have hcoef : C * ‖u‖ ^ (k - 1) =
        (k * ‖u‖ ^ k / 4) * ‖w‖ := by
      dsimp [C]
      rw [hnormw, hrpow]
      field_simp [ne_of_gt hr]
    have hcoefNonneg : 0 ≤ k * ‖u‖ ^ k / 4 := by positivity
    have hlinearLower : 2 * C * ‖u‖ ^ (k - 1) ≤
        |k * ‖u‖ ^ k * w.re| := by
      have hmult := mul_le_mul_of_nonneg_left hrealLower hcoefNonneg
      have hmulEq : (k * ‖u‖ ^ k / 4) * (2 * |w.re|) =
          (k * ‖u‖ ^ k / 2) * |w.re| := by ring
      have hmulAbs : |k * ‖u‖ ^ k * w.re| =
          k * ‖u‖ ^ k * |w.re| := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hk.le
          (Real.rpow_nonneg (norm_nonneg u) k))]
      calc
        2 * C * ‖u‖ ^ (k - 1) =
            2 * (C * ‖u‖ ^ (k - 1)) := by ring
        _ = 2 * ((k * ‖u‖ ^ k / 4) * ‖w‖) := by rw [hcoef]
        _ ≤ 2 * ((k * ‖u‖ ^ k / 4) * (2 * |w.re|)) :=
          mul_le_mul_of_nonneg_left hmult (by norm_num)
        _ = k * ‖u‖ ^ k * |w.re| := by rw [hmulEq]; ring
        _ = |k * ‖u‖ ^ k * w.re| := hmulAbs.symm
    have hlinear : taylorNumerator k z u =
        (‖u - z‖ ^ k - ‖u‖ ^ k) + k * ‖u‖ ^ k * w.re := by
      simpa [w] using taylorNumerator_linear k z u
    have htri : |k * ‖u‖ ^ k * w.re| ≤
        |taylorNumerator k z u| + |‖u - z‖ ^ k - ‖u‖ ^ k| := by
      calc
        |k * ‖u‖ ^ k * w.re| =
            |taylorNumerator k z u - (‖u - z‖ ^ k - ‖u‖ ^ k)| := by
              rw [hlinear]
              congr 1
              ring
        _ ≤ |taylorNumerator k z u| +
            |‖u - z‖ ^ k - ‖u‖ ^ k| := abs_sub _ _
    have hnumLower : C * ‖u‖ ^ (k - 1) ≤ |taylorNumerator k z u| := by
      linarith only [hlinearLower, htri, hA, hBpower]
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos hr β
    have hp : ‖u‖ ^ p = ‖u‖ ^ (k - 1) / ‖u‖ ^ β := by
      simpa [p] using (Real.rpow_sub hr (k - 1) β)
    have hkernel : C * ‖u‖ ^ p ≤
        |DOZZ.planarTaylorRemainder k β z u| := by
      change C * ‖u‖ ^ p ≤ |taylorNumerator k z u / ‖u‖ ^ β|
      rw [abs_div, abs_of_pos hden]
      calc
        C * ‖u‖ ^ p = (C * ‖u‖ ^ (k - 1)) / ‖u‖ ^ β := by rw [hp]; ring
        _ ≤ |taylorNumerator k z u| / ‖u‖ ^ β :=
          div_le_div_of_nonneg_right hnumLower hden.le
    have hpoint : ‖u‖ ^ p ≤ C⁻¹ *
        |DOZZ.planarTaylorRemainder k β z u| := by
      have hdiv : ‖u‖ ^ p ≤
          |DOZZ.planarTaylorRemainder k β z u| / C := by
        apply (le_div_iff₀ hC).2
        simpa [mul_comm] using hkernel
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) p)]
    exact hpoint
  have hSectorRot : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (taylorQuarterTurn '' S) volume := by
    apply (taylorQuarterTurn_measurePreserving.integrableOn_image
      taylorQuarterTurn.toHomeomorph.measurableEmbedding
      (f := fun u : ℂ => ‖u‖ ^ p) (s := S)).2
    simpa [Function.comp_def, taylorQuarterTurn] using hSectorRadial
  have hcover : ball (0 : ℂ) δ ⊆ (S ∪ taylorQuarterTurn '' S) ∪ {0} := by
    intro u hu
    have huδ : ‖u‖ < δ := by
      simpa [Metric.mem_ball, dist_zero_right] using hu
    by_cases hu0 : u = 0
    · exact Or.inr (by simp [hu0])
    · rcases taylor_local_sector_or_quarterTurn z δ hu0 huδ with hs | hs
      · exact Or.inl (Or.inl (by simpa [S] using hs))
      · exact Or.inl (Or.inr (by simpa [S] using hs))
  have hRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (ball (0 : ℂ) δ) volume := by
    have hsingle : IntegrableOn (fun u : ℂ => ‖u‖ ^ p) {0} volume := by
      exact integrableOn_singleton (by finiteness) (by simp)
    apply ((hSectorRadial.union hSectorRot).union hsingle).mono_set hcover
  have hexp := (integrableOn_norm_rpow_ball_iff p δ hδ).1 hRadial
  dsimp [p] at hexp
  linarith

private noncomputable def unitTaylorPathSq (w : ℂ) (t : ℝ) : ℝ :=
  1 - 2 * t * w.re + t ^ 2 * ‖w‖ ^ 2

private theorem unitTaylorPathSq_eq_normSq (w : ℂ) (t : ℝ) :
    unitTaylorPathSq w t = Complex.normSq (1 - (t : ℂ) * w) := by
  simp [unitTaylorPathSq, Complex.normSq, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im]
  have hn : w.re ^ 2 + w.im ^ 2 = ‖w‖ ^ 2 := by
    have h := Complex.normSq_eq_norm_sq w
    simp [Complex.normSq] at h
    rw [← h]; ring
  rw [← hn]; ring

private noncomputable def unitTaylorPath (k : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  unitTaylorPathSq w t ^ (k / 2)

private noncomputable def unitTaylorPathDeriv (k : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  k * unitTaylorPathSq w t ^ (k / 2 - 1) *
    (t * ‖w‖ ^ 2 - w.re)

private noncomputable def unitTaylorPathSecond (k : ℝ) (w : ℂ) (t : ℝ) : ℝ :=
  k * unitTaylorPathSq w t ^ (k / 2 - 2) *
    (unitTaylorPathSq w t * ‖w‖ ^ 2 +
      (k - 2) * (t * ‖w‖ ^ 2 - w.re) ^ 2)

private theorem unitTaylorPathSq_hasDerivAt (w : ℂ) (t : ℝ) :
    HasDerivAt (unitTaylorPathSq w) (2 * t * ‖w‖ ^ 2 - 2 * w.re) t := by
  change HasDerivAt (fun s : ℝ => 1 - 2 * s * w.re + s ^ 2 * ‖w‖ ^ 2) _ _
  convert (((hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul (2 * w.re))).add
      (((hasDerivAt_id t).pow 2).const_mul (‖w‖ ^ 2))) using 1
  · ext s
    simp
    ring
  · simp
    ring

private theorem unitTaylorPath_hasDerivAt (k : ℝ) (w : ℂ) (t : ℝ)
    (hq : 0 < unitTaylorPathSq w t) :
    HasDerivAt (unitTaylorPath k w)
      (unitTaylorPathDeriv k w t) t := by
  unfold unitTaylorPath
  change HasDerivAt ((fun x : ℝ => x ^ (k / 2)) ∘ unitTaylorPathSq w) _ _
  have hq' := unitTaylorPathSq_hasDerivAt w t
  have hp := (Real.hasDerivAt_rpow_const (x := unitTaylorPathSq w t)
    (p := k / 2) (Or.inl hq.ne')).comp t hq'
  convert hp using 1
  all_goals (simp [unitTaylorPathDeriv]; ring)

private theorem unitTaylorPathDeriv_hasDerivAt (k : ℝ) (w : ℂ) (t : ℝ)
    (hq : 0 < unitTaylorPathSq w t) :
    HasDerivAt (unitTaylorPathDeriv k w) (unitTaylorPathSecond k w t) t := by
  let q := unitTaylorPathSq w
  have hq' := unitTaylorPathSq_hasDerivAt w t
  have hp := (Real.hasDerivAt_rpow_const (x := q t)
    (p := k / 2 - 1) (Or.inl hq.ne')).comp t hq'
  have hv : HasDerivAt (fun s : ℝ => s * ‖w‖ ^ 2 - w.re)
      (‖w‖ ^ 2) t := by
    convert ((hasDerivAt_id t).const_mul (‖w‖ ^ 2)).sub_const w.re using 1
    · ext s
      simp
      ring
    · ring
  have h := (hp.mul hv).const_mul k
  have hqpos : 0 < q t := hq
  have hpow : q t ^ (k / 2 - 1) = q t ^ (k / 2 - 2) * q t := by
    rw [show k / 2 - 1 = (k / 2 - 2) + 1 by ring,
      Real.rpow_add hqpos, Real.rpow_one]
  have hvalue : k * ((k / 2 - 1) * q t ^ (k / 2 - 2) *
      (2 * t * ‖w‖ ^ 2 - 2 * w.re) * (t * ‖w‖ ^ 2 - w.re) +
        q t ^ (k / 2 - 1) * ‖w‖ ^ 2) = unitTaylorPathSecond k w t := by
    rw [hpow]
    dsimp [unitTaylorPathSecond]
    ring
  have h' : HasDerivAt (fun s : ℝ =>
      k * q s ^ (k / 2 - 1) * (s * ‖w‖ ^ 2 - w.re))
      (unitTaylorPathSecond k w t) t := by
    convert h using 1
    · ext s
      simp [Function.comp_def]
      ring
    · simpa only [Function.comp_apply,
        show k / 2 - 1 - 1 = k / 2 - 2 by ring] using hvalue.symm
  have hfun : unitTaylorPathDeriv k w = fun s : ℝ =>
      k * q s ^ (k / 2 - 1) * (s * ‖w‖ ^ 2 - w.re) := by
    funext s
    rfl
  rw [hfun]
  exact h'

private theorem unitTaylorPathSq_bounds (w : ℂ) (hw : ‖w‖ ≤ 1 / 8)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 / 2 : ℝ) ≤ unitTaylorPathSq w t ∧ unitTaylorPathSq w t ≤ 2 := by
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have htw : ‖(t : ℂ) * w‖ ≤ 1 / 8 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact (mul_le_mul_of_nonneg_left hw ht0).trans (by linarith only [ht1])
  have hlow : 7 / 8 ≤ ‖(1 : ℂ) - (t : ℂ) * w‖ := by
    have h := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * w)
    rw [norm_one] at h
    linarith only [h, htw]
  have hupp : ‖(1 : ℂ) - (t : ℂ) * w‖ ≤ 9 / 8 := by
    have h := norm_sub_le (1 : ℂ) ((t : ℂ) * w)
    rw [norm_one] at h
    linarith only [h, htw]
  rw [unitTaylorPathSq_eq_normSq, Complex.normSq_eq_norm_sq]
  have hlo2 := pow_le_pow_left₀ (by norm_num) hlow 2
  have hup2 := pow_le_pow_left₀ (norm_nonneg _) hupp 2
  exact ⟨by linarith only [hlo2], by linarith only [hup2]⟩

private theorem unitTaylorPath_iteratedDeriv_two (k : ℝ) (w : ℂ)
    (hw : ‖w‖ ≤ 1 / 8) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDeriv 2 (unitTaylorPath k w) t = unitTaylorPathSecond k w t := by
  have hbounds := unitTaylorPathSq_bounds w hw ht
  have hqpos : 0 < unitTaylorPathSq w t := lt_of_lt_of_le (by norm_num) hbounds.1
  have hEq : deriv (unitTaylorPath k w) =ᶠ[𝓝 t] unitTaylorPathDeriv k w := by
    have hcont : ContinuousAt (unitTaylorPathSq w) t := by
      change ContinuousAt (fun s : ℝ => 1 - 2 * s * w.re + s ^ 2 * ‖w‖ ^ 2) t
      fun_prop
    filter_upwards [hcont.eventually (isOpen_Ioi.mem_nhds hqpos)] with s hs
    exact (unitTaylorPath_hasDerivAt k w s hs).deriv
  have hsecond := unitTaylorPathDeriv_hasDerivAt k w t hqpos
  have hsecond' := hsecond.congr_of_eventuallyEq hEq
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hsecond'.deriv

private theorem unitTaylorPath_contDiffOn (k : ℝ) (w : ℂ)
    (hw : ‖w‖ ≤ 1 / 8) :
    ContDiffOn ℝ 2 (unitTaylorPath k w) (uIcc (0 : ℝ) 1) := by
  apply ContDiffOn.rpow_const_of_ne
  · change ContDiffOn ℝ 2
      (fun t : ℝ => 1 - 2 * t * w.re + t ^ 2 * ‖w‖ ^ 2) (uIcc (0 : ℝ) 1)
    fun_prop
  · intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa [uIcc] using ht
    have h := unitTaylorPathSq_bounds w hw ht'
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) h.1)

private theorem taylor_sector_coeff_lower (k ρ : ℝ) (hk : 0 < k)
    (_hk2 : k < 2) (hρ : 0 ≤ ρ) (hρsmall : 21 * ρ ≤ k)
    (hρsq : ρ ^ 2 ≤ ρ / 8) :
    k / 4 ≤ 1 - 2 * ρ + (k - 2) * (1 / 2 + (3 / 2) * ρ + ρ ^ 2) := by
  have hfirst : (5 - 3 * k / 2) * ρ ≤ 5 * ρ := by
    exact mul_le_mul_of_nonneg_right (by linarith) hρ
  have hsecond : (2 - k) * ρ ^ 2 ≤ ρ / 4 := by
    calc
      (2 - k) * ρ ^ 2 ≤ 2 * ρ ^ 2 := by
        exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg ρ)
      _ ≤ ρ / 4 := by linarith only [hρsq]
  have hident : 1 - 2 * ρ + (k - 2) *
      (1 / 2 + (3 / 2) * ρ + ρ ^ 2) =
      k / 2 - ((5 - 3 * k / 2) * ρ + (2 - k) * ρ ^ 2) := by ring
  rw [hident]
  linarith only [hfirst, hsecond, hρsmall]

private theorem taylor_path_bracket_lower (k ρ r q v : ℝ) (hk : 0 < k)
    (hρ : 0 ≤ ρ) (hρ8 : ρ ≤ 1 / 8) (hρ21 : 21 * ρ ≤ k)
    (hρsq : ρ ^ 2 ≤ ρ / 8) (hq : 1 - 2 * ρ ≤ q)
    (hv : v ^ 2 ≤ (1 / 2 + (3 / 2) * ρ + ρ ^ 2) * r ^ 2) :
    min (k / 4) (1 / 2 : ℝ) * r ^ 2 ≤ q * r ^ 2 + (k - 2) * v ^ 2 := by
  by_cases hk2 : k < 2
  · have hcoef := taylor_sector_coeff_lower k ρ hk hk2 hρ hρ21 hρsq
    have hmin : min (k / 4) (1 / 2 : ℝ) = k / 4 := by
      apply min_eq_left
      linarith
    rw [hmin]
    have hqmul : (1 - 2 * ρ) * r ^ 2 ≤ q * r ^ 2 :=
      mul_le_mul_of_nonneg_right hq (sq_nonneg r)
    have hvmul := mul_le_mul_of_nonpos_left hv (by linarith : k - 2 ≤ 0)
    calc
      (k / 4) * r ^ 2 ≤
          (1 - 2 * ρ + (k - 2) * (1 / 2 + (3 / 2) * ρ + ρ ^ 2)) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg r)
      _ = (1 - 2 * ρ) * r ^ 2 +
          (k - 2) * ((1 / 2 + (3 / 2) * ρ + ρ ^ 2) * r ^ 2) := by ring
      _ ≤ q * r ^ 2 + (k - 2) * v ^ 2 := by
        have hvmul' : (k - 2) *
            ((1 / 2 + (3 / 2) * ρ + ρ ^ 2) * r ^ 2) ≤
            (k - 2) * v ^ 2 := by exact hvmul
        exact add_le_add hqmul hvmul'
  · have hk2' : 2 ≤ k := le_of_not_gt hk2
    have hqhalf : 1 / 2 ≤ q := by linarith only [hq, hρ8]
    have hqmul : (1 / 2 : ℝ) * r ^ 2 ≤ q * r ^ 2 :=
      mul_le_mul_of_nonneg_right hqhalf (sq_nonneg r)
    have hmin : min (k / 4) (1 / 2 : ℝ) ≤ 1 / 2 := min_le_right _ _
    have hkn : 0 ≤ k - 2 := by linarith
    have hvnn : 0 ≤ v ^ 2 := sq_nonneg v
    calc
      min (k / 4) (1 / 2 : ℝ) * r ^ 2 ≤ (1 / 2 : ℝ) * r ^ 2 :=
        mul_le_mul_of_nonneg_right hmin (sq_nonneg r)
      _ ≤ q * r ^ 2 := hqmul
      _ ≤ q * r ^ 2 + (k - 2) * v ^ 2 := by
        exact le_add_of_nonneg_right (mul_nonneg hkn hvnn)

private theorem unitTaylorPath_second_pos (k : ℝ) (hk : 0 < k)
    (w : ℂ) (hw : ‖w‖ ≤ min (1 / 8) (k / 21))
    (hsector : 2 * w.re ^ 2 ≤ ‖w‖ ^ 2) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
      ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ)) * ‖w‖ ^ 2 ≤
      unitTaylorPathSecond k w t := by
  let ρ : ℝ := min (1 / 8) (k / 21)
  let q := unitTaylorPathSq w t
  let v := t * ‖w‖ ^ 2 - w.re
  have hρ0 : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 / 8 := by dsimp [ρ]; exact min_le_left _ _
  have hρ2 : ρ ≤ k / 21 := by dsimp [ρ]; exact min_le_right _ _
  have hwρ : ‖w‖ ≤ ρ := hw
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hs : 0 ≤ ‖w‖ := norm_nonneg w
  have hw8 : ‖w‖ ≤ 1 / 8 := le_trans hw (min_le_left _ _)
  have hq := unitTaylorPathSq_bounds w hw8 ht
  have hqlo : 1 - 2 * ρ ≤ q := by
    dsimp [q]
    have hformula := unitTaylorPathSq_eq_normSq w t
    rw [hformula, Complex.normSq_eq_norm_sq]
    have htw : ‖(t : ℂ) * w‖ ≤ ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      exact (mul_le_mul_of_nonneg_left hwρ ht0).trans (mul_le_of_le_one_left hρ0.le ht1)
    have hnorm : 1 - ρ ≤ ‖(1 : ℂ) - (t : ℂ) * w‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * w)
      rw [norm_one] at hh
      linarith
    have h2 := pow_le_pow_left₀ (by linarith only [hρ1]) hnorm 2
    linarith only [h2, sq_nonneg ρ]
  have hxabs : |w.re| ≤ (3 / 4 : ℝ) * ‖w‖ := by
    have hsq : 2 * |w.re| ^ 2 ≤ ‖w‖ ^ 2 := by
      simpa [sq_abs] using hsector
    have hnn : 0 ≤ ‖w‖ := norm_nonneg w
    have h2 : |w.re| ^ 2 ≤ ((3 / 4 : ℝ) * ‖w‖) ^ 2 := by
      linarith only [hsq, sq_nonneg ‖w‖]
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 h2
  have hvabs : |v| ≤ (3 / 4 : ℝ) * ‖w‖ + ‖w‖ ^ 2 := by
    dsimp [v]
    calc
      |t * ‖w‖ ^ 2 - w.re| ≤ |t * ‖w‖ ^ 2| + |w.re| := abs_sub _ _
      _ = t * ‖w‖ ^ 2 + |w.re| := by rw [abs_of_nonneg (mul_nonneg ht0 (sq_nonneg _))]
      _ ≤ (3 / 4 : ℝ) * ‖w‖ + ‖w‖ ^ 2 := by
        linarith only [hxabs, mul_le_of_le_one_left (sq_nonneg ‖w‖) ht1]
  have hρsq : ρ ^ 2 ≤ ρ / 8 := by
    linarith only [mul_le_mul_of_nonneg_left hρ1 hρ0.le]
  have hvSq : v ^ 2 ≤ (1 / 2 + (3 / 2) * ρ + ρ ^ 2) * ‖w‖ ^ 2 := by
    have hbase : v ^ 2 ≤ w.re ^ 2 + 2 * ‖w‖ ^ 2 * |w.re| + ‖w‖ ^ 4 := by
      have htSq : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
      have hr4nn : 0 ≤ ‖w‖ ^ 4 := by positivity
      have hquad : t ^ 2 * ‖w‖ ^ 4 ≤ ‖w‖ ^ 4 := by
        simpa using mul_le_mul_of_nonneg_right htSq hr4nn
      have hcross : -2 * t * ‖w‖ ^ 2 * w.re ≤
          2 * ‖w‖ ^ 2 * |w.re| := by
        have htx : -t * w.re ≤ |w.re| := by
          by_cases hx : 0 ≤ w.re
          · rw [abs_of_nonneg hx]
            linarith only [mul_nonneg ht0 hx, hx]
          · rw [abs_of_neg (lt_of_not_ge hx)]
            linarith only [mul_le_of_le_one_left (neg_nonneg.2 (lt_of_not_ge hx).le) ht1]
        linarith only [mul_le_mul_of_nonneg_right htx (sq_nonneg ‖w‖)]
      rw [show v ^ 2 =
          t ^ 2 * ‖w‖ ^ 4 - 2 * t * ‖w‖ ^ 2 * w.re + w.re ^ 2 by ring]
      linarith only [hcross, hquad]
    have hxSq : w.re ^ 2 ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by linarith only [hsector]
    have hr3 : ‖w‖ ^ 3 ≤ ρ * ‖w‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hwρ (sq_nonneg ‖w‖)
      linarith only [this]
    have hr4 : ‖w‖ ^ 4 ≤ ρ ^ 2 * ‖w‖ ^ 2 := by
      have hr2 : ‖w‖ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hs hwρ 2
      have := mul_le_mul_of_nonneg_right hr2 (sq_nonneg ‖w‖)
      linarith only [this]
    have hxTerm : 2 * ‖w‖ ^ 2 * |w.re| ≤
        (3 / 2 : ℝ) * ρ * ‖w‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hxabs (by positivity : 0 ≤ 2 * ‖w‖ ^ 2)
      linarith only [this, hr3]
    calc
      v ^ 2 ≤ w.re ^ 2 + 2 * ‖w‖ ^ 2 * |w.re| + ‖w‖ ^ 4 := hbase
      _ ≤ (1 / 2) * ‖w‖ ^ 2 + (3 / 2) * ρ * ‖w‖ ^ 2 + ρ ^ 2 * ‖w‖ ^ 2 := by
        exact add_le_add (add_le_add hxSq hxTerm) hr4
      _ = (1 / 2 + (3 / 2) * ρ + ρ ^ 2) * ‖w‖ ^ 2 := by ring
  have hA := taylor_path_bracket_lower k ρ ‖w‖ q v hk hρ0.le hρ1
    (by linarith only [hρ2]) hρsq hqlo hvSq
  have hp := unitTaylorPathSq_bounds w hw8 ht
  let e := k / 2 - 2
  have hpow : min ((1 / 2 : ℝ) ^ e) ((2 : ℝ) ^ e) ≤ q ^ e := by
    by_cases he : e ≤ 0
    · have hqpos : 0 < q := by dsimp [q]; linarith [hp.1]
      have h := Real.rpow_le_rpow_of_nonpos hqpos hp.2 he
      exact (min_le_right _ _).trans h
    · have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2) hp.1
        (le_of_not_ge he)
      exact (min_le_left _ _).trans h
  have hpowpos : 0 < min ((1 / 2 : ℝ) ^ e) ((2 : ℝ) ^ e) :=
    lt_min (Real.rpow_pos_of_pos (by norm_num) _) (Real.rpow_pos_of_pos (by norm_num) _)
  dsimp [unitTaylorPathSecond, q, v, e]
  have hfactor : 0 ≤ q ^ (k / 2 - 2) := Real.rpow_nonneg (by linarith [hq.1]) _
  have hbracket : 0 ≤ q * ‖w‖ ^ 2 + (k - 2) *
      (t * ‖w‖ ^ 2 - w.re) ^ 2 := by
    have hm : 0 ≤ min (k / 4) (1 / 2 : ℝ) := by positivity
    have hn : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
    exact (mul_nonneg hm hn).trans hA
  have hA' : min (k / 4) (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤
      q * ‖w‖ ^ 2 + (k - 2) * v ^ 2 := by
    exact hA
  have hprod : k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
      ((2 : ℝ) ^ (k / 2 - 2)) *
      (min (k / 4) (1 / 2 : ℝ) * ‖w‖ ^ 2) ≤
      k * q ^ (k / 2 - 2) *
        (q * ‖w‖ ^ 2 + (k - 2) * v ^ 2) := by
    have hm : 0 ≤ min (k / 4) (1 / 2 : ℝ) := by positivity
    have hc : 0 ≤ min (k / 4) (1 / 2 : ℝ) * ‖w‖ ^ 2 :=
      mul_nonneg hm (sq_nonneg ‖w‖)
    have hqpow : 0 ≤ q ^ (k / 2 - 2) := by positivity
    have hmul := mul_le_mul hpow hA' hc hqpow
    calc
      k * min ((1 / 2 : ℝ) ^ (k / 2 - 2)) ((2 : ℝ) ^ (k / 2 - 2)) *
          (min (k / 4) (1 / 2 : ℝ) * ‖w‖ ^ 2) =
          k * (min ((1 / 2 : ℝ) ^ (k / 2 - 2)) ((2 : ℝ) ^ (k / 2 - 2)) *
            (min (k / 4) (1 / 2 : ℝ) * ‖w‖ ^ 2)) := by ring
      _ ≤ k * (q ^ (k / 2 - 2) *
          (q * ‖w‖ ^ 2 + (k - 2) * v ^ 2)) :=
        mul_le_mul_of_nonneg_left hmul hk.le
      _ = k * q ^ (k / 2 - 2) *
          (q * ‖w‖ ^ 2 + (k - 2) * v ^ 2) := by ring
  have hhalf : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  simpa [unitTaylorPathSecond, q, v, hhalf, mul_assoc, mul_comm, mul_left_comm] using hprod

private theorem norm_rpow_eq_normSq_rpow (x : ℂ) (k : ℝ) :
    ‖x‖ ^ k = (‖x‖ ^ 2) ^ (k / 2) := by
  calc
    ‖x‖ ^ k = ‖x‖ ^ (2 * (k / 2)) := by congr 1; ring
    _ = (‖x‖ ^ 2) ^ (k / 2) :=
      Real.rpow_natCast_mul (norm_nonneg x) 2 (k / 2)

private theorem norm_unit_taylor_numerator_lower_of_sector (k : ℝ) (hk : 0 < k)
    (w : ℂ) (hw : ‖w‖ ≤ min (1 / 8) (k / 21))
    (hsector : 2 * w.re ^ 2 ≤ ‖w‖ ^ 2) :
    (k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
      ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2) *
        ‖w‖ ^ 2 ≤ |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re| := by
  let f : ℝ → ℝ := unitTaylorPath k w
  have hw8 : ‖w‖ ≤ 1 / 8 := le_trans hw (min_le_left _ _)
  have hcont := unitTaylorPath_contDiffOn k w hw8
  obtain ⟨t, ht, hTaylor⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x₀ := (0 : ℝ)) (x := 1) (by norm_num) hcont
  have htcc : t ∈ Icc (0 : ℝ) 1 := by
    rcases ht with ⟨ht0, ht1⟩
    have ht0' : 0 < t := by simpa using ht0
    have ht1' : t < 1 := by simpa using ht1
    exact ⟨le_of_lt ht0', le_of_lt ht1'⟩
  have hsecond := unitTaylorPath_iteratedDeriv_two k w hw8 htcc
  have hsecondLower := unitTaylorPath_second_pos k hk w hw hsector htcc
  have hf0 : f 0 = 1 := by simp [f, unitTaylorPath, unitTaylorPathSq]
  have hendpoint : f 1 = ‖(1 : ℂ) - w‖ ^ k := by
    dsimp [f, unitTaylorPath]
    rw [unitTaylorPathSq_eq_normSq, Complex.normSq_eq_norm_sq]
    simpa using (norm_rpow_eq_normSq_rpow (1 - w) k).symm
  have hqAt : ContDiffAt ℝ 2 (unitTaylorPathSq w) 0 := by
    change ContDiffAt ℝ 2
      (fun s : ℝ => 1 - 2 * s * w.re + s ^ 2 * ‖w‖ ^ 2) 0
    fun_prop
  have hfAt : ContDiffAt ℝ 2 f 0 := by
    change ContDiffAt ℝ 2 (fun s : ℝ => unitTaylorPathSq w s ^ (k / 2)) 0
    exact hqAt.rpow_const_of_ne (by simp [unitTaylorPathSq])
  have hfAt1 : ContDiffAt ℝ 1 f 0 := hfAt.of_le (by norm_num)
  have hwithin : iteratedDerivWithin 1 f (uIcc (0 : ℝ) 1) 0 = deriv f 0 := by
    calc
      iteratedDerivWithin 1 f (uIcc (0 : ℝ) 1) 0 = iteratedDeriv 1 f 0 :=
        iteratedDerivWithin_eq_iteratedDeriv (n := 1)
          (uniqueDiffOn_uIcc (by norm_num : (0 : ℝ) ≠ 1)) hfAt1 (by simp)
      _ = deriv f 0 := by simp [iteratedDeriv_succ, iteratedDeriv_zero]
  have hderiv0 : deriv f 0 = -k * w.re := by
    have h := unitTaylorPath_hasDerivAt k w 0 (by simp [unitTaylorPathSq])
    simpa [f, unitTaylorPathDeriv, unitTaylorPathSq] using h.deriv
  have hpoly : taylorWithinEval f 1 (uIcc (0 : ℝ) 1) 0 1 = 1 - k * w.re := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval, hwithin, hderiv0]
    simp [f, unitTaylorPath, unitTaylorPathSq]
    ring
  have hTaylor' : f 1 - taylorWithinEval f 1 (uIcc (0 : ℝ) 1) 0 1 =
      unitTaylorPathSecond k w t / 2 := by
    rw [hsecond] at hTaylor
    simpa using hTaylor
  have hvalue : ‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re =
      unitTaylorPathSecond k w t / 2 := by
    rw [hendpoint, hpoly] at hTaylor'
    linear_combination hTaylor'
  have hbound :
      (k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
        ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2) *
          ‖w‖ ^ 2 ≤ unitTaylorPathSecond k w t / 2 := by
    linarith only [hsecondLower]
  rw [hvalue]
  exact le_trans hbound (le_abs_self _)

private def taylorTailSector (z : ℂ) (R : ℝ) : Set ℂ :=
  {u | R ≤ ‖u‖ ∧ 2 * (z / u).re ^ 2 ≤ ‖z / u‖ ^ 2}

private theorem taylorTailSector_measurable (z : ℂ) (R : ℝ) :
    MeasurableSet (taylorTailSector z R) := by
  have hnorm : Measurable (fun u : ℂ => ‖u‖) := by fun_prop
  have hquot : Measurable (fun u : ℂ => z / u) := by fun_prop
  have hleft : Measurable (fun u : ℂ => 2 * (z / u).re ^ 2) := by fun_prop
  have hright : Measurable (fun u : ℂ => ‖z / u‖ ^ 2) := by fun_prop
  exact (measurableSet_le measurable_const hnorm).inter
    (measurableSet_le hleft hright)

private theorem norm_sq_eq_re_sq_add_im_sq (w : ℂ) :
    ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq]
  ring

private theorem taylor_sector_or_quarterTurn_sector (z : ℂ) (R : ℝ) {u : ℂ}
    (hu : u ≠ 0) (hR : R ≤ ‖u‖) :
    u ∈ taylorTailSector z R ∨
      u ∈ taylorQuarterTurn '' taylorTailSector z R := by
  let w : ℂ := z / u
  by_cases hsector : 2 * w.re ^ 2 ≤ ‖w‖ ^ 2
  · exact Or.inl ⟨hR, by simpa [w] using hsector⟩
  · have hnorm : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := norm_sq_eq_re_sq_add_im_sq w
    have hIm : 2 * w.im ^ 2 ≤ ‖w‖ ^ 2 := by linarith only [not_le.mp hsector, hnorm]
    have hturn : taylorQuarterTurn.symm u = -Complex.I * u := by
      change (rotation taylorQuarterTurnCircle).symm u = _
      rw [rotation_symm, rotation_apply]
      rw [Circle.coe_inv_eq_conj]
      simp [taylorQuarterTurnCircle, Complex.conj_I]
    have hquot : z / (taylorQuarterTurn.symm u) = Complex.I * w := by
      rw [hturn]
      dsimp [w]
      field_simp [hu, Complex.I_ne_zero]
      ring_nf
      simp [Complex.I_sq]
    have hmem : taylorQuarterTurn.symm u ∈ taylorTailSector z R := by
      constructor
      · rw [hturn]
        simp [norm_neg]
        exact hR
      · rw [hquot]
        simp [Complex.mul_re]
        exact hIm
    exact Or.inr ⟨taylorQuarterTurn.symm u, hmem, by simp⟩

private theorem rpow_tail_normalize (r s k β : ℝ) (hr : 0 < r) :
    r ^ k * (s / r) ^ 2 / r ^ β = s ^ 2 * r ^ (k - 2 - β) := by
  have hpow1 : r ^ k / r ^ 2 = r ^ (k - 2) := by
    simpa using (Real.rpow_sub hr k (2 : ℝ)).symm
  have hpow2 : r ^ (k - 2) / r ^ β = r ^ (k - 2 - β) :=
    (Real.rpow_sub hr (k - 2) β).symm
  calc
    _ = s ^ 2 * ((r ^ k / r ^ 2) / r ^ β) := by rw [div_pow]; ring
    _ = s ^ 2 * r ^ (k - 2 - β) := by rw [hpow1, hpow2]

private theorem abs_planarTaylorRemainder_lower_tail_sector (k β : ℝ)
    (hk : 0 < k) (z u : ℂ) (hu : u ≠ 0)
    (hw : ‖z / u‖ ≤ min (1 / 8) (k / 21))
    (hsector : 2 * (z / u).re ^ 2 ≤ ‖z / u‖ ^ 2) :
    (k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
      ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2) *
        ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) ≤
      |DOZZ.planarTaylorRemainder k β z u| := by
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let w : ℂ := z / u
  have hw' : ‖w‖ ≤ min (1 / 8) (k / 21) := by simpa [w] using hw
  have hsector' : 2 * w.re ^ 2 ≤ ‖w‖ ^ 2 := by simpa [w] using hsector
  have hunit := norm_unit_taylor_numerator_lower_of_sector k hk w hw' hsector'
  have hfactor : ‖u - z‖ ^ k = ‖u‖ ^ k * ‖(1 : ℂ) - w‖ ^ k := by
    have heq : u - z = u * ((1 : ℂ) - w) := by
      dsimp [w]
      field_simp [hu]
    rw [heq, norm_mul, Real.mul_rpow (norm_nonneg u) (norm_nonneg (1 - w))]
  have hstar : star z / star u = star w := by dsimp [w]; simp
  have hlinear : (z / u + star z / star u).re = 2 * w.re := by
    rw [hstar]
    simp [Complex.add_re]
    change (z / u).re + (z / u).re = 2 * (z / u).re
    ring
  have hnum : ‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
      (z / u + star z / star u).re =
      ‖u‖ ^ k * (‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re) := by
    rw [hfactor, hlinear]
    ring
  have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos hr β
  have hpow : ‖u‖ ^ k * (‖z‖ / ‖u‖) ^ 2 / ‖u‖ ^ β =
      ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) := rpow_tail_normalize ‖u‖ ‖z‖ k β hr
  change (k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
      ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2) *
        ‖z‖ ^ 2 * ‖u‖ ^ (k - 2 - β) ≤
      |(‖u - z‖ ^ k - ‖u‖ ^ k + (k / 2) * ‖u‖ ^ k *
        (z / u + star z / star u).re) / ‖u‖ ^ β|
  rw [hnum]
  have hrpow : 0 ≤ ‖u‖ ^ k := Real.rpow_nonneg (norm_nonneg u) k
  have hnormw : ‖w‖ = ‖z‖ / ‖u‖ := by dsimp [w]; rw [norm_div]
  rw [hnormw] at hunit
  calc
    _ = (k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
        ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2) *
          (‖u‖ ^ k * (‖z‖ / ‖u‖) ^ 2 / ‖u‖ ^ β) := by rw [hpow]; ring
    _ = (‖u‖ ^ k * ((k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
        ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2) *
          (‖z‖ / ‖u‖) ^ 2)) / ‖u‖ ^ β := by ring
    _ ≤ (‖u‖ ^ k * |‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re|) / ‖u‖ ^ β :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hunit hrpow) (Real.rpow_nonneg hr.le β)
    _ = |(‖u‖ ^ k * (‖(1 : ℂ) - w‖ ^ k - 1 + k * w.re)) /
          ‖u‖ ^ β| := by
      rw [abs_div, abs_of_pos hden, abs_mul, abs_of_nonneg hrpow]

private theorem planarTaylorRemainder_tail_exponent_lt (k β : ℝ)
    (hk : 0 < k) (z : ℂ) (hz : z ≠ 0)
    (hK : Integrable (DOZZ.planarTaylorRemainder k β z) volume) :
    k - 2 - β < -2 := by
  let ρ : ℝ := min (1 / 8) (k / 21)
  let R : ℝ := ‖z‖ / ρ
  let p : ℝ := k - 2 - β
  let c : ℝ := k * min ((1 / 2 : ℝ) ^ (k / 2 - 2))
    ((2 : ℝ) ^ (k / 2 - 2)) * min (k / 4) (1 / 2 : ℝ) / 2
  let C : ℝ := c * ‖z‖ ^ 2
  let S : Set ℂ := taylorTailSector z R
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hC : 0 < C := by
    dsimp [C, c]
    have hkpos : 0 < k := hk
    have he1 : 0 < (1 / 2 : ℝ) ^ (k / 2 - 2) := Real.rpow_pos_of_pos (by norm_num) _
    have he2 : 0 < (2 : ℝ) ^ (k / 2 - 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hmin : 0 < min (k / 4) (1 / 2 : ℝ) := lt_min (by linarith) (by norm_num)
    positivity
  have hSmeas : MeasurableSet S := by dsimp [S]; exact taylorTailSector_measurable z R
  have hKabs : Integrable (fun u : ℂ => |DOZZ.planarTaylorRemainder k β z u|) volume := by
    simpa only [Real.norm_eq_abs] using hK.norm
  have hmajor : IntegrableOn (fun u : ℂ => C⁻¹ *
      |DOZZ.planarTaylorRemainder k β z u|) S volume := by
    apply (integrableOn_univ.mpr (hKabs.const_mul C⁻¹)).mono_set
    exact Set.subset_univ S
  have hSectorRadial : IntegrableOn (fun u : ℂ => ‖u‖ ^ p) S volume := by
    apply hmajor.mono' (taylor_norm_rpow_measurable p).aestronglyMeasurable
    filter_upwards [ae_restrict_mem hSmeas] with u hu
    rcases hu with ⟨huR, hsector⟩
    have hu0 : u ≠ 0 := by
      intro hzero
      subst u
      have : R ≤ 0 := by simpa using huR
      linarith
    have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    have hsmall : ‖z / u‖ ≤ ρ := by
      rw [norm_div]
      apply (div_le_iff₀ huNorm).2
      have hmul : ‖z‖ ≤ ‖u‖ * ρ := by
        have hh := (div_le_iff₀ hρ).1 (by simpa [R] using huR)
        exact hh
      simpa [mul_comm] using hmul
    have hkernel := abs_planarTaylorRemainder_lower_tail_sector k β hk z u hu0
      (by simpa [ρ] using hsmall) hsector
    have hpoint : ‖u‖ ^ p ≤ C⁻¹ *
        |DOZZ.planarTaylorRemainder k β z u| := by
      calc
        ‖u‖ ^ p ≤ |DOZZ.planarTaylorRemainder k β z u| / C := by
          apply (le_div_iff₀ hC).2
          simpa [C, c, p, mul_assoc, mul_left_comm, mul_comm] using hkernel
        _ = C⁻¹ * |DOZZ.planarTaylorRemainder k β z u| := by
          rw [div_eq_mul_inv, mul_comm]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg u) p)]
    exact hpoint
  have hSectorRot : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (taylorQuarterTurn '' S) volume := by
    apply (taylorQuarterTurn_measurePreserving.integrableOn_image
      taylorQuarterTurn.toHomeomorph.measurableEmbedding
      (f := fun u : ℂ => ‖u‖ ^ p) (s := S)).2
    simpa [Function.comp_def, taylorQuarterTurn] using hSectorRadial
  have hcover : (Metric.ball (0 : ℂ) R)ᶜ ⊆ S ∪ taylorQuarterTurn '' S := by
    intro u hu
    have huR : R ≤ ‖u‖ := by
      by_contra h
      apply hu
      simpa [Metric.mem_ball, dist_zero_right] using lt_of_not_ge h
    have hu0 : u ≠ 0 := by
      intro hzero
      subst u
      exact (not_le_of_gt hR) (by simpa using huR)
    rcases taylor_sector_or_quarterTurn_sector z R hu0 huR with hs | hs
    · exact Or.inl (by simpa [S] using hs)
    · exact Or.inr (by simpa [S] using hs)
  have hExterior : IntegrableOn (fun u : ℂ => ‖u‖ ^ p)
      (Metric.ball (0 : ℂ) R)ᶜ volume := by
    apply (integrableOn_union.mpr ⟨hSectorRadial, hSectorRot⟩).mono_set hcover
  have hexp := (integrableOn_norm_rpow_ball_compl_iff p R hR).1 hExterior
  dsimp [p] at hexp
  exact hexp

/-- Exact absolute-integrability criterion for the corrected Taylor kernel. -/
theorem planar_taylor_integrable_iff (k β : ℝ) (hk : 0 < k)
    (z : ℂ) (hz : z ≠ 0) :
    Integrable (DOZZ.planarTaylorRemainder k β z) volume ↔
      k < β ∧ β < 2 ∧ β < k + 1 := by
  constructor
  · intro hK
    have htail := planarTaylorRemainder_tail_exponent_lt k β hk z hz hK
    have hkβ : k < β := by linarith
    by_cases hk₁ : 1 ≤ k
    · have hβ₂ := taylor_local_exponent_gt_neg_two k β hk₁ z hz hK
      have hβlin : β < k + 1 := by linarith
      exact ⟨hkβ, hβ₂, hβlin⟩
    · have hk₁' : k < 1 := lt_of_not_ge hk₁
      have hβlin := taylor_local_exponent_gt_k_minus_one k β hk hk₁' z hz hK
      have hβ₂ : β < 2 := by linarith
      exact ⟨hkβ, hβ₂, hβlin⟩
  · rintro ⟨hβ, hβ₂, hβlin⟩
    exact integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin z

end DOZZ.Proofs
