/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionRetainedEstimate
public import DOZZ.FourPoint.FusionSingleScaleEstimate
public import DOZZ.FourPoint.FusionRetainedKernels
public import DOZZ.FourPoint.FusionUniformPowers

/-! The literal compact-uniform first four-insertion fusion estimate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem localized_four_insertion_fusion_case_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ R : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hR : 0 < R)
    (K : Set ℂ) (hK : IsCompact K)
    (A : Set (Fin 4 → ℝ)) (hA : IsCompact A)
    (S : Set ℝ) (hS : IsCompact S)
    (hcharges : ∀ α ∈ A, ∀ i : Fin 4, α i < Q γ)
    (horders : ∀ α ∈ A, ∀ q ∈ S,
      0 < q ∧ q ≥ fourFusionNu4 γ α / γ)
    (hcase : ∀ α ∈ A, ∀ q ∈ S,
      0 ≤ fourFusionNu3 γ α ∧ 0 ≤ α 3)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ A, ∀ q ∈ S, ∀ y : Fin 4 → ℂ,
        (∀ i, y i ∈ K) → OrderedFourFusionCenters y →
        (∀ i j : Fin 4, i ≠ j → y i ≠ y j) →
        (∫⁻ ω, ENNReal.rpow (fourFusionMass γ (M ω) α y R) (-q) ∂P) ≤
          ENNReal.ofReal (C * (‖y 0 - y 2‖ / ‖y 0 - y 3‖) ^
                (fourFusionNu3 γ α ^ 2 / 2) *
              ‖y 0 - y 3‖ ^ (fourFusionNu4 γ α ^ 2 / 2)) := by
  have hQ : 0 < Q γ := by
    unfold Q
    exact add_pos (div_pos (by norm_num) hγ) (div_pos hγ (by norm_num))
  obtain ⟨BK, hBK⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let B : ℝ := max 1 BK
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hnorm : ∀ z ∈ K, ‖z‖ ≤ B := fun z hz => (hBK z hz).trans (le_max_right _ _)
  obtain ⟨H, hH, hαH, hqH⟩ := fusion_compact_parameter_bound A hA S hS
  have hHpos : 0 < H := zero_lt_one.trans_le hH
  let r₀ : ℝ := min (1 / 8) (R / 32)
  have hr₀ : 0 < r₀ := lt_min (by norm_num) (div_pos hR (by norm_num))
  have hr₀8 : r₀ ≤ 1 / 8 := min_le_left _ _
  have hr₀R : 13 * r₀ ≤ R := by have hh := min_le_right (1 / 8 : ℝ) (R / 32); linarith only [hh, hR]
  let k : ℝ := 1 + 2 * B / r₀
  have hk : 1 ≤ k := by dsimp only [k]; linarith only [div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hB) hr₀]
  have hk0 : 0 < k := zero_lt_one.trans_le hk
  have hkB : 2 * B ≤ k * r₀ := by dsimp only [k]; field_simp; nlinarith only [hr₀]
  let m : ℝ := 100 + 25 / r₀ + 13 * r₀ + 2 * B + 7 * k
  have hm100 : 100 ≤ m := by dsimp only [m]; linarith only [hr₀, hB, hk0, div_pos (by norm_num : (0 : ℝ) < 25) hr₀]
  have hm1 : 1 ≤ m := (by norm_num : (1 : ℝ) ≤ 100).trans hm100
  have hmpos : 0 < m := zero_lt_one.trans_le hm1
  have hm6 : 6 ≤ m := (by norm_num : (6 : ℝ) ≤ 100).trans hm100
  have hm25 : 25 ≤ m := (by norm_num : (25 : ℝ) ≤ 100).trans hm100
  have hmk : 5 + k ≤ m := by dsimp only [m]; linarith [div_pos (by norm_num : (0 : ℝ) < 25) hr₀]
  have hm2k : 2 * k ≤ m := by dsimp only [m]; linarith [div_pos (by norm_num : (0 : ℝ) < 25) hr₀]
  have hml : 25 ≤ m * r₀ := by
    have hh : 25 / r₀ ≤ m := by dsimp only [m]; linarith
    have hh' := mul_le_mul_of_nonneg_right hh hr₀.le
    rwa [div_mul_cancel₀ _ hr₀.ne'] at hh'
  have hmu : 13 * r₀ + 2 * B ≤ m := by dsimp only [m]; linarith [div_pos (by norm_num : (0 : ℝ) < 25) hr₀]
  let T : ℝ := (m ^ (γ * H)) ^ 4
  have hT : 0 < T := by dsimp only [T]; positivity
  have hT1 : 1 ≤ T := one_le_pow₀ (Real.one_le_rpow hm1 (mul_pos hγ hHpos).le)
  let E : ℝ := (3 * H) ^ 2 / 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨Cn, hCn, hn⟩ := fusion_retained_physical_bound P X hX γ hγ hγ₂ M hM
    B r₀ H hB.le hr₀ hr₀8 hHpos.le
  obtain ⟨Cs, hCs, hsingle⟩ := fusion_single_scale_physical_bound P X hX γ hγ hγ₂ M hM
    B r₀ H hB.le hr₀ hr₀8 hHpos.le
  let C₀ : ℝ := (Cn + Cs * (100 : ℝ) ^ E) * T ^ H
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  refine ⟨C₀ * k ^ E, by positivity, ?_⟩
  intro α hα q hq y hy hord hne
  have _hChargeDomain := hcharges α hα
  obtain ⟨hqpos, hbudget⟩ := horders α hα q hq
  obtain ⟨hν3, hα3⟩ := hcase α hα q hq
  have hν4 : 0 ≤ fourFusionNu4 γ α := by rw [four_fusion_nu4]; positivity
  have hqbound : q ≤ H := (le_abs_self q).trans (hqH q hq)
  have hchargesBound : ∀ i : Fin 4, |α i| ≤ H := hαH α hα
  have hνbound : fourFusionNu3 γ α ≤ 3 * H := by
    have h0 := (abs_le.mp (hchargesBound 0)).2
    have h1 := (abs_le.mp (hchargesBound 1)).2
    have h2 := (abs_le.mp (hchargesBound 2)).2
    unfold fourFusionNu3
    linarith only [h0, h1, h2, hQ]
  have he3 : fourFusionNu3 γ α ^ 2 / 2 ≤ E := by dsimp only [E]; nlinarith only [hν3, hνbound]
  let r : ℝ := ‖y 0 - y 2‖
  let u : ℝ := ‖y 0 - y 3‖
  let t : ℝ := min u r₀
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr (hne 0 2 (by decide)))
  have hu : 0 < u := norm_pos_iff.mpr (sub_ne_zero.mpr (hne 0 3 (by decide)))
  have ht : 0 < t := lt_min hu hr₀
  have htu : t ≤ u := min_le_left _ _
  have ht0 : t ≤ r₀ := min_le_right _ _
  have hroot := (ordered_fusion_radial_bounds y hord).2.2
  have huB : u ≤ 2 * B := by
    have hh := norm_sub_le (y 0) (y 3)
    linarith only [hh, hnorm (y 0) (hy 0), hnorm (y 3) (hy 3)]
  have huk : u ≤ k * t := by
    rcases le_total u r₀ with hh | hh
    · dsimp only [t]; rw [min_eq_left hh]; exact le_mul_of_one_le_left hu.le hk
    · dsimp only [t]; rw [min_eq_right hh]; exact huB.trans hkB
  have hyouter : ∀ i : Fin 4, ‖y i - y 0‖ ≤ k * t := fun i => (hroot i).trans huk
  have hyfixed : ∀ i : Fin 4, ‖y i - y 0‖ ≤ 2 * B := fun i => (hroot i).trans huB
  obtain ⟨j, hj⟩ := four_root_guard_center y (y 0) t 4 ht
  obtain ⟨l, hl⟩ := four_root_guard_center y (y 0) r₀ 12 hr₀
  let I : Ω → ℝ≥0∞ := fun ω => fourFusionMass γ (M ω) α y R
  let wB : ℝ := (T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹
  let wD : ℝ := T⁻¹
  have hwB : 0 < wB := by dsimp only [wB]; positivity
  have hwD : 0 < wD := inv_pos.mpr hT
  have hlB (ω : Ω) : ENNReal.ofReal wB * M ω
      (Metric.ball (y 0 + (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)) (t / 100)) ≤ I ω :=
    fusion_outer_retained_kernel γ H R t k m hγ ht hm1 hm25 hmk
      (by linarith only [ht0, hr₀R, hr₀]) α hchargesBound y hyouter j hj (M ω)
  have hlD (ω : Ω) : ENNReal.ofReal wD * M ω
      (Metric.ball (y 0 + (((12 + (l.val : ℝ) / 5) * r₀ : ℝ) : ℂ)) (r₀ / 100)) ≤ I ω :=
    fusion_fixed_retained_kernel γ H R r₀ (2 * B) m hγ hr₀ hm1 hml hmu hr₀R
      α hchargesBound y hyfixed l hl (M ω)
  have hlocal : (∫⁻ ω, I ω ^ (-q) ∂P) ≤
      ENNReal.ofReal (C₀ * (r / t) ^ (fourFusionNu3 γ α ^ 2 / 2) * t ^ (fourFusionNu4 γ α ^ 2 / 2)) := by
    by_cases hsep : 100 * r ≤ t
    · let a : ℝ := fourFusionNu3 γ α / γ
      let b : ℝ := α 3 / γ
      let s : ℝ := q - a - b
      have ha : 0 ≤ a := div_nonneg hν3 hγ.le
      have hb : 0 ≤ b := div_nonneg hα3 hγ.le
      have hab : a + b = fourFusionNu4 γ α / γ := by
        dsimp only [a, b]; rw [← add_div, four_fusion_nu4]
      have hs : 0 ≤ s := by dsimp only [s]; linarith only [hab, hbudget]
      have has : a + b + s = q := by dsimp only [s]; ring
      have haH : a ≤ H := by linarith only [has, hb, hs, hqbound]
      have hbH : b ≤ H := by linarith only [has, ha, hs, hqbound]
      have hsH : s ≤ H := by linarith only [has, ha, hb, hqbound]
      have hga : γ * a = fourFusionNu3 γ α := by dsimp only [a]; field_simp
      have hgb : γ * b = α 3 := by dsimp only [b]; field_simp
      let wA : ℝ := (T * r ^ (γ * (α 0 + α 1 + α 2)) * t ^ (γ * α 3))⁻¹
      have hwA : 0 < wA := by dsimp only [wA]; positivity
      have hyinner : ∀ i : Fin 3, ‖y i.castSucc - y 0‖ ≤ r := by
        intro i
        fin_cases i
        · change ‖y 0 - y 0‖ ≤ r; simpa only [sub_self, norm_zero] using hr.le
        · change ‖y 1 - y 0‖ ≤ r; rw [norm_sub_rev (y 1)]; exact hord.1
        · change ‖y 2 - y 0‖ ≤ r; rw [norm_sub_rev (y 2)]
      have hlA (ω : Ω) : ENNReal.ofReal wA * M ω
          (Metric.ball (y 0 + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) ≤ I ω :=
        fusion_inner_triple_retained_kernel γ H R r t k m hγ hr hsep hm6 hm2k
          (by linarith only [hsep, ht0, hr₀R, hr₀]) α hchargesBound y hyinner
          (by simpa only [norm_sub_rev (y 3)] using htu)
          (by simpa only [norm_sub_rev (y 3)] using huk) (M ω)
      have hh := hn a b s ha haH hb hbH hs hsH (y 0) (hnorm _ (hy 0)) r t hr ht hsep ht0
        j l I wA wB wD hwA hwB hwD hlA hlB hlD
      rw [has] at hh
      have hp := fusion_case_one_weight_power γ T r t a b s hT hr ht α hga hgb
      have heq : Cn * (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) *
          t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
          (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
          Cn * T ^ q * (r / t) ^ (fourFusionNu3 γ α ^ 2 / 2) * t ^ (fourFusionNu4 γ α ^ 2 / 2) := by
        dsimp only [wA, wB, wD]
        calc
          _ = Cn * (((T * r ^ (γ * (α 0 + α 1 + α 2)) * t ^ (γ * α 3))⁻¹) ^ (-a) *
              ((T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) ^ (-b) * T⁻¹ ^ (-s) *
              t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
              (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by ring
          _ = _ := by rw [hp, has]; ring
      rw [heq] at hh
      refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      dsimp only [C₀]
      have hpow := Real.rpow_le_rpow_of_exponent_le hT1 hqbound
      have hh' := mul_le_mul_of_nonneg_left hpow hCn.le
      have hcoef : Cn ≤ Cn + Cs * (100 : ℝ) ^ E := le_add_of_nonneg_right (by positivity)
      exact hh'.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos hT H).le)
    · let a : ℝ := fourFusionNu4 γ α / γ
      let s : ℝ := q - a
      have ha : 0 ≤ a := div_nonneg hν4 hγ.le
      have hs : 0 ≤ s := by dsimp only [s, a]; linarith only [hbudget]
      have has : a + s = q := by dsimp only [s]; ring
      have haH : a ≤ H := by linarith only [has, hs, hqbound]
      have hsH : s ≤ H := by linarith only [has, ha, hqbound]
      have hga : γ * a = fourFusionNu4 γ α := by dsimp only [a]; field_simp
      have hh := hsingle a s ha haH hs hsH (y 0) (hnorm _ (hy 0)) t ht ht0 j l I wB wD hwB hwD hlB hlD
      rw [has] at hh
      have hp := fusion_single_weight_power γ T t a s hT ht α hga
      have heq : Cs * (wB ^ (-a) * wD ^ (-s)) * t ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
          Cs * T ^ q * t ^ (fourFusionNu4 γ α ^ 2 / 2) := by
        dsimp only [wB, wD]
        calc
          _ = Cs * (((T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) ^ (-a) * T⁻¹ ^ (-s) *
              t ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by ring
          _ = _ := by rw [hp, has]; ring
      rw [heq] at hh
      have hratio : (1 / 100 : ℝ) ≤ r / t := (le_div_iff₀ ht).mpr (by linarith only [hsep])
      have hpRatio := fusion_ratio_power_lower (r / t) 100 (fourFusionNu3 γ α ^ 2 / 2) E
        (by norm_num) hratio (by positivity) he3
      refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hpow := Real.rpow_le_rpow_of_exponent_le hT1 hqbound
      have h1 := mul_le_mul_of_nonneg_left hpow hCs.le
      have h2 := mul_le_mul_of_nonneg_left hpRatio (mul_pos hCs (Real.rpow_pos_of_pos hT H)).le
      have h3 : Cs * T ^ H * ((100 : ℝ) ^ E * (r / t) ^ (fourFusionNu3 γ α ^ 2 / 2)) ≤
          C₀ * (r / t) ^ (fourFusionNu3 γ α ^ 2 / 2) := by
        dsimp only [C₀]
        have hcoef : Cs * (100 : ℝ) ^ E ≤ Cn + Cs * (100 : ℝ) ^ E := le_add_of_nonneg_left hCn.le
        have hh' := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos hT H).le)
          (Real.rpow_pos_of_pos (div_pos hr ht) (fourFusionNu3 γ α ^ 2 / 2)).le
        convert hh' using 1
        ring
      simp only [mul_one] at h2
      exact h1.trans (h2.trans h3)
  have hconvert := fusion_truncated_outer_power r t u k (fourFusionNu3 γ α ^ 2 / 2) E
    (fourFusionNu4 γ α ^ 2 / 2) hr ht htu huk hk (by positivity) he3 (by positivity)
  refine hlocal.trans (ENNReal.ofReal_le_ofReal ?_)
  have hh := mul_le_mul_of_nonneg_left hconvert hC₀.le
  simpa only [mul_assoc, I, r, u] using hh

end DOZZ.Proofs
