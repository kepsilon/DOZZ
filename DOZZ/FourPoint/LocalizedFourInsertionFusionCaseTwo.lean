/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.LocalizedFourInsertionFusionCaseOne
public import DOZZ.FourPoint.FusionPairKernel
public import DOZZ.FourPoint.FusionPairPowerAlgebra
public import DOZZ.FourPoint.FusionTruncatedMiddle

/-! The literal compact-uniform second four-insertion fusion estimate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem localized_four_insertion_fusion_case_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ R : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hR : 0 < R)
    (K : Set ℂ) (hK : IsCompact K)
    (A : Set (Fin 4 → ℝ)) (hA : IsCompact A)
    (S : Set ℝ) (hS : IsCompact S)
    (hcharges : ∀ α ∈ A, ∀ i : Fin 4, α i < Q γ)
    (horders : ∀ α ∈ A, ∀ q ∈ S,
      0 < q ∧ q ≥ fourFusionNu4 γ α / γ)
    (hcase : ∀ α ∈ A, ∀ q ∈ S,
      0 < fourFusionNu2 γ α ∧ 0 ≤ fourFusionNu3 γ α ∧
        α 2 ≤ 0 ∧ 0 ≤ α 2 + α 3)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ A, ∀ q ∈ S, ∀ y : Fin 4 → ℂ,
        (∀ i, y i ∈ K) → OrderedFourFusionCenters y →
        (∀ i j : Fin 4, i ≠ j → y i ≠ y j) →
        (∫⁻ ω, ENNReal.rpow (fourFusionMass γ (M ω) α y R) (-q) ∂P) ≤
          ENNReal.ofReal (C * (‖y 0 - y 1‖ / ‖y 0 - y 2‖) ^
                (fourFusionNu2 γ α ^ 2 / 2) *
            (‖y 0 - y 2‖ / ‖y 0 - y 3‖) ^
                ((fourFusionNu3 γ α ^ 2 - (α 2) ^ 2) / 2) *
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
  have hkB : 2 * B ≤ k * r₀ := by dsimp only [k]; field_simp; linarith only [hr₀]
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
  let E : ℝ := (2 * H) ^ 2 / 2
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨Cn, hCn, hn⟩ := fusion_retained_physical_bound P X hX γ hγ hγ₂ M hM
    B r₀ H hB.le hr₀ hr₀8 hHpos.le
  have hcase1 : ∀ α ∈ A, ∀ q ∈ S, 0 ≤ fourFusionNu3 γ α ∧ 0 ≤ α 3 := by
    intro α hα q hq
    obtain ⟨_, hν3, hα2, hα23⟩ := hcase α hα q hq
    exact ⟨hν3, by linarith only [hα2, hα23]⟩
  obtain ⟨C1, hC1, hcaseOne⟩ := localized_four_insertion_fusion_case_one P X M γ R hγ hγ₂ hR
    K hK A hA S hS hcharges horders hcase1 hX hM
  let C : ℝ := Cn * T ^ H * k ^ E * k ^ E + C1 * (100 * k) ^ E
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro α hα q hq y hy hord hne
  obtain ⟨hqpos, hbudget⟩ := horders α hα q hq
  obtain ⟨hν2, hν3, hα2, hα23⟩ := hcase α hα q hq
  have hα3 : 0 ≤ α 3 := by linarith only [hα2, hα23]
  have hν4 : 0 ≤ fourFusionNu4 γ α := by rw [four_fusion_nu4]; positivity
  have hqbound : q ≤ H := (le_abs_self q).trans (hqH q hq)
  have hchargesBound : ∀ i : Fin 4, |α i| ≤ H := hαH α hα
  have hνbound : fourFusionNu2 γ α ≤ 2 * H := by
    have h0 := (abs_le.mp (hchargesBound 0)).2
    have h1 := (abs_le.mp (hchargesBound 1)).2
    unfold fourFusionNu2
    linarith only [h0, h1, hQ]
  let e₂ : ℝ := fourFusionNu2 γ α ^ 2 / 2
  let e₃ : ℝ := (fourFusionNu3 γ α ^ 2 - (α 2) ^ 2) / 2
  let e₄ : ℝ := fourFusionNu4 γ α ^ 2 / 2
  have he₂ : 0 ≤ e₂ := by dsimp only [e₂]; positivity
  have he₄ : 0 ≤ e₄ := by dsimp only [e₄]; positivity
  have he₂E : e₂ ≤ E := by dsimp only [e₂, E]; linarith only [pow_le_pow_left₀ hν2.le hνbound 2]
  have hν32 : fourFusionNu3 γ α ≤ fourFusionNu2 γ α := by
    rw [four_fusion_nu3]; linarith only [hα2]
  have he₃lo : -E ≤ e₃ := by
    dsimp only [e₃]
    rw [← fusion_middle_exponent]
    dsimp only [e₂] at he₂E
    linarith only [he₂E, mul_nonneg hν2.le hν3]
  have he₃hi : e₃ ≤ E := by
    dsimp only [e₃]
    rw [← fusion_middle_exponent]
    dsimp only [e₂] at he₂E
    linarith only [he₂E, mul_le_mul_of_nonneg_left hν32 hν2.le]
  let r : ℝ := ‖y 0 - y 1‖
  let x : ℝ := ‖y 0 - y 2‖
  let u : ℝ := ‖y 0 - y 3‖
  let t : ℝ := min u r₀
  let v : ℝ := min x t
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr (hne 0 1 (by decide)))
  have hx : 0 < x := norm_pos_iff.mpr (sub_ne_zero.mpr (hne 0 2 (by decide)))
  have hu : 0 < u := norm_pos_iff.mpr (sub_ne_zero.mpr (hne 0 3 (by decide)))
  have ht : 0 < t := lt_min hu hr₀
  have hv : 0 < v := lt_min hx ht
  have htu : t ≤ u := min_le_left _ _
  have ht0 : t ≤ r₀ := min_le_right _ _
  have hvx : v ≤ x := min_le_left _ _
  have hvt : v ≤ t := min_le_right _ _
  have hradial := ordered_fusion_radial_bounds y hord
  have hrx : r ≤ x := hradial.1
  have hxu : x ≤ u := hradial.2.1
  have hroot := hradial.2.2
  have huB : u ≤ 2 * B := by
    have hh := norm_sub_le (y 0) (y 3)
    linarith only [hh, hnorm (y 0) (hy 0), hnorm (y 3) (hy 3)]
  have huk : u ≤ k * t := by
    rcases le_total u r₀ with hh | hh
    · dsimp only [t]; rw [min_eq_left hh]; exact le_mul_of_one_le_left hu.le hk
    · dsimp only [t]; rw [min_eq_right hh]; exact huB.trans hkB
  have hxkv : x ≤ k * v := by
    rcases le_total x t with hh | hh
    · dsimp only [v]; rw [min_eq_left hh]; exact le_mul_of_one_le_left hx.le hk
    · dsimp only [v]; rw [min_eq_right hh]; exact hxu.trans huk
  by_cases hsep : 100 * r ≤ v
  · have hrt : 100 * r ≤ t := hsep.trans hvt
    have hyouter : ∀ i : Fin 4, ‖y i - y 0‖ ≤ k * t := fun i => (hroot i).trans huk
    have hyfixed : ∀ i : Fin 4, ‖y i - y 0‖ ≤ 2 * B := fun i => (hroot i).trans huB
    obtain ⟨j, hj⟩ := four_root_guard_center y (y 0) t 4 ht
    obtain ⟨l, hl⟩ := four_root_guard_center y (y 0) r₀ 12 hr₀
    let I : Ω → ℝ≥0∞ := fun ω => fourFusionMass γ (M ω) α y R
    let wB : ℝ := (T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹
    let wD : ℝ := T⁻¹
    let wA : ℝ := (T * r ^ (γ * (α 0 + α 1)) * v ^ (γ * α 2) * t ^ (γ * α 3))⁻¹
    have hwA : 0 < wA := by dsimp only [wA]; positivity
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
    have hparts : ∀ i : Fin 4,
        (![r, r, v, t] i = r ∧ ‖y i - y 0‖ ≤ r) ∨
          (100 * r ≤ ![r, r, v, t] i ∧ ![r, r, v, t] i ≤ ‖y i - y 0‖ ∧
            ‖y i - y 0‖ ≤ k * ![r, r, v, t] i) := by
      intro i
      fin_cases i
      · exact Or.inl ⟨rfl, by change ‖y 0 - y 0‖ ≤ r; simpa only [sub_self, norm_zero] using hr.le⟩
      · exact Or.inl ⟨rfl, by change ‖y 1 - y 0‖ ≤ r; rw [norm_sub_rev (y 1)]⟩
      · change (v = r ∧ ‖y 2 - y 0‖ ≤ r) ∨
          (100 * r ≤ v ∧ v ≤ ‖y 2 - y 0‖ ∧ ‖y 2 - y 0‖ ≤ k * v)
        exact Or.inr ⟨hsep, by simpa only [norm_sub_rev (y 2)] using hvx,
          by simpa only [norm_sub_rev (y 2)] using hxkv⟩
      · change (t = r ∧ ‖y 3 - y 0‖ ≤ r) ∨
          (100 * r ≤ t ∧ t ≤ ‖y 3 - y 0‖ ∧ ‖y 3 - y 0‖ ≤ k * t)
        exact Or.inr ⟨hrt, by simpa only [norm_sub_rev (y 3)] using htu,
          by simpa only [norm_sub_rev (y 3)] using huk⟩
    have href : ∀ i : Fin 4, 0 < (![r, r, v, t] i) := by intro i; fin_cases i <;> assumption
    have hlA (ω : Ω) : ENNReal.ofReal wA * M ω
        (Metric.ball (y 0 + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) ≤ I ω := by
      have hh := fusion_inner_cluster_retained_kernel γ H R r k m hγ hr hm6 hm2k
        (by linarith only [hrt, ht0, hr₀R, hr₀]) α hchargesBound y ![r, r, v, t] href hparts (M ω)
      rw [fusion_pair_reference_product γ r v t hr α] at hh
      simpa only [mul_assoc, wA, T] using hh
    let a : ℝ := fourFusionNu2 γ α / γ
    let b : ℝ := (α 2 + α 3) / γ
    let s : ℝ := q - a - b
    have ha : 0 ≤ a := div_nonneg hν2.le hγ.le
    have hb : 0 ≤ b := div_nonneg hα23 hγ.le
    have hab : a + b = fourFusionNu4 γ α / γ := by
      dsimp only [a, b]
      rw [← add_div, four_fusion_nu4, four_fusion_nu3]
      congr 1
      ring
    have hs : 0 ≤ s := by dsimp only [s]; linarith only [hab, hbudget]
    have has : a + b + s = q := by dsimp only [s]; ring
    have haH : a ≤ H := by linarith only [has, hb, hs, hqbound]
    have hbH : b ≤ H := by linarith only [has, ha, hs, hqbound]
    have hsH : s ≤ H := by linarith only [has, ha, hb, hqbound]
    have hga : γ * a = fourFusionNu2 γ α := by dsimp only [a]; field_simp
    have hgb : γ * b = α 2 + α 3 := by dsimp only [b]; field_simp
    have hh := hn a b s ha haH hb hbH hs hsH (y 0) (hnorm _ (hy 0)) r t hr ht hrt ht0
      j l I wA wB wD hwA hwB hwD hlA hlB hlD
    rw [has] at hh
    have hp := fusion_case_two_weight_power γ T r v t a b s hT hr hv ht α hga hgb
    have heq : Cn * (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) *
        t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
        (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
        Cn * T ^ q * (r / v) ^ e₂ * (v / t) ^ e₃ * t ^ e₄ := by
      dsimp only [wA, wB, wD, e₂, e₃, e₄]
      calc
        _ = Cn * (((T * r ^ (γ * (α 0 + α 1)) * v ^ (γ * α 2) * t ^ (γ * α 3))⁻¹) ^ (-a) *
            ((T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) ^ (-b) * T⁻¹ ^ (-s) *
            t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
            (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by ring
        _ = _ := by rw [hp, has]; ring
    rw [heq] at hh
    have hpow := Real.rpow_le_rpow_of_exponent_le hT1 hqbound
    have hratio₂ := fusion_truncated_outer_power r v x k e₂ E 0 hr hv hvx hxkv hk he₂ he₂E (by norm_num)
    simp only [Real.rpow_zero, mul_one] at hratio₂
    have hratio₃ := fusion_middle_truncated_power x t u k e₃ E hx ht hxu htu huk hk he₃lo he₃hi
    have hscale := Real.rpow_le_rpow ht.le htu he₄
    have hprod := mul_le_mul
      (mul_le_mul
        (mul_le_mul (mul_le_mul_of_nonneg_left hpow hCn.le) hratio₂ (by positivity) (by positivity))
        hratio₃ (by positivity) (by positivity)) hscale (by positivity) (by positivity)
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    have hcoef : Cn * T ^ H * k ^ E * k ^ E ≤ C := le_add_of_nonneg_right (by positivity)
    have hprod' := hprod.trans (show
        (Cn * T ^ H * (k ^ E * (r / x) ^ e₂)) * (k ^ E * (x / u) ^ e₃) * u ^ e₄ ≤
          C * (r / x) ^ e₂ * (x / u) ^ e₃ * u ^ e₄ from by
        have hbnd := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef
            (Real.rpow_pos_of_pos (div_pos hr hx) e₂).le)
            (Real.rpow_pos_of_pos (div_pos hx hu) e₃).le) (Real.rpow_pos_of_pos hu e₄).le
        convert hbnd using 1
        ring)
    simpa only [I, r, x, u, e₂, e₃, e₄] using hprod'
  · have hx100 : x ≤ 100 * k * r := by
      have hh := mul_lt_mul_of_pos_left (show v < 100 * r by linarith only [hsep]) hk0
      linarith only [hxkv, hh]
    have hratio₂ : 1 / (100 * k) ≤ r / x := by
      apply (le_div_iff₀ hx).mpr
      rw [show (1 / (100 * k)) * x = x / (100 * k) by ring]
      exact (div_le_iff₀ (by positivity)).mpr (by linarith only [hx100])
    have hpRatio := fusion_ratio_power_lower (r / x) (100 * k) e₂ E
      (by linarith only [hk]) hratio₂ he₂ he₂E
    have hh := hcaseOne α hα q hq y hy hord hne
    have hratio₃1 : x / u ≤ 1 := (div_le_one₀ hu).mpr hxu
    have he₃full : e₃ ≤ fourFusionNu3 γ α ^ 2 / 2 := by dsimp only [e₃]; linarith only [sq_nonneg (α 2)]
    have hmiddle := Real.rpow_le_rpow_of_exponent_ge (div_pos hx hu) hratio₃1 he₃full
    have hbound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmiddle hC1.le)
      (Real.rpow_pos_of_pos hu e₄).le
    refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
    have halloc := mul_le_mul_of_nonneg_left hpRatio (hC1.le)
    simp only [mul_one, ← mul_assoc] at halloc
    have hcoef : C1 * (100 * k) ^ E ≤ C := le_add_of_nonneg_left (by positivity)
    have hfinal := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (halloc.trans (mul_le_mul_of_nonneg_right hcoef (Real.rpow_pos_of_pos (div_pos hr hx) e₂).le))
        (Real.rpow_pos_of_pos (div_pos hx hu) e₃).le) (Real.rpow_pos_of_pos hu e₄).le
    have htgt := hbound.trans (show C1 * (x / u) ^ e₃ * u ^ e₄ ≤
        C * (r / x) ^ e₂ * (x / u) ^ e₃ * u ^ e₄ from by simpa only [mul_assoc] using hfinal)
    simpa only [r, x, u, e₂, e₃, e₄] using htgt

end DOZZ.Proofs
