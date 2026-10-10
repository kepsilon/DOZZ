/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CoulombCutoffDefs
public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.Moments.InfinityChart

/-! # Pointwise bounds for the single-chart regularized Coulomb weight

Away from the origin both partition functions are at most one and add up to one, and the
inverted-chart weight at `x⁻¹` has a closed form in `x` with softened distances
`‖x - z k‖ + e^{-r} ‖x‖`. Near a root, in the bulk and in the exterior every base lies in a compact
subinterval of `(0, ∞)`, uniformly in the parameters, except the softened root factor; this gives
upper bounds in the three regions and a lower bound on a fixed exterior disk, with constants
depending only on the size of the parameters. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Partition functions -/

/-- Away from the origin both partition functions are at most one. -/
theorem partition_weights_le_one (partition : GMCChartPartition) {x : ℂ} (hx : x ≠ 0) :
    (partition.finiteWeight x : ℝ≥0∞) ≤ 1 ∧ (partition.infinityWeight x⁻¹ : ℝ≥0∞) ≤ 1 := by
  have h : (partition.finiteWeight x : ℝ≥0∞) + (partition.infinityWeight x⁻¹ : ℝ≥0∞) = 1 := by
    exact_mod_cast partition.sum_one x hx
  exact ⟨le_of_le_of_eq le_self_add h, le_of_le_of_eq le_add_self h⟩

/-- The single-chart weight is at most the sum of bounds for the two chart weights, each needed
only where the corresponding partition function does not vanish. -/
theorem coulombCutoffBound_weight_le (partition : GMCChartPartition) {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0) {A B : ℝ≥0∞}
    (hf : partition.finiteWeight x ≠ 0 → coulombCutoffFiniteWeight γ α z αinf r x ≤ A)
    (hi : partition.infinityWeight x⁻¹ ≠ 0 →
      coulombCutoffInfinityWeight γ α z αinf r x⁻¹ ≤ B) :
    coulombCutoffWeight partition γ α z αinf r x ≤ A + B := by
  obtain ⟨h1, h2⟩ := partition_weights_le_one partition hx
  unfold coulombCutoffWeight
  refine add_le_add ?_ ?_
  · by_cases h0 : partition.finiteWeight x = 0
    · rw [h0, ENNReal.coe_zero, zero_mul]
      exact zero_le
    · exact (mul_le_mul' h1 (hf h0)).trans_eq (one_mul _)
  · by_cases h0 : partition.infinityWeight x⁻¹ = 0
    · rw [h0, ENNReal.coe_zero, zero_mul]
      exact zero_le
    · exact (mul_le_mul' h2 (hi h0)).trans_eq (one_mul _)

/-- A common lower bound for both chart weights is a lower bound for the single-chart weight. -/
theorem coulombCutoffBound_le_weight (partition : GMCChartPartition) {N : ℕ} (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0) {c : ℝ≥0∞}
    (hf : c ≤ coulombCutoffFiniteWeight γ α z αinf r x)
    (hi : c ≤ coulombCutoffInfinityWeight γ α z αinf r x⁻¹) :
    c ≤ coulombCutoffWeight partition γ α z αinf r x := by
  have h : (partition.finiteWeight x : ℝ≥0∞) + (partition.infinityWeight x⁻¹ : ℝ≥0∞) = 1 := by
    exact_mod_cast partition.sum_one x hx
  calc c = ((partition.finiteWeight x : ℝ≥0∞) + (partition.infinityWeight x⁻¹ : ℝ≥0∞)) * c := by
        rw [h, one_mul]
    _ = (partition.finiteWeight x : ℝ≥0∞) * c + (partition.infinityWeight x⁻¹ : ℝ≥0∞) * c :=
        add_mul _ _ _
    _ ≤ _ := add_le_add (mul_le_mul' le_rfl hf) (mul_le_mul' le_rfl hi)

/-! ### The inverted-chart weight in the original variable -/

/-- The inverted-chart root base in the original variable. -/
theorem coulombCutoffBound_inv_root_base {x z : ℂ} {δ : ℝ} (hx : x ≠ 0) :
    normPlus x⁻¹ / (‖1 - z * x⁻¹‖ + δ) = normPlus x / (‖x - z‖ + δ * ‖x‖) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : ‖1 - z * x⁻¹‖ = ‖x - z‖ / ‖x‖ := by
    rw [← norm_div]
    congr 1
    field_simp
  rw [normPlus_inv_identity hx, h1, div_add' _ _ _ hn.ne', div_div_div_cancel_right₀ hn.ne']

/-- The inverted-chart base at infinity in the original variable. -/
theorem coulombCutoffBound_inv_infty_base {x : ℂ} {δ : ℝ} (hx : x ≠ 0) :
    normPlus x⁻¹ / (‖x⁻¹‖ + δ) = normPlus x / (1 + δ * ‖x‖) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have h1 : ‖x⁻¹‖ + δ = (1 + δ * ‖x‖) / ‖x‖ := by
    rw [norm_inv]
    field_simp
  rw [normPlus_inv_identity hx, h1, div_div_div_cancel_right₀ hn.ne']

/-- The inverted-chart weight at `x⁻¹` in the original variable `x`. -/
theorem coulombCutoffBound_infinityWeight_inv {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) {x : ℂ} (hx : x ≠ 0) :
    coulombCutoffInfinityWeight γ α z αinf r x⁻¹ =
      (∏ k, ENNReal.rpow
          (ENNReal.ofReal (normPlus x / (‖x - z k‖ + Real.exp (-r) * ‖x‖))) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x / (1 + Real.exp (-r) * ‖x‖))) (γ * αinf) := by
  unfold coulombCutoffInfinityWeight
  rw [coulombCutoffBound_inv_infty_base hx]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [coulombCutoffBound_inv_root_base hx]

/-! ### Products of powers with bounded bases and exponents -/

/-- A single power with base in `[L⁻¹, L]` and exponent of size at most `E`. -/
theorem coulombCutoffBound_rpow_le {L y e E : ℝ} (hL : 1 ≤ L) (hy1 : L⁻¹ ≤ y) (hy2 : y ≤ L)
    (he : |e| ≤ E) : ENNReal.rpow (ENNReal.ofReal y) e ≤ ENNReal.ofReal (L ^ E) :=
  (ennreal_rpow_ofReal_le_of_mem_Icc hL hy1 hy2 e).trans
    (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL he))

/-- A single power with base in `[L⁻¹, L]` and exponent of size at most `E`: lower bound. -/
theorem coulombCutoffBound_le_rpow {L y e E : ℝ} (hL : 1 ≤ L) (hy1 : L⁻¹ ≤ y) (hy2 : y ≤ L)
    (he : |e| ≤ E) : ENNReal.ofReal (L ^ (-E)) ≤ ENNReal.rpow (ENNReal.ofReal y) e :=
  (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg he))).trans
    (ennreal_ofReal_le_rpow_ofReal_of_mem_Icc hL hy1 hy2 e)

/-- A product over a subset of `Fin N` of powers with bases in `[L⁻¹, L]`. -/
theorem coulombCutoffBound_prod_le {N : ℕ} (s : Finset (Fin N)) (a e : Fin N → ℝ) {L E : ℝ}
    (hL : 1 ≤ L) (hE : 0 ≤ E) (h : ∀ j ∈ s, L⁻¹ ≤ a j ∧ a j ≤ L)
    (he : ∀ j ∈ s, |e j| ≤ E) :
    ∏ j ∈ s, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E)) := by
  refine (coulombWeight_prod_le s a e hL h).trans (ENNReal.ofReal_le_ofReal ?_)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  calc ∑ j ∈ s, |e j| ≤ ∑ j ∈ s, E := Finset.sum_le_sum he
    _ = s.card * E := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ N * E := by
      refine mul_le_mul_of_nonneg_right ?_ hE
      exact_mod_cast (Finset.card_le_univ s).trans_eq (Fintype.card_fin N)

/-- A product over `Fin N` of powers with bases in `[L⁻¹, L]`: lower bound. -/
theorem coulombCutoffBound_prod_ge {N : ℕ} (a e : Fin N → ℝ) {L E : ℝ} (hL : 1 ≤ L)
    (h : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (he : ∀ j, |e j| ≤ E) :
    ENNReal.ofReal (L ^ (-((N : ℝ) * E))) ≤
      ∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (coulombWeight_prod_ge Finset.univ a e hL fun j _ => h j)
  refine Real.rpow_le_rpow_of_exponent_le hL ?_
  rw [neg_le_neg_iff]
  calc ∑ j, |e j| ≤ ∑ _j : Fin N, E := Finset.sum_le_sum fun j _ => he j
    _ = N * E := by simp

/-- A product of bounded powers times the factor at infinity: upper bound. -/
theorem coulombCutoffBound_form_le {N : ℕ} (a e : Fin N → ℝ) (g eg : ℝ) {L E : ℝ} (hL : 1 ≤ L)
    (hE : 0 ≤ E) (ha : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L)
    (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) :
    (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E)) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  calc _ ≤ ENNReal.ofReal (L ^ ((N : ℝ) * E)) * ENNReal.ofReal (L ^ E) :=
        mul_le_mul' (coulombCutoffBound_prod_le Finset.univ a e hL hE (fun j _ => ha j)
          fun j _ => he j) (coulombCutoffBound_rpow_le hL hg.1 hg.2 heg)
    _ = _ := coulombWeight_ofReal_rpow_mul hLpos _ _

/-- A product of bounded powers times the factor at infinity: lower bound. -/
theorem coulombCutoffBound_form_ge {N : ℕ} (a e : Fin N → ℝ) (g eg : ℝ) {L E : ℝ} (hL : 1 ≤ L)
    (ha : ∀ j, L⁻¹ ≤ a j ∧ a j ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L)
    (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) :
    ENNReal.ofReal (L ^ (-((N : ℝ) * E + E))) ≤
      (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  calc ENNReal.ofReal (L ^ (-((N : ℝ) * E + E)))
      = ENNReal.ofReal (L ^ (-((N : ℝ) * E))) * ENNReal.ofReal (L ^ (-E)) := by
        rw [coulombWeight_ofReal_rpow_mul hLpos, neg_add]
    _ ≤ _ := mul_le_mul' (coulombCutoffBound_prod_ge a e hL ha he)
        (coulombCutoffBound_le_rpow hL hg.1 hg.2 heg)

/-- A product of bounded powers times the factor at infinity, with one root factor singled out:
the root factor contributes the softened root singularity. -/
theorem coulombCutoffBound_rootForm_le {N : ℕ} (a e : Fin N → ℝ) (c D g eg : ℝ) (k : Fin N)
    {L E : ℝ} (hL : 1 ≤ L) (hE : 0 ≤ E) (hD : 0 < D) (hak : a k = c / D)
    (hc : L⁻¹ ≤ c ∧ c ≤ L) (hg : L⁻¹ ≤ g ∧ g ≤ L)
    (ha : ∀ j, j ≠ k → L⁻¹ ≤ a j ∧ a j ≤ L) (he : ∀ j, |e j| ≤ E) (heg : |eg| ≤ E) :
    (∏ j, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) * ENNReal.rpow (ENNReal.ofReal g) eg ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) * ENNReal.rpow (ENNReal.ofReal D) (-e k) := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hcpos : 0 < c := lt_of_lt_of_le (inv_pos.mpr hLpos) hc.1
  have hP : ∏ j ∈ Finset.univ.erase k, ENNReal.rpow (ENNReal.ofReal (a j)) (e j) ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E)) :=
    coulombCutoffBound_prod_le _ a e hL hE
      (fun j hj => ha j (Finset.ne_of_mem_erase hj)) fun j _ => he j
  have hC := coulombCutoffBound_rpow_le hL hc.1 hc.2 (he k)
  have hG := coulombCutoffBound_rpow_le hL hg.1 hg.2 heg
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k), hak,
    coulombWeight_rpow_ofReal_div hcpos hD]
  generalize ENNReal.rpow (ENNReal.ofReal D) (-e k) = R
  calc _ = (ENNReal.rpow (ENNReal.ofReal c) (e k) *
          (∏ j ∈ Finset.univ.erase k, ENNReal.rpow (ENNReal.ofReal (a j)) (e j)) *
            ENNReal.rpow (ENNReal.ofReal g) eg) * R := by ring
    _ ≤ (ENNReal.ofReal (L ^ E) * ENNReal.ofReal (L ^ ((N : ℝ) * E)) *
          ENNReal.ofReal (L ^ E)) * R := by gcongr
    _ = (ENNReal.ofReal (L ^ ((N : ℝ) * E)) * ENNReal.ofReal (L ^ E) *
          ENNReal.ofReal (L ^ E)) * R := by rw [mul_comm (ENNReal.ofReal (L ^ E))]
    _ = _ := by rw [coulombWeight_ofReal_rpow_mul hLpos, coulombWeight_ofReal_rpow_mul hLpos]

/-! ### Elementary real inequalities -/

/-- The softening `e^{-r}` for `r ≥ 0` lies in `(0, 1]`. -/
theorem coulombCutoffBound_exp_neg_mem {r : ℝ} (hr : 0 ≤ r) :
    0 < Real.exp (-r) ∧ Real.exp (-r) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)⟩

/-- Each root has norm at most the sum of the norms. -/
theorem coulombCutoffBound_norm_le {N : ℕ} {z : Fin N → ℂ} {Zs : ℝ} (hz : ∑ j, ‖z j‖ ≤ Zs)
    (j : Fin N) : ‖z j‖ ≤ Zs :=
  (Finset.single_le_sum (f := fun i => ‖z i‖) (fun i _ => norm_nonneg (z i))
    (Finset.mem_univ j)).trans hz

/-- A point near the root `z k` is at distance between `ρs` and `2 Zs + 1` from every other
root. -/
theorem coulombCutoffBound_root_dist {Zs ρs : ℝ} {x zj zk : ℂ} (hzj : ‖zj‖ ≤ Zs)
    (hsep : 2 * ρs ≤ ‖zj - zk‖) (hd : ‖x - zk‖ < ρs) (hzk : ‖zk‖ ≤ Zs) (hρs1 : ρs ≤ 1) :
    ρs ≤ ‖x - zj‖ ∧ ‖x - zj‖ ≤ 2 * Zs + 1 := by
  have h1 := norm_sub_le_norm_sub_add_norm_sub zj x zk
  rw [norm_sub_rev zj x] at h1
  have h2 := norm_sub_le x zj
  have h3 := norm_sub_norm_le x zk
  constructor <;> linarith only [h1, h2, h3, hsep, hd, hzj, hzk, hρs1]

/-- The root factor: the power of the softened distance is the singular power. -/
theorem coulombCutoffBound_root_rpow {D : ℝ} (hD : 0 < D) (γ a : ℝ) :
    ENNReal.rpow (ENNReal.ofReal D) (-(γ * a)) = ENNReal.ofReal (D ^ (-γ * a)) := by
  rw [coulombWeight_rpow_ofReal hD, neg_mul]

/-- A point `y ≥ 1` below `L ≥ 1` lies in `[L⁻¹, L]`. -/
theorem coulombCutoffBound_mem_of_one_le {L y : ℝ} (hL : 1 ≤ L) (hy1 : 1 ≤ y) (hyL : y ≤ L) :
    L⁻¹ ≤ y ∧ y ≤ L :=
  ⟨(inv_le_one_of_one_le₀ hL).trans hy1, hyL⟩

/-- Enlarging `L` enlarges the interval `[L⁻¹, L]`. -/
theorem coulombCutoffBound_mem_mono {L L' y : ℝ} (hL : 0 < L) (hLL' : L ≤ L')
    (h : L⁻¹ ≤ y ∧ y ≤ L) : L'⁻¹ ≤ y ∧ y ≤ L' :=
  ⟨(inv_anti₀ hL hLL').trans h.1, h.2.trans hLL'⟩

/-- The base at infinity of the inverted chart lies between `1/2` and `normPlus`. -/
theorem coulombCutoffBound_infty_base_mem {t m δ : ℝ} (hm1 : 1 ≤ m) (htm : t ≤ m) (ht0 : 0 ≤ t)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (2 : ℝ)⁻¹ ≤ m / (1 + δ * t) ∧ m / (1 + δ * t) ≤ m := by
  have hδt : δ * t ≤ t := mul_le_of_le_one_left ht0 hδ1
  have hδt0 : 0 ≤ δ * t := mul_nonneg hδ.le ht0
  have hpos : 0 < 1 + δ * t := by linarith only [hδt0]
  constructor
  · rw [le_div_iff₀ hpos]
    linarith only [hδt, htm, hm1]
  · rw [div_le_iff₀ hpos]
    linarith only [mul_nonneg (by linarith only [hm1] : 0 ≤ m) hδt0]

/-- Rewriting a quotient with a free common factor. -/
theorem coulombCutoffBound_div_eq {m a b : ℝ} (hb : b ≠ 0) : m / a = m * b / a / b := by
  rw [div_div, mul_div_mul_right _ _ hb]

/-- The numerator constant of the root factor in the inverted chart. -/
theorem coulombCutoffBound_root_numer {m t d δ M Ri : ℝ} (hm1 : 1 ≤ m) (htm : t ≤ m)
    (hmM : m ≤ M) (hd : 0 ≤ d) (hδ : 0 < δ) (hRi : 1 ≤ Ri) (ht : Ri⁻¹ ≤ t) :
    1 ≤ m * (d + δ) / (d + δ * t) ∧ m * (d + δ) / (d + δ * t) ≤ M * Ri := by
  have hRipos : 0 < Ri := lt_of_lt_of_le one_pos hRi
  have ht0 : 0 < t := lt_of_lt_of_le (inv_pos.mpr hRipos) ht
  have hpos : 0 < d + δ * t := by linarith only [hd, mul_pos hδ ht0]
  have hRit : 1 ≤ Ri * t := by
    calc (1 : ℝ) = Ri * Ri⁻¹ := (mul_inv_cancel₀ hRipos.ne').symm
      _ ≤ Ri * t := mul_le_mul_of_nonneg_left ht hRipos.le
  have hM0 : 0 ≤ M := by linarith only [hm1, hmM]
  constructor
  · rw [le_div_iff₀ hpos]
    linarith only [mul_nonneg hd (sub_nonneg.2 hm1), mul_nonneg hδ.le (sub_nonneg.2 htm)]
  · rw [div_le_iff₀ hpos]
    have h1 : d + δ ≤ Ri * (d + δ * t) := by
      linarith only [mul_nonneg hd (sub_nonneg.2 hRi), mul_nonneg hδ.le (sub_nonneg.2 hRit)]
    calc m * (d + δ) ≤ M * (d + δ) := mul_le_mul_of_nonneg_right hmM (by linarith only [hd, hδ])
      _ ≤ M * (Ri * (d + δ * t)) := mul_le_mul_of_nonneg_left h1 hM0
      _ = M * Ri * (d + δ * t) := by ring

/-- Quotient bounds for the exterior: `t` against a point within `Zs` of `t` and `2 t + Zs`. -/
theorem coulombCutoffBound_ext_quot {t v Zs : ℝ} (ht : 2 * Zs ≤ t) (ht0 : 0 < t)
    (hv1 : t - Zs ≤ v) (hv2 : v ≤ 2 * t + Zs) :
    (5 / 2 : ℝ)⁻¹ ≤ t / v ∧ t / v ≤ 5 / 2 := by
  have hv : 0 < v := by linarith only [hv1, ht, ht0]
  constructor
  · rw [le_div_iff₀ hv, show (5 / 2 : ℝ)⁻¹ = 2 / 5 by norm_num]
    linarith only [hv2, ht]
  · rw [div_le_iff₀ hv]
    linarith only [hv1, ht, ht0]

/-- The factor at infinity of the inverted chart in the exterior. -/
theorem coulombCutoffBound_exterior_last {t δ e E : ℝ} (ht : 1 ≤ t) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (he : |e| ≤ E) :
    ENNReal.rpow (ENNReal.ofReal (t / (1 + δ * t))) e ≤
      ENNReal.ofReal (2 ^ E) * ENNReal.ofReal (t ^ max e 0) := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht
  obtain ⟨hy1, hy2⟩ := coulombCutoffBound_infty_base_mem (m := t) ht le_rfl ht0.le hδ hδ1
  have hy0 : 0 < t / (1 + δ * t) :=
    lt_of_lt_of_le (inv_pos.mpr two_pos) hy1
  have hE0 : 0 ≤ E := (abs_nonneg e).trans he
  have h2E : 1 ≤ (2 : ℝ) ^ E := Real.one_le_rpow one_le_two hE0
  rw [coulombWeight_rpow_ofReal hy0, ← ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two E)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases le_total 0 e with he0 | he0
  · rw [max_eq_left he0]
    calc (t / (1 + δ * t)) ^ e ≤ t ^ e := Real.rpow_le_rpow hy0.le hy2 he0
      _ = 1 * t ^ e := (one_mul _).symm
      _ ≤ 2 ^ E * t ^ e := mul_le_mul_of_nonneg_right h2E (Real.rpow_nonneg ht0.le e)
  · rw [max_eq_right he0, Real.rpow_zero, mul_one]
    calc (t / (1 + δ * t)) ^ e ≤ ((2 : ℝ)⁻¹) ^ e :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hy1 he0
      _ = 2 ^ (-e) := by rw [Real.inv_rpow zero_le_two, Real.rpow_neg zero_le_two]
      _ ≤ 2 ^ E := Real.rpow_le_rpow_of_exponent_le one_le_two
          ((neg_le_abs e).trans he)

/-! ### Near a finite root -/

/-- The scale `L` used near a finite root. -/
theorem coulombCutoffBound_root_const {Zs ρs Ri : ℝ} (hZs : 0 ≤ Zs) (hρs : 0 < ρs)
    (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri) :
    ∃ L : ℝ, Zs + 1 ≤ L * ρs ∧ 3 * Zs + 3 ≤ L ∧ (Zs + 1) * Ri ≤ L := by
  refine ⟨(3 * Zs + 3) * Ri / ρs, ?_, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ hρs.ne']
    linarith only [mul_nonneg hZs (sub_nonneg.2 hRi), hZs, hRi]
  · rw [le_div_iff₀ hρs]
    linarith only [mul_nonneg (by linarith only [hZs] : 0 ≤ 3 * Zs + 3) (sub_nonneg.2 hRi),
      mul_nonneg (by linarith only [hZs] : 0 ≤ 3 * Zs + 3) (sub_nonneg.2 hρs1)]
  · rw [le_div_iff₀ hρs]
    have hZ1 : 0 ≤ Zs + 1 := by linarith only [hZs]
    have hRi0 : 0 ≤ Ri := by linarith only [hRi]
    linarith only [mul_nonneg hZ1 hRi0, mul_nonneg (mul_nonneg hZ1 hRi0) (sub_nonneg.2 hρs1)]

/-- The finite-chart weight near a root. -/
theorem coulombCutoffBound_finite_root {N : ℕ} {Zs E ρs L : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hLρ : Zs + 1 ≤ L * ρs) (hL2 : 2 * Zs + 2 ≤ L)
    {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {k : Fin N} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hsep : ∀ j, j ≠ k → 2 * ρs ≤ ‖z j - z k‖) (hx : x ∈ Metric.ball (z k) ρs) :
    coulombCutoffFiniteWeight γ α z αinf r x ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) *
        ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) := by
  have hzj := coulombCutoffBound_norm_le hz
  have hd : ‖x - z k‖ < ρs := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have ht : ‖x‖ ≤ Zs + 1 := by
    have h1 := norm_sub_norm_le x (z k)
    linarith only [h1, hd, hρs1, hzj k]
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have hmM : normPlus x ≤ Zs + 1 := max_le (by linarith only [hZs]) ht
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hL1 : 1 ≤ L := by linarith only [hL2, hZs]
  have hDk : 0 < ‖x - z k‖ + Real.exp (-r) := by positivity
  have ha : ∀ j, j ≠ k → L⁻¹ ≤ normPlus x / (‖x - z j‖ + Real.exp (-r)) ∧
      normPlus x / (‖x - z j‖ + Real.exp (-r)) ≤ L := by
    intro j hj
    obtain ⟨h1, h3⟩ := coulombCutoffBound_root_dist (hzj j) (hsep j hj) hd (hzj k) hρs1
    exact coulombWeight_quot_bounds hρs hρs1 hm1 hmM (by linarith only [h1, hδ])
      (by linarith only [h3, hδ1]) hLρ hL2
  have hc : L⁻¹ ≤ normPlus x ∧ normPlus x ≤ L :=
    coulombCutoffBound_mem_of_one_le hL1 hm1 (by linarith only [hmM, hL2, hZs])
  have hRk := coulombCutoffBound_root_rpow hDk γ (α k)
  unfold coulombCutoffFiniteWeight
  rw [← hRk]
  exact coulombCutoffBound_rootForm_le (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r)))
    (fun j => γ * α j) (normPlus x) (‖x - z k‖ + Real.exp (-r)) (normPlus x) (γ * αinf) k hL1 hE
    hDk rfl hc hc ha hα hαinf

/-- The inverted-chart weight near a root, where the inverted partition function is supported. -/
theorem coulombCutoffBound_infinity_root {N : ℕ} {Zs E ρs Ri L : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri) (hLρ : Zs + 1 ≤ L * ρs)
    (hL3 : 3 * Zs + 3 ≤ L) (hLRi : (Zs + 1) * Ri ≤ L)
    {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {k : Fin N} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hsep : ∀ j, j ≠ k → 2 * ρs ≤ ‖z j - z k‖) (hx : x ∈ Metric.ball (z k) ρs)
    (hxRi : Ri⁻¹ ≤ ‖x‖) :
    coulombCutoffInfinityWeight γ α z αinf r x⁻¹ ≤
      ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) *
        ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) := by
  have hRipos : 0 < Ri := lt_of_lt_of_le one_pos hRi
  have ht0 : 0 < ‖x‖ := lt_of_lt_of_le (inv_pos.mpr hRipos) hxRi
  have hx0 : x ≠ 0 := norm_pos_iff.mp ht0
  have hzj := coulombCutoffBound_norm_le hz
  have hd : ‖x - z k‖ < ρs := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  have ht : ‖x‖ ≤ Zs + 1 := by
    have h1 := norm_sub_norm_le x (z k)
    linarith only [h1, hd, hρs1, hzj k]
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have htm : ‖x‖ ≤ normPlus x := le_max_right _ _
  have hmM : normPlus x ≤ Zs + 1 := max_le (by linarith only [hZs]) ht
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hδt : Real.exp (-r) * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left ht0.le hδ1
  have hδt0 : 0 < Real.exp (-r) * ‖x‖ := mul_pos hδ ht0
  have hL1 : 1 ≤ L := by linarith only [hL3, hZs]
  have hL2 : 2 ≤ L := by linarith only [hL3, hZs]
  have hDk : 0 < ‖x - z k‖ + Real.exp (-r) := by positivity
  have ha : ∀ j, j ≠ k → L⁻¹ ≤ normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ∧
      normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ≤ L := by
    intro j hj
    obtain ⟨h1, h3⟩ := coulombCutoffBound_root_dist (hzj j) (hsep j hj) hd (hzj k) hρs1
    exact coulombWeight_quot_bounds hρs hρs1 hm1 hmM (by linarith only [h1, hδt0])
      (by linarith only [h3, hδt, ht]) hLρ hL3
  obtain ⟨hc1, hc2⟩ := coulombCutoffBound_root_numer (d := ‖x - z k‖) (δ := Real.exp (-r))
    hm1 htm hmM (norm_nonneg _) hδ hRi hxRi
  have hc : L⁻¹ ≤ normPlus x * (‖x - z k‖ + Real.exp (-r)) /
      (‖x - z k‖ + Real.exp (-r) * ‖x‖) ∧ normPlus x * (‖x - z k‖ + Real.exp (-r)) /
      (‖x - z k‖ + Real.exp (-r) * ‖x‖) ≤ L :=
    coulombCutoffBound_mem_of_one_le hL1 hc1 (hc2.trans hLRi)
  obtain ⟨hg1, hg2⟩ := coulombCutoffBound_infty_base_mem (m := normPlus x) (t := ‖x‖)
    (δ := Real.exp (-r)) hm1 htm ht0.le hδ hδ1
  have hg : L⁻¹ ≤ normPlus x / (1 + Real.exp (-r) * ‖x‖) ∧
      normPlus x / (1 + Real.exp (-r) * ‖x‖) ≤ L :=
    ⟨(inv_anti₀ two_pos hL2).trans hg1, hg2.trans (hmM.trans (by linarith only [hL3, hZs]))⟩
  have hRk := coulombCutoffBound_root_rpow hDk γ (α k)
  rw [coulombCutoffBound_infinityWeight_inv γ α z αinf r hx0, ← hRk]
  exact coulombCutoffBound_rootForm_le
    (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖)) (fun j => γ * α j)
    (normPlus x * (‖x - z k‖ + Real.exp (-r)) / (‖x - z k‖ + Real.exp (-r) * ‖x‖))
    (‖x - z k‖ + Real.exp (-r)) (normPlus x / (1 + Real.exp (-r) * ‖x‖)) (γ * αinf) k hL1 hE
    hDk (coulombCutoffBound_div_eq hDk.ne') hc hg ha hα hαinf

/-! ### The bulk -/

/-- The scale `L` used in the bulk. -/
theorem coulombCutoffBound_bulk_const {Zs R0 ρs : ℝ} (hZs : 0 ≤ Zs) (hR0 : 0 ≤ R0)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) : ∃ L : ℝ, 1 + R0 ≤ L * ρs ∧ 2 * R0 + Zs + 2 ≤ L := by
  refine ⟨(2 * R0 + Zs + 2) / ρs, ?_, ?_⟩
  · rw [div_mul_cancel₀ _ hρs.ne']
    linarith only [hR0, hZs]
  · rw [le_div_iff₀ hρs]
    linarith only [mul_nonneg (by linarith only [hR0, hZs] : 0 ≤ 2 * R0 + Zs + 2)
      (sub_nonneg.2 hρs1)]

/-- The finite-chart weight is bounded in the bulk. -/
theorem coulombCutoffBound_finite_bulk {N : ℕ} {Zs E ρs R0 L : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hR0 : 0 ≤ R0) (hLρ : 1 + R0 ≤ L * ρs)
    (hLB : 2 * R0 + Zs + 2 ≤ L) {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hxR : ‖x‖ ≤ R0) (hxz : ∀ k, ρs ≤ ‖x - z k‖) :
    coulombCutoffFiniteWeight γ α z αinf r x ≤ ENNReal.ofReal (L ^ ((N : ℝ) * E + E)) := by
  have hzj := coulombCutoffBound_norm_le hz
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have hmM : normPlus x ≤ 1 + R0 := max_le (by linarith only [hR0]) (by linarith only [hxR])
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hL1 : 1 ≤ L := by linarith only [hLB, hR0, hZs]
  have hLpos : 0 < L := by linarith only [hLB, hR0, hZs]
  have ha : ∀ j, L⁻¹ ≤ normPlus x / (‖x - z j‖ + Real.exp (-r)) ∧
      normPlus x / (‖x - z j‖ + Real.exp (-r)) ≤ L := by
    intro j
    have h3 : ‖x - z j‖ ≤ R0 + Zs := by
      have := norm_sub_le x (z j)
      linarith only [this, hxR, hzj j]
    exact coulombWeight_quot_bounds hρs hρs1 hm1 hmM (by linarith only [hxz j, hδ])
      (by linarith only [h3, hδ1, hR0]) hLρ hLB
  have hLρL : L * ρs ≤ L := mul_le_of_le_one_right hLpos.le hρs1
  have hg : L⁻¹ ≤ normPlus x ∧ normPlus x ≤ L :=
    coulombCutoffBound_mem_of_one_le hL1 hm1 (hmM.trans (hLρ.trans hLρL))
  unfold coulombCutoffFiniteWeight
  exact coulombCutoffBound_form_le (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r)))
    (fun j => γ * α j) (normPlus x) (γ * αinf) hL1 hE ha hg hα hαinf

/-- The inverted-chart weight is bounded in the bulk. -/
theorem coulombCutoffBound_infinity_bulk {N : ℕ} {Zs E ρs R0 L : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E)
    (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hLρ : 1 + R0 ≤ L * ρs) (hLB : 2 * R0 + Zs + 2 ≤ L)
    {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hxR : ‖x‖ ≤ R0) (hxz : ∀ k, ρs ≤ ‖x - z k‖) (hx0 : x ≠ 0) :
    coulombCutoffInfinityWeight γ α z αinf r x⁻¹ ≤ ENNReal.ofReal (L ^ ((N : ℝ) * E + E)) := by
  have hzj := coulombCutoffBound_norm_le hz
  have ht0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hm1 : 1 ≤ normPlus x := le_max_left _ _
  have htm : ‖x‖ ≤ normPlus x := le_max_right _ _
  have hmM : normPlus x ≤ 1 + R0 := max_le (by linarith only [hxR, ht0]) (by linarith only [hxR])
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hδt : Real.exp (-r) * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left ht0.le hδ1
  have hδt0 : 0 < Real.exp (-r) * ‖x‖ := mul_pos hδ ht0
  have hL1 : 1 ≤ L := by linarith only [hLB, hZs, hxR, ht0]
  have hL2 : 2 ≤ L := by linarith only [hLB, hZs, hxR, ht0]
  have hLpos : 0 < L := by linarith only [hLB, hZs, hxR, ht0]
  have ha : ∀ j, L⁻¹ ≤ normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ∧
      normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ≤ L := by
    intro j
    have h3 : ‖x - z j‖ ≤ R0 + Zs := by
      have := norm_sub_le x (z j)
      linarith only [this, hxR, hzj j]
    exact coulombWeight_quot_bounds hρs hρs1 hm1 hmM (by linarith only [hxz j, hδt0])
      (by linarith only [h3, hδt, hxR]) hLρ hLB
  obtain ⟨hg1, hg2⟩ := coulombCutoffBound_infty_base_mem (m := normPlus x) (t := ‖x‖)
    (δ := Real.exp (-r)) hm1 htm ht0.le hδ hδ1
  have hLρL : L * ρs ≤ L := mul_le_of_le_one_right hLpos.le hρs1
  have hg : L⁻¹ ≤ normPlus x / (1 + Real.exp (-r) * ‖x‖) ∧
      normPlus x / (1 + Real.exp (-r) * ‖x‖) ≤ L :=
    ⟨(inv_anti₀ two_pos hL2).trans hg1, hg2.trans (hmM.trans (hLρ.trans hLρL))⟩
  rw [coulombCutoffBound_infinityWeight_inv γ α z αinf r hx0]
  exact coulombCutoffBound_form_le
    (fun j => normPlus x / (‖x - z j‖ + Real.exp (-r) * ‖x‖)) (fun j => γ * α j)
    (normPlus x / (1 + Real.exp (-r) * ‖x‖)) (γ * αinf) hL1 hE ha hg hα hαinf

/-! ### The exterior -/

/-- The inverted-chart weight in the exterior is at most a constant times the power at infinity. -/
theorem coulombCutoffBound_infinity_exterior {N : ℕ} {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E)
    (hR0 : 2 * Zs + 2 ≤ R0) {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hxR : R0 ≤ ‖x‖) :
    coulombCutoffInfinityWeight γ α z αinf r x⁻¹ ≤
      ENNReal.ofReal ((5 / 2 : ℝ) ^ ((N : ℝ) * E)) *
        (ENNReal.ofReal (2 ^ E) * ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0)) := by
  have hzj := coulombCutoffBound_norm_le hz
  have ht0 : 0 < ‖x‖ := by linarith only [hxR, hR0, hZs]
  have hx0 : x ≠ 0 := norm_pos_iff.mp ht0
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith only [hxR, hR0, hZs])
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hδt : Real.exp (-r) * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left ht0.le hδ1
  have hδt0 : 0 < Real.exp (-r) * ‖x‖ := mul_pos hδ ht0
  have ha : ∀ j, ((5 / 2 : ℝ))⁻¹ ≤ ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ∧
      ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ≤ 5 / 2 := by
    intro j
    have h1 := norm_sub_norm_le x (z j)
    have h2 := norm_sub_le x (z j)
    exact coulombCutoffBound_ext_quot (Zs := Zs) (by linarith only [hxR, hR0, hZs]) ht0
      (by linarith only [h1, hzj j, hδt0])
      (by linarith only [h2, hzj j, hδt])
  rw [coulombCutoffBound_infinityWeight_inv γ α z αinf r hx0, hnp]
  exact mul_le_mul' (coulombCutoffBound_prod_le Finset.univ
    (fun j => ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖)) (fun j => γ * α j)
    (by norm_num) hE (fun j _ => ha j) fun j _ => hα j)
    (coulombCutoffBound_exterior_last (by linarith only [hxR, hR0, hZs]) hδ hδ1 hαinf)

/-! ### The fixed exterior disk -/

/-- The norm on the fixed exterior disk. -/
theorem coulombCutoffBound_ball_norm {R0 : ℝ} (hR0 : 0 ≤ R0) {x : ℂ}
    (hx : x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8)) :
    R0 + 7 / 8 < ‖x‖ ∧ ‖x‖ < R0 + 9 / 8 := by
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h1 := norm_sub_norm_le x (((R0 + 1 : ℝ)) : ℂ)
  have h2 := norm_sub_norm_le (((R0 + 1 : ℝ)) : ℂ) x
  have h3 : ‖(((R0 + 1 : ℝ)) : ℂ)‖ = R0 + 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith only [hR0])]
  rw [norm_sub_rev] at h2
  constructor <;> linarith only [h1, h2, h3, hx]

/-- The finite-chart weight on the fixed exterior disk is bounded below. -/
theorem coulombCutoffBound_finite_ball {N : ℕ} {Zs E R0 : ℝ} (hZs : 0 ≤ Zs)
    (hR0 : 2 * Zs + 2 ≤ R0) {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hx : x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8)) :
    ENNReal.ofReal ((R0 + 2) ^ (-((N : ℝ) * E + E))) ≤
      coulombCutoffFiniteWeight γ α z αinf r x := by
  have hzj := coulombCutoffBound_norm_le hz
  obtain ⟨ht1, ht2⟩ := coulombCutoffBound_ball_norm (by linarith only [hR0, hZs]) hx
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith only [ht1, hR0, hZs])
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hL : 1 ≤ R0 + 2 := by linarith only [hR0, hZs]
  have ha : ∀ j, (R0 + 2)⁻¹ ≤ ‖x‖ / (‖x - z j‖ + Real.exp (-r)) ∧
      ‖x‖ / (‖x - z j‖ + Real.exp (-r)) ≤ R0 + 2 := by
    intro j
    have h1 := norm_sub_norm_le x (z j)
    have h2 := norm_sub_le x (z j)
    exact coulombCutoffBound_mem_mono two_pos (by linarith only [hR0, hZs])
      (coulombWeight_exterior_quot_bounds (w := Zs + 1) (by linarith only [hZs])
        (by linarith only [ht1, hR0])
        (by linarith only [h1, hzj j, hδ])
        (by linarith only [h2, hzj j, hδ1]))
  have hg : (R0 + 2)⁻¹ ≤ ‖x‖ ∧ ‖x‖ ≤ R0 + 2 :=
    coulombCutoffBound_mem_of_one_le hL (by linarith only [ht1, hR0, hZs])
      (by linarith only [ht2])
  unfold coulombCutoffFiniteWeight
  rw [hnp]
  exact coulombCutoffBound_form_ge (fun j => ‖x‖ / (‖x - z j‖ + Real.exp (-r)))
    (fun j => γ * α j) ‖x‖ (γ * αinf) hL ha hg hα hαinf

/-- The inverted-chart weight on the fixed exterior disk is bounded below. -/
theorem coulombCutoffBound_infinity_ball {N : ℕ} {Zs E R0 : ℝ} (hZs : 0 ≤ Zs)
    (hR0 : 2 * Zs + 2 ≤ R0) {γ : ℝ} {α : Fin N → ℝ} {z : Fin N → ℂ} {αinf r : ℝ} {x : ℂ}
    (hr : 0 ≤ r) (hz : ∑ j, ‖z j‖ ≤ Zs) (hα : ∀ j, |γ * α j| ≤ E) (hαinf : |γ * αinf| ≤ E)
    (hx : x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8)) :
    ENNReal.ofReal ((R0 + 2) ^ (-((N : ℝ) * E + E))) ≤
      coulombCutoffInfinityWeight γ α z αinf r x⁻¹ := by
  have hzj := coulombCutoffBound_norm_le hz
  obtain ⟨ht1, ht2⟩ := coulombCutoffBound_ball_norm (by linarith only [hR0, hZs]) hx
  have ht0 : 0 < ‖x‖ := by linarith only [ht1, hR0, hZs]
  have hx0 : x ≠ 0 := norm_pos_iff.mp ht0
  have hnp : normPlus x = ‖x‖ := max_eq_right (by linarith only [ht1, hR0, hZs])
  obtain ⟨hδ, hδ1⟩ := coulombCutoffBound_exp_neg_mem hr
  have hδt : Real.exp (-r) * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left ht0.le hδ1
  have hδt0 : 0 < Real.exp (-r) * ‖x‖ := mul_pos hδ ht0
  have hL : 1 ≤ R0 + 2 := by linarith only [hR0, hZs]
  have ha : ∀ j, (R0 + 2)⁻¹ ≤ ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ∧
      ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖) ≤ R0 + 2 := by
    intro j
    have h1 := norm_sub_norm_le x (z j)
    have h2 := norm_sub_le x (z j)
    exact coulombCutoffBound_mem_mono (L := 5 / 2) (by norm_num) (by linarith only [hR0, hZs])
      (coulombCutoffBound_ext_quot (Zs := Zs) (by linarith only [ht1, hR0]) ht0
        (by linarith only [h1, hzj j, hδt0])
        (by linarith only [h2, hzj j, hδt]))
  have hg : (R0 + 2)⁻¹ ≤ ‖x‖ / (1 + Real.exp (-r) * ‖x‖) ∧
      ‖x‖ / (1 + Real.exp (-r) * ‖x‖) ≤ R0 + 2 := by
    obtain ⟨hg1, hg2⟩ := coulombCutoffBound_infty_base_mem (m := ‖x‖) (t := ‖x‖)
      (δ := Real.exp (-r)) (by linarith only [ht1, hR0, hZs]) le_rfl ht0.le hδ hδ1
    exact ⟨(inv_anti₀ two_pos (by linarith only [hR0, hZs])).trans hg1,
      hg2.trans (by linarith only [ht2])⟩
  rw [coulombCutoffBound_infinityWeight_inv γ α z αinf r hx0, hnp]
  exact coulombCutoffBound_form_ge (fun j => ‖x‖ / (‖x - z j‖ + Real.exp (-r) * ‖x‖))
    (fun j => γ * α j) (‖x‖ / (1 + Real.exp (-r) * ‖x‖)) (γ * αinf) hL ha hg hα hαinf

/-! ### The pointwise bounds -/

/-- On the support of the inverted partition function, a bound on `‖x⁻¹‖` is a lower bound on
`‖x‖`. -/
theorem coulombCutoffBound_le_norm_of_inv {x : ℂ} {Ri : ℝ} (hRi : 0 < Ri) (hx : x ≠ 0)
    (h : ‖x⁻¹‖ ≤ Ri) : Ri⁻¹ ≤ ‖x‖ := by
  rw [norm_inv] at h
  exact (inv_le_comm₀ (norm_pos_iff.mpr hx) hRi).1 h

/-- Near a finite root the single-chart weight is the softened root singularity times a bounded
factor, uniformly over bounded parameters. -/
theorem coulombCutoffWeight_le_root (partition : GMCChartPartition) (N : ℕ)
    {Zs E ρs Ri : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1) (hRi : 1 ≤ Ri)
    (hsupp : ∀ u, partition.infinityWeight u ≠ 0 → ‖u‖ ≤ Ri) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (k : Fin N)
      (x : ℂ), 0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      (∀ j, j ≠ k → 2 * ρs ≤ ‖z j - z k‖) → x ∈ Metric.ball (z k) ρs → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤
        ENNReal.ofReal C * ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)) := by
  obtain ⟨L, hLρ, hL3, hLRi⟩ := coulombCutoffBound_root_const hZs hρs hρs1 hRi
  have hLpos : 0 < L := by linarith only [hL3, hZs]
  have hRipos : 0 < Ri := lt_of_lt_of_le one_pos hRi
  refine ⟨L ^ ((N : ℝ) * E + E + E) + L ^ ((N : ℝ) * E + E + E), by positivity, ?_⟩
  intro γ α z αinf r k x hr hz hα hαinf hsep hx hx0
  have key := coulombCutoffBound_weight_le partition γ α z αinf r hx0
    (A := ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) *
      ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)))
    (B := ENNReal.ofReal (L ^ ((N : ℝ) * E + E + E)) *
      ENNReal.ofReal ((‖x - z k‖ + Real.exp (-r)) ^ (-γ * α k)))
    (fun _ => coulombCutoffBound_finite_root hZs hE hρs hρs1 hLρ (by linarith only [hL3, hZs]) hr
      hz hα hαinf hsep hx)
    (fun h => coulombCutoffBound_infinity_root hZs hE hρs hρs1 hRi hLρ hL3 hLRi hr hz hα hαinf
      hsep hx (coulombCutoffBound_le_norm_of_inv hRipos hx0 (hsupp _ h)))
  rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)] at key
  exact key

/-- Away from the roots, on a bounded set, the single-chart weight is bounded. -/
theorem coulombCutoffWeight_le_bulk (partition : GMCChartPartition) (N : ℕ)
    {Zs E ρs R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hR0 : 0 ≤ R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      ‖x‖ ≤ R0 → (∀ k, ρs ≤ ‖x - z k‖) → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤ ENNReal.ofReal C := by
  obtain ⟨L, hLρ, hLB⟩ := coulombCutoffBound_bulk_const hZs hR0 hρs hρs1
  have hLpos : 0 < L := by linarith only [hLB, hR0, hZs]
  refine ⟨L ^ ((N : ℝ) * E + E) + L ^ ((N : ℝ) * E + E), by positivity, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hxR hxz hx0
  have key := coulombCutoffBound_weight_le partition γ α z αinf r hx0
    (A := ENNReal.ofReal (L ^ ((N : ℝ) * E + E))) (B := ENNReal.ofReal (L ^ ((N : ℝ) * E + E)))
    (fun _ => coulombCutoffBound_finite_bulk hZs hE hρs hρs1 hR0 hLρ hLB hr hz hα hαinf hxR hxz)
    (fun _ => coulombCutoffBound_infinity_bulk hZs hE hρs hρs1 hLρ hLB hr hz hα hαinf hxR hxz
      hx0)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)] at key
  exact key

/-- Far out the single-chart weight is at most a constant times the power at infinity. -/
theorem coulombCutoffWeight_le_exterior (partition : GMCChartPartition) (N : ℕ)
    {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hR0 : 2 * Zs + 2 ≤ R0)
    (hsuppf : ∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < R0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E → R0 ≤ ‖x‖ →
      coulombCutoffWeight partition γ α z αinf r x ≤
        ENNReal.ofReal C * ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0) := by
  refine ⟨(5 / 2 : ℝ) ^ ((N : ℝ) * E) * 2 ^ E, by positivity, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hxR
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith only [hxR, hR0, hZs])
  have key := coulombCutoffBound_weight_le partition γ α z αinf r hx0 (A := 0)
    (B := ENNReal.ofReal ((5 / 2 : ℝ) ^ ((N : ℝ) * E)) *
      (ENNReal.ofReal (2 ^ E) * ENNReal.ofReal (‖x‖ ^ max (γ * αinf) 0)))
    (fun h => absurd (hsuppf x h) (not_lt.2 hxR))
    (fun _ => coulombCutoffBound_infinity_exterior hZs hE hR0 hr hz hα hαinf hxR)
  rw [zero_add, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at key
  exact key

/-- On a fixed exterior disk the single-chart weight is bounded below. -/
theorem coulombCutoffWeight_ge_ball (partition : GMCChartPartition) (N : ℕ)
    {Zs E R0 : ℝ} (hZs : 0 ≤ Zs) (hR0 : 2 * Zs + 2 ≤ R0) :
    ∃ c : ℝ, 0 < c ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      x ∈ Metric.ball (((R0 + 1 : ℝ)) : ℂ) (1 / 8) →
      ENNReal.ofReal c ≤ coulombCutoffWeight partition γ α z αinf r x := by
  refine ⟨(R0 + 2) ^ (-((N : ℝ) * E + E)), Real.rpow_pos_of_pos (by linarith only [hR0, hZs]) _, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hx
  obtain ⟨ht1, -⟩ := coulombCutoffBound_ball_norm (by linarith only [hR0, hZs]) hx
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith only [ht1, hR0, hZs])
  exact coulombCutoffBound_le_weight partition γ α z αinf r hx0
    (coulombCutoffBound_finite_ball hZs hR0 hr hz hα hαinf hx)
    (coulombCutoffBound_infinity_ball hZs hR0 hr hz hα hαinf hx)

end DOZZ.Proofs
