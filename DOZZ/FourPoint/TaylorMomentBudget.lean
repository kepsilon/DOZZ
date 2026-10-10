/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TwoRootedExponents

/-! Strict positive-moment and spatial margins in the intermediate Taylor region. -/

@[expose] public section
open Set
namespace DOZZ.Proofs

/-- The optimized intermediate-region order lies strictly below both GMC thresholds.
The reduced order is below 2, so the interpolation of the square in the proof of
[KRV, (fundest)] is legitimate. -/
theorem twoRooted_optimized_order (γ α q : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2)
    (hα : γ / 2 < α) (hα2 : α < 2 / γ) (hq : 1 < q) :
    let r := (γ / 2 + Q γ - α) / (γ * q)
    0 < r ∧ r < 2 ∧
      q * r < min (4 / γ ^ 2) (2 / γ * (Q γ - α)) ∧
        γ * (Q γ - α + γ / 2) * r - γ ^ 2 * q * r ^ 2 / 2 =
          (γ / 2 + Q γ - α) ^ 2 / (2 * q) := by
  have hqpos : 0 < q := zero_lt_one.trans hq
  have hγsqpos : 0 < γ ^ 2 := sq_pos_of_pos hγ
  have hQmult : γ * Q γ = 2 + γ ^ 2 / 2 := by unfold Q; field_simp
  have hαmult : γ * α > γ ^ 2 / 2 := by
    have hh := mul_lt_mul_of_pos_left hα hγ
    nlinarith only [hh]
  have hαupper : γ * α < 2 := by simpa only [mul_comm] using (lt_div_iff₀ hγ).mp hα2
  have ha : 0 < γ / 2 + Q γ - α := by unfold Q; linarith only [hα2, hγ]
  have hrpos : 0 < (γ / 2 + Q γ - α) / (γ * q) := div_pos ha (mul_pos hγ hqpos)
  have horder : q * ((γ / 2 + Q γ - α) / (γ * q)) = (γ / 2 + Q γ - α) / γ := by
    field_simp
  have hbulk : (γ / 2 + Q γ - α) / γ < 4 / γ ^ 2 := by
    apply (div_lt_div_iff₀ hγ hγsqpos).mpr
    nlinarith only [hQmult, hαmult, hγ, hγ2]
  have hinsertion : (γ / 2 + Q γ - α) / γ < 2 / γ * (Q γ - α) := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_div_iff_of_pos_right hγ).mpr
    unfold Q
    linarith only [hα2]
  have hsmall : (γ / 2 + Q γ - α) / γ < 2 := by
    apply (div_lt_iff₀ hγ).mpr
    have hh : γ / 2 + Q γ - α < 2 * γ := by
      apply (mul_lt_mul_iff_right₀ hγ).mp
      nlinarith only [hQmult, hαmult, hγsq]
    simpa only [mul_comm] using hh
  refine ⟨hrpos, ?_, ?_, ?_⟩
  · have hh : (γ / 2 + Q γ - α) / (γ * q) < q * ((γ / 2 + Q γ - α) / (γ * q)) := by
      exact lt_mul_of_one_lt_left hrpos hq
    rw [horder] at hh
    exact hh.trans hsmall
  · rw [horder]
    exact lt_min hbulk hinsertion
  · field_simp
    ring

/-- Choose Holder, radial cutoff and near-root margins together, before any spatial scale. -/
theorem taylor_region_margins (κ W d n : ℝ)
    (hκ : 0 < κ) (hκ2 : κ < 2) (hW : 2 * κ < W) (hd : 0 < d) (hn : 0 < n) :
    ∃ q δ ε η : ℝ, 1 < q ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ 0 < η ∧ η < 2 - κ ∧
      η ≤ δ * d ∧ η ≤ n ∧
        κ - 2 + η ≤ -2 - 2 * ε + (1 - δ) * W / (2 * q) := by
  let q : ℝ := (W + 2 * κ) / (4 * κ)
  have hq : 1 < q := by
    dsimp only [q]
    apply (lt_div_iff₀ (by positivity : 0 < 4 * κ)).mpr
    linarith only [hW]
  have hqpos : 0 < q := zero_lt_one.trans hq
  let E : ℝ := W / (2 * q)
  have hE : κ < E := by
    apply (lt_div_iff₀ (mul_pos (by norm_num) hqpos)).mpr
    have heq : κ * (2 * q) = (W + 2 * κ) / 2 := by dsimp only [q]; field_simp; ring
    rw [heq]
    linarith only [hW]
  have hEpos : 0 < E := hκ.trans hE
  let g : ℝ := E - κ
  have hg : 0 < g := sub_pos.mpr hE
  let δ : ℝ := min (1 / 2) (g / (4 * E))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hg (by positivity))
  have hδ1 : δ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hδE : δ * E ≤ g / 4 := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right (1 / 2 : ℝ) (g / (4 * E))) hEpos.le
    have heq : g / (4 * E) * E = g / 4 := by field_simp
    exact hh.trans_eq heq
  let ε : ℝ := g / 8
  have hε : 0 < ε := div_pos hg (by norm_num)
  let η : ℝ := min (g / 4) (min (δ * d / 2) (min (n / 2) ((2 - κ) / 2)))
  have hη : 0 < η := lt_min (div_pos hg (by norm_num))
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hηg : η ≤ g / 4 := min_le_left _ _
  have hηd : η ≤ δ * d / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηn : η ≤ n / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hηκ : η ≤ (2 - κ) / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨q, δ, ε, η, hq, hδ, hδ1, hε, hη, ?_, ?_, ?_, ?_⟩
  · linarith only [hηκ, hκ2]
  · have hh : 0 < δ * d := mul_pos hδ hd
    linarith only [hηd, hh]
  · linarith only [hηn, hn]
  · have heq : (1 - δ) * W / (2 * q) = E - δ * E := by dsimp only [E]; ring
    rw [heq]
    dsimp only [ε, g] at hηg hδE ⊢
    linarith only [hηg, hδE, hE]

end DOZZ.Proofs
