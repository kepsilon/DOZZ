/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Quadratic small-deviation recursions

Two pure real-analysis lemmas about antitone nonnegative functions `G` satisfying a quadratic
recursion `G x ≤ error x + B * G (κ * x - c₀) ^ 2`. If the error vanishes and `G` is eventually
small enough, then `G` tends to zero. If the error is Gaussian and the contraction ratio `κ`
exceeds one half, then `G` decays like a stretched exponential `exp (-d * x ^ β)` with `β > 1`. -/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- If an antitone nonnegative function satisfies a quadratic recursion with vanishing error and
is eventually below `L` with `L * B < 1`, then it tends to zero. -/
theorem quadRec_tendsto_zero
    (G a : ℝ → ℝ) (hG : Antitone G) (hG0 : ∀ x, 0 ≤ G x)
    (κ c₀ B x₀ L : ℝ) (hκ : 0 < κ) (hB : 0 < B) (hL : L * B < 1)
    (ha : Tendsto a atTop (𝓝 0))
    (hrec : ∀ x, x₀ ≤ x → G x ≤ a x + B * G (κ * x - c₀) ^ 2)
    (hsmall : ∀ᶠ x in atTop, G x ≤ L) :
    Tendsto G atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range G) := ⟨0, by rintro _ ⟨x, rfl⟩; exact hG0 x⟩
  have htend : Tendsto G atTop (𝓝 (⨅ x, G x)) := tendsto_atTop_ciInf hG hbdd
  set g : ℝ := ⨅ x, G x
  have hg0 : 0 ≤ g := le_ciInf hG0
  have hgL : g ≤ L := by
    obtain ⟨x, hx⟩ := hsmall.exists
    exact (ciInf_le hbdd x).trans hx
  have hlin : Tendsto (fun x : ℝ => κ * x - c₀) atTop atTop := by
    have h1 : Tendsto (fun x : ℝ => κ * x) atTop atTop := tendsto_id.const_mul_atTop hκ
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c₀) h1
  have hcomp : Tendsto (fun x : ℝ => G (κ * x - c₀)) atTop (𝓝 g) := htend.comp hlin
  have hrhs : Tendsto (fun x : ℝ => a x + B * G (κ * x - c₀) ^ 2) atTop (𝓝 (0 + B * g ^ 2)) :=
    ha.add ((hcomp.pow 2).const_mul B)
  have hineq : g ≤ 0 + B * g ^ 2 :=
    le_of_tendsto_of_tendsto htend hrhs (eventually_atTop.2 ⟨x₀, fun x hx => hrec x hx⟩)
  have hBg : B * g < 1 := by
    have : B * g ≤ B * L := mul_le_mul_of_nonneg_left hgL hB.le
    linarith
  have hprod : g * (1 - B * g) ≤ 0 := by nlinarith
  have hg_nonpos : g ≤ 0 := by
    by_contra hpos
    have := mul_pos (not_le.1 hpos) (sub_pos.2 hBg)
    linarith
  have hg_zero : g = 0 := le_antisymm hg_nonpos hg0
  rw [hg_zero] at htend
  exact htend

/-- A contraction ratio above one half allows an exponent `β ∈ (1, 2)` with `2 k ^ β > 1`. -/
theorem quadRec_exists_beta (k : ℝ) (hk : 1 / 2 < k) :
    ∃ β : ℝ, 1 < β ∧ β < 2 ∧ 1 < 2 * k ^ β := by
  have hk0 : 0 < k := lt_trans (by norm_num) hk
  have hcont : ContinuousAt (fun β : ℝ => 2 * k ^ β) 1 :=
    continuousAt_const.mul (Real.continuousAt_const_rpow hk0.ne')
  have h1 : ∀ᶠ β in 𝓝 (1 : ℝ), 1 < 2 * k ^ β := by
    refine hcont.eventually (lt_mem_nhds ?_)
    simp only [Real.rpow_one]
    linarith
  have h2 : ∀ᶠ β in 𝓝 (1 : ℝ), β < 2 := eventually_lt_nhds (by norm_num)
  have h3 : ∀ᶠ β in 𝓝[>] (1 : ℝ), (1 < 2 * k ^ β ∧ β < 2) ∧ 1 < β :=
    ((h1.and h2).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨β, ⟨hβ1, hβ2⟩, hβ3⟩ := h3.exists
  exact ⟨β, hβ3, hβ2, hβ1⟩

/-- Replacing the shifted argument `κ x - c₀` by `k x` for a smaller ratio `k < κ`. -/
theorem quadRec_shift_recursion
    (G : ℝ → ℝ) (hG : Antitone G) (hG0 : ∀ x, 0 ≤ G x)
    (A B c κ k c₀ x₀ : ℝ) (hB : 0 ≤ B) (hkκ : k < κ)
    (hrec : ∀ x, x₀ ≤ x → G x ≤ A * Real.exp (-c * x ^ 2) + B * G (κ * x - c₀) ^ 2) :
    ∀ x, max x₀ (|c₀| / (κ - k)) ≤ x →
      G x ≤ A * Real.exp (-c * x ^ 2) + B * G (k * x) ^ 2 := by
  intro x hx
  have hx0 : x₀ ≤ x := (le_max_left _ _).trans hx
  have hxc : |c₀| / (κ - k) ≤ x := (le_max_right _ _).trans hx
  have hκk : 0 < κ - k := sub_pos.2 hkκ
  have hc₀ : c₀ ≤ (κ - k) * x := by
    have h1 : |c₀| ≤ x * (κ - k) := (div_le_iff₀ hκk).1 hxc
    have h2 : c₀ ≤ |c₀| := le_abs_self c₀
    linarith
  have hle : k * x ≤ κ * x - c₀ := by linarith
  have h1 : G (κ * x - c₀) ≤ G (k * x) := hG hle
  have h2 : G (κ * x - c₀) ^ 2 ≤ G (k * x) ^ 2 := pow_le_pow_left₀ (hG0 _) h1 2
  have h3 : B * G (κ * x - c₀) ^ 2 ≤ B * G (k * x) ^ 2 := mul_le_mul_of_nonneg_left h2 hB
  have h4 := hrec x hx0
  linarith

/-- Squaring the bound at the contracted point `k x` leaves at most half of the target bound at
`x`, once `x` is beyond the scale `Z`. -/
theorem quadRec_square_step (k β d h ℓ B Z x : ℝ) (hk : 0 < k) (hd : 0 < d) (hh : 0 < h)
    (hkβ : 2 * k ^ β = 1 + h) (hB : B * Real.exp (-ℓ) ≤ 1 / 2) (hB0 : 0 ≤ B)
    (hZx : Z ≤ x) (hZ : 0 ≤ Z) (hβ : 0 ≤ β) (hℓ : ℓ ≤ h * d * Z ^ β) :
    B * Real.exp (-d * (k * x) ^ β) ^ 2 ≤ 1 / 2 * Real.exp (-d * x ^ β) := by
  have hx : 0 ≤ x := hZ.trans hZx
  have hxβ : Z ^ β ≤ x ^ β := Real.rpow_le_rpow hZ hZx hβ
  have h1 : Real.exp (-d * (k * x) ^ β) ^ 2 =
      Real.exp (-d * x ^ β) * Real.exp (-(h * d * x ^ β)) := by
    rw [Real.mul_rpow hk.le hx, pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-d * x ^ β) * hkβ
  have h2 : Real.exp (-(h * d * x ^ β)) ≤ Real.exp (-ℓ) := by
    apply Real.exp_le_exp.2
    have : h * d * Z ^ β ≤ h * d * x ^ β :=
      mul_le_mul_of_nonneg_left hxβ (mul_nonneg hh.le hd.le)
    linarith
  calc B * Real.exp (-d * (k * x) ^ β) ^ 2
      = B * (Real.exp (-d * x ^ β) * Real.exp (-(h * d * x ^ β))) := by rw [h1]
    _ ≤ B * (Real.exp (-d * x ^ β) * Real.exp (-ℓ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg _)) hB0
    _ = (B * Real.exp (-ℓ)) * Real.exp (-d * x ^ β) := by ring
    _ ≤ 1 / 2 * Real.exp (-d * x ^ β) := mul_le_mul_of_nonneg_right hB (Real.exp_nonneg _)

/-- The Gaussian error term is at most half of the target bound once `d ≤ c / 2` and the scale
`Z` is large. -/
theorem quadRec_gaussian_step (A c d β Z x : ℝ) (hA : 0 ≤ A) (hd : 0 ≤ d) (hβ : β ≤ 2)
    (hdc : d ≤ c / 2) (hZ : 1 ≤ Z) (hZx : Z ≤ x)
    (hAZ : A * Real.exp (-(c / 2) * Z ^ 2) ≤ 1 / 2) :
    A * Real.exp (-c * x ^ 2) ≤ 1 / 2 * Real.exp (-d * x ^ β) := by
  have hx1 : 1 ≤ x := hZ.trans hZx
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have h1 : x ^ β ≤ x ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 hβ
    rwa [Real.rpow_two] at this
  have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
  have h2 : d * x ^ β ≤ c / 2 * x ^ 2 :=
    (mul_le_mul_of_nonneg_left h1 hd).trans (mul_le_mul_of_nonneg_right hdc hx2)
  have h3 : Z ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hZ0 hZx 2
  have hc : 0 ≤ c / 2 := hd.trans hdc
  have h3' : c / 2 * Z ^ 2 ≤ c / 2 * x ^ 2 := mul_le_mul_of_nonneg_left h3 hc
  have h4 : Real.exp (-c * x ^ 2) ≤
      Real.exp (-(c / 2) * Z ^ 2) * Real.exp (-d * x ^ β) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    linarith
  calc A * Real.exp (-c * x ^ 2)
      ≤ A * (Real.exp (-(c / 2) * Z ^ 2) * Real.exp (-d * x ^ β)) :=
        mul_le_mul_of_nonneg_left h4 hA
    _ = (A * Real.exp (-(c / 2) * Z ^ 2)) * Real.exp (-d * x ^ β) := by ring
    _ ≤ 1 / 2 * Real.exp (-d * x ^ β) := mul_le_mul_of_nonneg_right hAZ (Real.exp_nonneg _)

/-- A Gaussian tail estimate for large scales. -/
theorem quadRec_gaussian_tail (A c Z : ℝ) (hc : 0 < c) (hZ : 1 ≤ Z) (hAZ : 4 * A / c ≤ Z) :
    A * Real.exp (-(c / 2) * Z ^ 2) ≤ 1 / 2 := by
  have h1 : 4 * A ≤ Z * c := (div_le_iff₀ hc).1 hAZ
  have h2 : Z ≤ Z ^ 2 := by nlinarith
  have h3 : c / 2 * Z ≤ c / 2 * Z ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : c / 2 * Z ^ 2 ≤ Real.exp (c / 2 * Z ^ 2) := by
    have := Real.add_one_le_exp (c / 2 * Z ^ 2)
    linarith
  have hE : 0 < Real.exp (c / 2 * Z ^ 2) := Real.exp_pos _
  have h5 : A ≤ 1 / 2 * Real.exp (c / 2 * Z ^ 2) := by linarith
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  exact h5

/-- The inductive core: if the bound `G x ≤ exp (-d * x ^ β)` holds on `[Y, Z]` with `Y = k * Z`,
and the error terms are absorbed beyond `Z`, then it propagates to all `x ≥ Y`. -/
theorem quadRec_core
    (G : ℝ → ℝ) (hG : Antitone G) (hG0 : ∀ x, 0 ≤ G x)
    (A B c k β d h ℓ Y Z : ℝ) (hk0 : 0 < k) (hk1 : k < 1) (hβ : 0 ≤ β) (hd : 0 < d)
    (hh : 0 < h) (hkβ : 2 * k ^ β = 1 + h) (hB : B * Real.exp (-ℓ) ≤ 1 / 2) (hB0 : 0 ≤ B)
    (hY : 0 < Y) (hYZ : k * Z = Y)
    (hrec : ∀ x, Y ≤ x → G x ≤ A * Real.exp (-c * x ^ 2) + B * G (k * x) ^ 2)
    (hGY : G Y ≤ Real.exp (-d * Z ^ β)) (hℓ : ℓ ≤ h * d * Z ^ β)
    (hgauss : ∀ x, Z ≤ x → A * Real.exp (-c * x ^ 2) ≤ 1 / 2 * Real.exp (-d * x ^ β)) :
    ∀ x, Y ≤ x → G x ≤ Real.exp (-d * x ^ β) := by
  have hkne : k ≠ 0 := hk0.ne'
  have hZ0 : 0 < Z := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hk0.le (not_lt.1 hneg)
    linarith
  have hYZ' : Y ≤ Z := by
    rw [← hYZ]
    exact mul_le_of_le_one_left hZ0.le hk1.le
  have hbase : ∀ x, Y ≤ x → x ≤ Z → G x ≤ Real.exp (-d * x ^ β) := by
    intro x hYx hxZ
    have hx0 : 0 ≤ x := hY.le.trans hYx
    have h1 : x ^ β ≤ Z ^ β := Real.rpow_le_rpow hx0 hxZ hβ
    have h2 : d * x ^ β ≤ d * Z ^ β := mul_le_mul_of_nonneg_left h1 hd.le
    calc G x ≤ G Y := hG hYx
      _ ≤ Real.exp (-d * Z ^ β) := hGY
      _ ≤ Real.exp (-d * x ^ β) := Real.exp_le_exp.2 (by linarith)
  have hstep : ∀ x, Z ≤ x → G (k * x) ≤ Real.exp (-d * (k * x) ^ β) →
      G x ≤ Real.exp (-d * x ^ β) := by
    intro x hZx hGkx
    have hYx : Y ≤ x := hYZ'.trans hZx
    have h1 : G (k * x) ^ 2 ≤ Real.exp (-d * (k * x) ^ β) ^ 2 :=
      pow_le_pow_left₀ (hG0 _) hGkx 2
    have h2 : B * G (k * x) ^ 2 ≤ B * Real.exp (-d * (k * x) ^ β) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 hB0
    have h3 := quadRec_square_step k β d h ℓ B Z x hk0 hd hh hkβ hB hB0 hZx hZ0.le hβ hℓ
    have h4 := hgauss x hZx
    have h5 := hrec x hYx
    linarith
  have key : ∀ n : ℕ, ∀ x, Y ≤ x → x ≤ Z * k⁻¹ ^ n → G x ≤ Real.exp (-d * x ^ β) := by
    intro n
    induction n with
    | zero =>
      intro x hYx hxZ
      exact hbase x hYx (by simpa using hxZ)
    | succ n ih =>
      intro x hYx hxZ
      by_cases hZx : x ≤ Z
      · exact hbase x hYx hZx
      · have hZx' : Z ≤ x := (not_le.1 hZx).le
        refine hstep x hZx' (ih (k * x) ?_ ?_)
        · rw [← hYZ]
          exact mul_le_mul_of_nonneg_left hZx' hk0.le
        · calc k * x ≤ k * (Z * k⁻¹ ^ (n + 1)) := mul_le_mul_of_nonneg_left hxZ hk0.le
            _ = Z * k⁻¹ ^ n := by
              rw [pow_succ]
              field_simp
  intro x hx
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (x / Z) ((one_lt_inv₀ hk0).2 hk1)
  refine key n x hx ?_
  have := (div_lt_iff₀ hZ0).1 hn
  linarith

/-- A quadratic recursion with a Gaussian error term and contraction ratio above one half
upgrades decay to zero into stretched-exponential decay. -/
theorem quadRec_stretched_exp
    (G : ℝ → ℝ) (hG : Antitone G) (hG0 : ∀ x, 0 ≤ G x)
    (hlim : Tendsto G atTop (𝓝 0))
    (κ c₀ A B c x₀ : ℝ) (hκ : 1 / 2 < κ) (hκ1 : κ < 1) (hA : 0 ≤ A) (hB : 0 < B)
    (hc : 0 < c)
    (hrec : ∀ x, x₀ ≤ x → G x ≤ A * Real.exp (-c * x ^ 2) + B * G (κ * x - c₀) ^ 2) :
    ∃ C d β : ℝ, 0 < d ∧ 1 < β ∧ ∀ x, 0 ≤ x → G x ≤ C * Real.exp (-d * x ^ β) := by
  -- an intermediate contraction ratio `k` with `1 / 2 < k < κ`
  obtain ⟨k, hk_lo, hk_hi⟩ : ∃ k : ℝ, 1 / 2 < k ∧ k < κ :=
    ⟨(κ + 1 / 2) / 2, by linarith, by linarith⟩
  have hk1 : k < 1 := lt_trans hk_hi hκ1
  have hk0 : 0 < k := lt_trans (by norm_num) hk_lo
  -- the exponent `β` and the gap `h = 2 k ^ β - 1`
  obtain ⟨β, hβ1, hβ2, hβk⟩ := quadRec_exists_beta k hk_lo
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = 2 * k ^ β - 1 := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hh_def]; linarith
  have hkβ : 2 * k ^ β = 1 + h := by rw [hh_def]; ring
  -- the constant `ℓ ≥ 1` with `B * exp (-ℓ) ≤ 1 / 2`
  obtain ⟨ℓ, hℓ_def⟩ : ∃ ℓ : ℝ, ℓ = max 1 (2 * B) := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := hℓ_def ▸ le_max_left _ _
  have hℓ2B : 2 * B ≤ ℓ := hℓ_def ▸ le_max_right _ _
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hB' : B * Real.exp (-ℓ) ≤ 1 / 2 := by
    have h1 : ℓ + 1 ≤ Real.exp ℓ := Real.add_one_le_exp ℓ
    have hE : 0 < Real.exp ℓ := Real.exp_pos ℓ
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
    linarith
  have hshift := quadRec_shift_recursion G hG hG0 A B c κ k c₀ x₀ hB.le hk_hi hrec
  -- the starting point `Y`
  have hev : ∀ᶠ Y in atTop,
      (max x₀ (|c₀| / (κ - k)) ≤ Y ∧ 1 ≤ Y ∧ 2 * ℓ / (c * h) ≤ Y ∧ 4 * A / c ≤ Y) ∧
        G Y < Real.exp (-(ℓ / h)) := by
    refine Eventually.and ?_ (hlim.eventually (eventually_lt_nhds (Real.exp_pos _)))
    exact (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((eventually_ge_atTop _).and (eventually_ge_atTop _)))
  obtain ⟨Y, ⟨hY1, hY2, hY3, hY4⟩, hGY⟩ := hev.exists
  have hY0 : 0 < Y := lt_of_lt_of_le one_pos hY2
  obtain ⟨Z, hYZ⟩ : ∃ Z : ℝ, k * Z = Y := ⟨Y / k, by field_simp⟩
  have hZ0 : 0 < Z := by
    by_contra hneg
    have := mul_nonpos_of_nonneg_of_nonpos hk0.le (not_lt.1 hneg)
    linarith
  have hYZ' : Y ≤ Z := by
    rw [← hYZ]
    exact mul_le_of_le_one_left hZ0.le hk1.le
  have hZ1 : 1 ≤ Z := hY2.trans hYZ'
  have hZβ0 : 0 < Z ^ β := Real.rpow_pos_of_pos hZ0 β
  have hZY : Y ≤ Z ^ β := hYZ'.trans (Real.self_le_rpow_of_one_le hZ1 hβ1.le)
  -- the rate `d`
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = ℓ / (h * Z ^ β) := ⟨_, rfl⟩
  have hd : 0 < d := hd_def ▸ div_pos hℓ0 (mul_pos hh hZβ0)
  have hdZ : d * Z ^ β = ℓ / h := by
    rw [hd_def]
    field_simp
  have hℓ' : ℓ ≤ h * d * Z ^ β := by
    have : h * d * Z ^ β = ℓ := by
      rw [mul_assoc, hdZ]
      field_simp
    exact this.ge
  have hdc : d ≤ c / 2 := by
    have h2ℓ : 2 * ℓ ≤ Y * (c * h) := (div_le_iff₀ (mul_pos hc hh)).1 hY3
    have h3 : Y * (c * h) ≤ Z ^ β * (c * h) :=
      mul_le_mul_of_nonneg_right hZY (mul_pos hc hh).le
    rw [hd_def, div_le_iff₀ (mul_pos hh hZβ0)]
    linarith
  have hgauss : ∀ x, Z ≤ x →
      A * Real.exp (-c * x ^ 2) ≤ 1 / 2 * Real.exp (-d * x ^ β) := fun x hx =>
    quadRec_gaussian_step A c d β Z x hA hd.le hβ2.le hdc hZ1 hx
      (quadRec_gaussian_tail A c Z hc hZ1 (hY4.trans hYZ'))
  have hGY' : G Y ≤ Real.exp (-d * Z ^ β) := by
    have : -d * Z ^ β = -(ℓ / h) := by rw [neg_mul, hdZ]
    rw [this]
    exact hGY.le
  have hcore := quadRec_core G hG hG0 A B c k β d h ℓ Y Z hk0 hk1 (by linarith) hd hh hkβ hB'
    hB.le hY0 hYZ (fun x hx => hshift x (hY1.trans hx)) hGY' hℓ' hgauss
  -- the constant `C`
  refine ⟨max 1 (G 0 * Real.exp (d * Y ^ β)), d, β, hd, hβ1, ?_⟩
  intro x hx
  by_cases hxY : Y ≤ x
  · calc G x ≤ Real.exp (-d * x ^ β) := hcore x hxY
      _ = 1 * Real.exp (-d * x ^ β) := (one_mul _).symm
      _ ≤ max 1 (G 0 * Real.exp (d * Y ^ β)) * Real.exp (-d * x ^ β) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
  · have hxY' : x ≤ Y := (not_le.1 hxY).le
    have h1 : x ^ β ≤ Y ^ β := Real.rpow_le_rpow hx hxY' (by linarith)
    have h2 : d * x ^ β ≤ d * Y ^ β := mul_le_mul_of_nonneg_left h1 hd.le
    have h3 : Real.exp (-d * Y ^ β) ≤ Real.exp (-d * x ^ β) :=
      Real.exp_le_exp.2 (by linarith)
    have h4 : G 0 * Real.exp (d * Y ^ β) ≤ max 1 (G 0 * Real.exp (d * Y ^ β)) :=
      le_max_right _ _
    have h5 : G 0 = (G 0 * Real.exp (d * Y ^ β)) * Real.exp (-d * Y ^ β) := by
      have : d * Y ^ β + -d * Y ^ β = 0 := by ring
      rw [mul_assoc, ← Real.exp_add, this, Real.exp_zero, mul_one]
    calc G x ≤ G 0 := hG hx
      _ = (G 0 * Real.exp (d * Y ^ β)) * Real.exp (-d * Y ^ β) := h5
      _ ≤ max 1 (G 0 * Real.exp (d * Y ^ β)) * Real.exp (-d * x ^ β) :=
          mul_le_mul h4 h3 (Real.exp_nonneg _)
            ((mul_nonneg (hG0 0) (Real.exp_nonneg _)).trans h4)

end DOZZ.Proofs
