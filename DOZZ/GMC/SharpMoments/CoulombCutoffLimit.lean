/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CoulombCutoffDefs
public import DOZZ.GMC.SharpMoments.SeibergWeight
public import DOZZ.GMC.Moments.InfinityChart

/-! # Convergence of the single-chart regularized Coulomb weight

With the cutoff removed, the inverted-chart weight at `x⁻¹` is the Coulomb weight at `x`, so by the
partition of unity the single-chart regularized weight converges to the Coulomb weight. On a set
away from the roots and from infinity every softened factor is the unsoftened factor times
`exp w` with `|w|` controlled by `exp (-r)`, which gives the uniform convergence with an explicit
rate. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Inversion identities -/

/-- The norm of `1 - w * x⁻¹` in terms of `‖x - w‖`. -/
theorem coulombCutoffLimit_norm_one_sub_mul_inv {x w : ℂ} (hx : x ≠ 0) :
    ‖1 - w * x⁻¹‖ = ‖x - w‖ / ‖x‖ := by
  have h : 1 - w * x⁻¹ = (x - w) / x := by
    field_simp [hx]
  rw [h, norm_div]

/-- With the cutoff removed, the inverted-chart weight at `x⁻¹` is the Coulomb weight at `x`. -/
theorem coulombInfinityWeight_inv_eq_coulombWeight {N : ℕ} (γ : ℝ) (α : Fin N → ℝ)
    (z : Fin N → ℂ) (αinf : ℝ) {x : ℂ} (hx : x ≠ 0) :
    (∏ k, ENNReal.rpow (ENNReal.ofReal (normPlus x⁻¹ / ‖1 - z k * x⁻¹‖)) (γ * α k)) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x⁻¹ / ‖x⁻¹‖)) (γ * αinf) =
      coulombWeight γ α z αinf x := by
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h1 : ∀ k, normPlus x⁻¹ / ‖1 - z k * x⁻¹‖ = normPlus x / ‖x - z k‖ := by
    intro k
    rw [coulombCutoffLimit_norm_one_sub_mul_inv hx, normPlus_inv_identity hx]
    exact div_div_div_cancel_right₀ hxn _ _
  have h2 : normPlus x⁻¹ / ‖x⁻¹‖ = normPlus x := by
    rw [normPlus_inv_identity hx, norm_inv]
    field_simp
  unfold coulombWeight
  simp only [h1, h2]

/-! ### Softening multiplies a factor by an exponential -/

/-- `|exp w - 1| ≤ |w| exp |w|`. -/
theorem coulombCutoffLimit_abs_exp_sub_one_le (w : ℝ) :
    |Real.exp w - 1| ≤ |w| * Real.exp |w| := by
  rcases le_total 0 w with hw | hw
  · rw [abs_of_nonneg hw]
    have h1 : 1 ≤ Real.exp w := Real.one_le_exp hw
    have h2 : (-w + 1) * Real.exp w ≤ 1 := by
      calc (-w + 1) * Real.exp w ≤ Real.exp (-w) * Real.exp w :=
            mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-w)) (Real.exp_pos w).le
        _ = 1 := by rw [← Real.exp_add]; simp
    rw [abs_of_nonneg (by linarith)]
    linarith only [h2]
  · rw [abs_of_nonpos hw]
    have h1 : Real.exp w ≤ 1 := Real.exp_le_one_iff.mpr hw
    have h2 : w + 1 ≤ Real.exp w := Real.add_one_le_exp w
    have h3 : 1 ≤ Real.exp (-w) := Real.one_le_exp (by linarith)
    rw [abs_of_nonpos (by linarith)]
    linarith only [h2, mul_nonneg (neg_nonneg.2 hw) (sub_nonneg.2 h3)]

/-- Softening one factor `n / d` to `n / (d + δ)` multiplies it by an exponential `exp w` with
`|w| ≤ |e| δ / ρ2` as soon as `d ≥ ρ2 > 0`. -/
theorem coulombCutoffLimit_factor {n d δ ρ2 : ℝ} (e : ℝ) (hn : 0 < n) (hρ2 : 0 < ρ2)
    (hd : ρ2 ≤ d) (hδ : 0 < δ) :
    ∃ w : ℝ, |w| ≤ |e| * (δ / ρ2) ∧
      ENNReal.rpow (ENNReal.ofReal (n / (d + δ))) e =
        ENNReal.rpow (ENNReal.ofReal (n / d)) e * ENNReal.ofReal (Real.exp w) := by
  have hd0 : 0 < d := lt_of_lt_of_le hρ2 hd
  refine ⟨-(e * Real.log (1 + δ / d)), ?_, ?_⟩
  · rw [abs_neg, abs_mul]
    have ht : 0 ≤ δ / d := by positivity
    have hlog0 : 0 ≤ Real.log (1 + δ / d) := Real.log_nonneg (by linarith)
    have hlog1 : Real.log (1 + δ / d) ≤ δ / d := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + δ / d)
      linarith
    have hdd : δ / d ≤ δ / ρ2 := div_le_div_of_nonneg_left hδ.le hρ2 hd
    rw [abs_of_nonneg hlog0]
    exact mul_le_mul_of_nonneg_left (hlog1.trans hdd) (abs_nonneg e)
  · have h1 : 0 < n / (d + δ) := by positivity
    have h2 : 0 < n / d := by positivity
    rw [coulombWeight_rpow_ofReal h1, coulombWeight_rpow_ofReal h2,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg h2.le e)]
    congr 1
    have h3 : n / (d + δ) = n / d * (d / (d + δ)) := by field_simp
    have h4 : d / (d + δ) = (1 + δ / d)⁻¹ := by field_simp
    have h5 : (d / (d + δ)) ^ e = Real.exp (-(e * Real.log (1 + δ / d))) := by
      rw [h4, Real.rpow_def_of_pos (by positivity), Real.log_inv]
      congr 1
      ring
    rw [h3, Real.mul_rpow h2.le (by positivity), h5]

/-- Softening a finite product of factors multiplies it by one exponential. -/
theorem coulombCutoffLimit_prod {N : ℕ} {n δ ρ2 E : ℝ} (d e : Fin N → ℝ) (hn : 0 < n)
    (hρ2 : 0 < ρ2) (hd : ∀ k, ρ2 ≤ d k) (hδ : 0 < δ) (he : ∀ k, |e k| ≤ E) :
    ∃ w : ℝ, |w| ≤ N * E * (δ / ρ2) ∧
      ∏ k, ENNReal.rpow (ENNReal.ofReal (n / (d k + δ))) (e k) =
        (∏ k, ENNReal.rpow (ENNReal.ofReal (n / d k)) (e k)) * ENNReal.ofReal (Real.exp w) := by
  choose w hw hprod using fun k =>
    coulombCutoffLimit_factor (n := n) (d := d k) (δ := δ) (ρ2 := ρ2) (e k) hn hρ2 (hd k) hδ
  refine ⟨∑ k, w k, ?_, ?_⟩
  · calc |∑ k, w k| ≤ ∑ k, |w k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin N, E * (δ / ρ2) :=
        Finset.sum_le_sum fun k _ =>
          (hw k).trans (mul_le_mul_of_nonneg_right (he k) (by positivity))
      _ = N * E * (δ / ρ2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  · rw [Finset.prod_congr rfl fun k _ => hprod k, Finset.prod_mul_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le]

/-- The finite-chart softened weight is the Coulomb weight times an exponential. -/
theorem coulombCutoffLimit_finite_eq {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) {E ρ2 : ℝ} (hρ2 : 0 < ρ2) (hα : ∀ j, |γ * α j| ≤ E) {x : ℂ}
    (hxz : ∀ k, ρ2 ≤ ‖x - z k‖) :
    ∃ w : ℝ, |w| ≤ N * E * (Real.exp (-r) / ρ2) ∧
      coulombCutoffFiniteWeight γ α z αinf r x =
        coulombWeight γ α z αinf x * ENNReal.ofReal (Real.exp w) := by
  have hn : 0 < normPlus x := lt_of_lt_of_le one_pos (le_max_left _ _)
  obtain ⟨w, hw, hprod⟩ := coulombCutoffLimit_prod (n := normPlus x) (fun k => ‖x - z k‖)
    (fun k => γ * α k) hn hρ2 hxz (Real.exp_pos (-r)) hα
  refine ⟨w, hw, ?_⟩
  unfold coulombCutoffFiniteWeight coulombWeight
  rw [hprod, mul_right_comm]

/-- The inverted-chart softened weight at `x⁻¹` is the Coulomb weight at `x` times an
exponential. -/
theorem coulombCutoffLimit_infinity_eq {N : ℕ} (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ)
    (αinf r : ℝ) {E ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hα : ∀ j, |γ * α j| ≤ E)
    (hαinf : |γ * αinf| ≤ E) {x : ℂ} (hx : x ≠ 0) (hxρ : ‖x‖ ≤ 1 / ρ)
    (hxz : ∀ k, ρ ≤ ‖x - z k‖) :
    ∃ w : ℝ, |w| ≤ (N + 1) * E * (Real.exp (-r) / ρ ^ 2) ∧
      coulombCutoffInfinityWeight γ α z αinf r x⁻¹ =
        coulombWeight γ α z αinf x * ENNReal.ofReal (Real.exp w) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hρρ : ρ * ‖x‖ ≤ 1 := by
    calc ρ * ‖x‖ ≤ ρ * (1 / ρ) := mul_le_mul_of_nonneg_left hxρ hρ.le
      _ = 1 := by field_simp
  have hn : 0 < normPlus x⁻¹ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hd : ∀ k, ρ ^ 2 ≤ ‖1 - z k * x⁻¹‖ := by
    intro k
    rw [coulombCutoffLimit_norm_one_sub_mul_inv hx, le_div_iff₀ hxpos]
    calc ρ ^ 2 * ‖x‖ = ρ * (ρ * ‖x‖) := by ring
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hρρ hρ.le
      _ ≤ ‖x - z k‖ := by simpa using hxz k
  have hdinf : ρ ^ 2 ≤ ‖x⁻¹‖ := by
    rw [norm_inv, ← one_div, le_div_iff₀ hxpos]
    calc ρ ^ 2 * ‖x‖ = ρ * (ρ * ‖x‖) := by ring
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hρρ hρ.le
      _ ≤ 1 := by linarith
  obtain ⟨w₁, hw₁, hprod⟩ := coulombCutoffLimit_prod (n := normPlus x⁻¹)
    (fun k => ‖1 - z k * x⁻¹‖) (fun k => γ * α k) hn hρ2 hd (Real.exp_pos (-r)) hα
  obtain ⟨w₂, hw₂, hfac⟩ := coulombCutoffLimit_factor (n := normPlus x⁻¹) (d := ‖x⁻¹‖)
    (δ := Real.exp (-r)) (ρ2 := ρ ^ 2) (γ * αinf) hn hρ2 hdinf (Real.exp_pos (-r))
  refine ⟨w₁ + w₂, ?_, ?_⟩
  · calc |w₁ + w₂| ≤ |w₁| + |w₂| := abs_add_le _ _
      _ ≤ N * E * (Real.exp (-r) / ρ ^ 2) + E * (Real.exp (-r) / ρ ^ 2) :=
        add_le_add hw₁ ((hw₂).trans (mul_le_mul_of_nonneg_right hαinf (by positivity)))
      _ = (N + 1) * E * (Real.exp (-r) / ρ ^ 2) := by ring
  · unfold coulombCutoffInfinityWeight
    rw [hprod, hfac, ← coulombInfinityWeight_inv_eq_coulombWeight γ α z αinf hx, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring

/-! ### Combining the two charts -/

/-- A convex combination of two softened copies of `W` is bounded by the bound for `W` times
`exp c`. -/
theorem coulombCutoffLimit_combine_le {W : ℝ≥0∞} {Wb c δ wF wG : ℝ} {fw iw : ℝ≥0}
    (hW : W ≤ ENNReal.ofReal Wb) (hWb : 0 ≤ Wb) (hc : 0 ≤ c) (hδ1 : δ ≤ 1)
    (hfi : fw + iw = 1) (hF : |wF| ≤ c * δ) (hG : |wG| ≤ c * δ) :
    (fw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wF)) +
        (iw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wG)) ≤ ENNReal.ofReal (Wb * Real.exp c) := by
  have hcδ : c * δ ≤ c := mul_le_of_le_one_right hc hδ1
  have hwF : wF ≤ c := (le_abs_self wF).trans (hF.trans hcδ)
  have hwG : wG ≤ c := (le_abs_self wG).trans (hG.trans hcδ)
  have hone : (fw : ℝ≥0∞) + (iw : ℝ≥0∞) = 1 := by
    rw [← ENNReal.coe_add, hfi, ENNReal.coe_one]
  calc (fw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wF)) +
        (iw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wG))
      ≤ (fw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp c)) +
        (iw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp c)) := by
        gcongr
    _ = W * ENNReal.ofReal (Real.exp c) := by rw [← add_mul, hone, one_mul]
    _ ≤ ENNReal.ofReal Wb * ENNReal.ofReal (Real.exp c) := by gcongr
    _ = ENNReal.ofReal (Wb * Real.exp c) := (ENNReal.ofReal_mul hWb).symm

/-- A convex combination of two softened copies of `W` is within `Wb * (c * exp c) * δ` of `W`. -/
theorem coulombCutoffLimit_combine_sub {W : ℝ≥0∞} {Wb c δ wF wG : ℝ} {fw iw : ℝ≥0}
    (hW : W ≤ ENNReal.ofReal Wb) (hWb : 0 ≤ Wb) (hc : 0 ≤ c) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hfi : fw + iw = 1) (hF : |wF| ≤ c * δ) (hG : |wG| ≤ c * δ) :
    |((fw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wF)) +
        (iw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wG))).toReal - W.toReal| ≤
      Wb * (c * Real.exp c) * δ := by
  have hWtop : W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW
  have h1 : (fw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wF)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hWtop ENNReal.ofReal_ne_top)
  have h2 : (iw : ℝ≥0∞) * (W * ENNReal.ofReal (Real.exp wG)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top hWtop ENNReal.ofReal_ne_top)
  have e1 : (ENNReal.ofReal (Real.exp wF)).toReal = Real.exp wF :=
    ENNReal.toReal_ofReal (Real.exp_pos _).le
  have e2 : (ENNReal.ofReal (Real.exp wG)).toReal = Real.exp wG :=
    ENNReal.toReal_ofReal (Real.exp_pos _).le
  rw [ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal, e1, e2]
  have hfi' : (fw : ℝ) + iw = 1 := by exact_mod_cast hfi
  have hfw : 0 ≤ (fw : ℝ) := fw.coe_nonneg
  have hiw : 0 ≤ (iw : ℝ) := iw.coe_nonneg
  have hWr0 : 0 ≤ W.toReal := ENNReal.toReal_nonneg
  have hWrb : W.toReal ≤ Wb := ENNReal.toReal_le_of_le_ofReal hWb hW
  have hcδ : c * δ ≤ c := mul_le_of_le_one_right hc hδ1
  have hkey : ∀ w : ℝ, |w| ≤ c * δ → |Real.exp w - 1| ≤ c * δ * Real.exp c := fun w hw =>
    (coulombCutoffLimit_abs_exp_sub_one_le w).trans
      (mul_le_mul hw (Real.exp_le_exp.mpr (hw.trans hcδ)) (Real.exp_pos _).le
        ((abs_nonneg _).trans hw))
  have hnn : 0 ≤ c * δ * Real.exp c := by positivity
  have hdiff : (fw : ℝ) * (W.toReal * Real.exp wF) + (iw : ℝ) * (W.toReal * Real.exp wG) -
      W.toReal = (fw : ℝ) * W.toReal * (Real.exp wF - 1) +
        (iw : ℝ) * W.toReal * (Real.exp wG - 1) := by
    linear_combination W.toReal * hfi'
  rw [hdiff]
  calc |(fw : ℝ) * W.toReal * (Real.exp wF - 1) + (iw : ℝ) * W.toReal * (Real.exp wG - 1)|
      ≤ |(fw : ℝ) * W.toReal * (Real.exp wF - 1)| +
        |(iw : ℝ) * W.toReal * (Real.exp wG - 1)| := abs_add_le _ _
    _ = (fw : ℝ) * W.toReal * |Real.exp wF - 1| + (iw : ℝ) * W.toReal * |Real.exp wG - 1| := by
        simp only [abs_mul, abs_of_nonneg hfw, abs_of_nonneg hiw, abs_of_nonneg hWr0]
    _ ≤ (fw : ℝ) * W.toReal * (c * δ * Real.exp c) +
        (iw : ℝ) * W.toReal * (c * δ * Real.exp c) := by
        gcongr
        · exact hkey _ hF
        · exact hkey _ hG
    _ = W.toReal * (c * δ * Real.exp c) := by
        linear_combination (W.toReal * (c * δ * Real.exp c)) * hfi'
    _ ≤ Wb * (c * δ * Real.exp c) := mul_le_mul_of_nonneg_right hWrb hnn
    _ = Wb * (c * Real.exp c) * δ := by ring

/-! ### Uniform convergence -/

/-- Uniform convergence of the single-chart weight to the Coulomb weight on sets away from the
roots and from infinity. -/
theorem coulombCutoffWeight_sub_coulombWeight_le (partition : GMCChartPartition) (N : ℕ)
    {Zs E ρ : ℝ} (hZs : 0 ≤ Zs) (hE : 0 ≤ E) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf r : ℝ) (x : ℂ),
      0 ≤ r → ∑ j, ‖z j‖ ≤ Zs → (∀ j, |γ * α j| ≤ E) → |γ * αinf| ≤ E →
      ‖x‖ ≤ 1 / ρ → (∀ k, ρ ≤ ‖x - z k‖) → x ≠ 0 →
      coulombCutoffWeight partition γ α z αinf r x ≤ ENNReal.ofReal L ∧
      coulombWeight γ α z αinf x ≤ ENNReal.ofReal L ∧
      |(coulombCutoffWeight partition γ α z αinf r x).toReal -
          (coulombWeight γ α z αinf x).toReal| ≤ L * Real.exp (-r) := by
  set S : ℝ := (N + 1) * E with hS
  set c : ℝ := S / ρ ^ 2 with hc
  set L₀ : ℝ := (1 + 1 / ρ + Zs) / ρ with hL₀
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hS0 : 0 ≤ S := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hL₀1 : 1 ≤ L₀ := by
    rw [hL₀, le_div_iff₀ hρ]
    have : 0 ≤ 1 / ρ := by positivity
    linarith
  have hexp1 : 1 ≤ Real.exp c := Real.one_le_exp hc0
  have hK : 0 ≤ c * Real.exp c := by positivity
  have hL₀0 : 0 ≤ L₀ ^ S := by positivity
  refine ⟨L₀ ^ S * (Real.exp c + c * Real.exp c), by positivity, ?_⟩
  intro γ α z αinf r x hr hz hα hαinf hxρ hxz hx0
  have hδ : 0 < Real.exp (-r) := Real.exp_pos _
  have hδ1 : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexpo : ∑ j, |γ * α j| + |γ * αinf| ≤ S := by
    calc ∑ j, |γ * α j| + |γ * αinf| ≤ ∑ _j : Fin N, E + E :=
          add_le_add (Finset.sum_le_sum fun j _ => hα j) hαinf
      _ = S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hS]
        ring
  have hW : coulombWeight γ α z αinf x ≤ ENNReal.ofReal (L₀ ^ S) := by
    refine (coulombWeight_le_bulk γ α z αinf hρ hρ1 (by positivity : (0 : ℝ) ≤ 1 / ρ) hxρ
      hxz).trans (ENNReal.ofReal_le_ofReal ?_)
    calc ((1 + 1 / ρ + ∑ j, ‖z j‖) / ρ) ^ (∑ j, |γ * α j| + |γ * αinf|)
        ≤ L₀ ^ (∑ j, |γ * α j| + |γ * αinf|) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          rw [hL₀]
          gcongr
      _ ≤ L₀ ^ S := Real.rpow_le_rpow_of_exponent_le hL₀1 hexpo
  have hρρ : ρ ^ 2 ≤ ρ := pow_le_of_le_one hρ.le hρ1 two_ne_zero
  obtain ⟨wF, hwF, hF⟩ := coulombCutoffLimit_finite_eq γ α z αinf r hρ2 hα
    (fun k => hρρ.trans (hxz k))
  obtain ⟨wG, hwG, hG⟩ := coulombCutoffLimit_infinity_eq γ α z αinf r hρ hρ1 hα hαinf hx0 hxρ
    hxz
  have hwF' : |wF| ≤ c * Real.exp (-r) := by
    refine hwF.trans ?_
    rw [hc, hS]
    have : (N : ℝ) * E ≤ (N + 1) * E := by linarith only [hE]
    calc (N : ℝ) * E * (Real.exp (-r) / ρ ^ 2) ≤ (N + 1) * E * (Real.exp (-r) / ρ ^ 2) := by
          gcongr
      _ = (N + 1) * E / ρ ^ 2 * Real.exp (-r) := by ring
  have hwG' : |wG| ≤ c * Real.exp (-r) := by
    refine hwG.trans (le_of_eq ?_)
    rw [hc, hS]
    ring
  have hfi : partition.finiteWeight x + partition.infinityWeight x⁻¹ = 1 :=
    partition.sum_one x hx0
  have hWc : coulombCutoffWeight partition γ α z αinf r x =
      (partition.finiteWeight x : ℝ≥0∞) *
          (coulombWeight γ α z αinf x * ENNReal.ofReal (Real.exp wF)) +
        (partition.infinityWeight x⁻¹ : ℝ≥0∞) *
          (coulombWeight γ α z αinf x * ENNReal.ofReal (Real.exp wG)) := by
    unfold coulombCutoffWeight
    rw [hF, hG]
  have h1 := coulombCutoffLimit_combine_le hW hL₀0 hc0 hδ1 hfi hwF' hwG'
  have h2 := coulombCutoffLimit_combine_sub hW hL₀0 hc0 hδ hδ1 hfi hwF' hwG'
  rw [hWc]
  refine ⟨h1.trans (ENNReal.ofReal_le_ofReal ?_), hW.trans (ENNReal.ofReal_le_ofReal ?_),
    h2.trans ?_⟩
  · have : L₀ ^ S * Real.exp c ≤ L₀ ^ S * (Real.exp c + c * Real.exp c) := by
      gcongr
      linarith
    exact this
  · have : L₀ ^ S * 1 ≤ L₀ ^ S * (Real.exp c + c * Real.exp c) := by
      gcongr
      linarith
    simpa using this
  · have : L₀ ^ S * (c * Real.exp c) ≤ L₀ ^ S * (Real.exp c + c * Real.exp c) := by
      gcongr
      linarith
    exact mul_le_mul_of_nonneg_right this hδ.le

end DOZZ.Proofs
