/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.FourPointWardExt
public import DOZZ.FourPoint.BPZ.GCutoff
public import DOZZ.FourPoint.BPZ.WirtingerG

/-! # The four-point Ward identity for the rational function `g(x) = x (x − 1)/(z − x)`

For a real-linear functional `ℓ : ℂ →L[ℝ] ℝ` (for instance `Re` or `Im`) we apply the extension
theorem `bpz_fourPoint_ward_extend` to the test function `φ = ℓ ∘ g`, which has a simple pole at
`z` and is approximated by the compactly supported smooth truncations
`φₙ = ℓ (g χₙ)` of `GCutoff`.

* `bpz_g_fderiv_bound` : `|∂_v (ℓ g · k̃)| ≤ A (1 + |x − z|^{-2}) k̃`;
* `bpz_g_kern_bound` : `|(ℓ g(x) − ℓ g(y)) K_v(x − y)| ≤ A (1 + |x − z|^{-2} + |y − z|^{-2})`;
* `bpz_fourPoint_ward_g` : the Ward identity for `ℓ ∘ g`.

The truncations satisfy the same two bounds with a constant independent of `n`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-! ### Elementary facts -/


/-- The test function `ℓ ∘ g` is measurable. -/
theorem bpzWardG_measurable (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) : Measurable (fun x => ℓ (bpzG z x)) := by
  have h : Measurable (bpzG z) := by
    unfold bpzG
    fun_prop
  exact ℓ.continuous.measurable.comp h

/-- The truncation `ℓ (g χₙ)` is `C¹`. -/
theorem bpzWardG_contDiff (z : ℂ) (n : ℕ) (ℓ : ℂ →L[ℝ] ℝ) :
    ContDiff ℝ 1 (fun x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ))) :=
  ℓ.contDiff.comp ((contDiff_bpzG_mul_cutoff z n).of_le (by simp))

/-- The support of the truncation lies in the support of the cutoff. -/
theorem bpzWardG_support_subset (z : ℂ) (n : ℕ) (ℓ : ℂ →L[ℝ] ℝ) :
    Function.support (fun x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ))) ⊆
      tsupport (bpzCutoffSeq z n) := by
  intro x hx
  refine subset_tsupport _ ?_
  intro h0
  apply hx
  simp [h0]

/-- The truncation `ℓ (g χₙ)` has compact support. -/
theorem bpzWardG_hasCompactSupport (z : ℂ) (n : ℕ) (ℓ : ℂ →L[ℝ] ℝ) :
    HasCompactSupport (fun x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ))) :=
  (hasCompactSupport_bpzCutoffSeq z n).mono' (bpzWardG_support_subset z n ℓ)

/-- The truncation `ℓ (g χₙ)` is supported away from `0`, `1`, `z`. -/
theorem bpzWardG_tsupport_subset (z : ℂ) (n : ℕ) (ℓ : ℂ →L[ℝ] ℝ) :
    tsupport (fun x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ))) ⊆ bpzRegular z :=
  (closure_minimal (bpzWardG_support_subset z n ℓ) (isClosed_tsupport _)).trans
    (tsupport_bpzCutoffSeq_subset z n)

/-- Near every regular point the truncations eventually agree with `ℓ ∘ g`. -/
theorem bpzWardG_eventually_eq (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) {x : ℂ} (hx : x ∈ bpzRegular z) :
    ∀ᶠ n in atTop, (fun x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ))) =ᶠ[𝓝 x]
      fun x => ℓ (bpzG z x) := by
  filter_upwards [bpzCutoffSeq_eventually_eq_one hx] with n hn
  filter_upwards [hn] with y hy
  simp [hy]

/-! ### The gradient bound -/

/-- The pointwise gradient bound for a product `ℓ (F y) · k̃ y`, in terms of a bound `B₁` for the
quantity `‖F x‖ (1/‖x − z‖ + 1/‖x‖ + 1/‖x − 1‖)` and a bound `B₂` for the gradient of `F`. -/
theorem bpzWardG_abs_fderiv_le {z x : ℂ} (hx : x ∈ bpzRegular z) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    {F : ℂ → ℂ} (hF : DifferentiableAt ℝ F x) {B₁ B₂ : ℝ}
    (hB₁ : ‖F x‖ / ‖x - z‖ + ‖F x‖ / ‖x‖ + ‖F x‖ / ‖x - 1‖ ≤ B₁)
    (hB₂ : ‖fderiv ℝ F x‖ ≤ B₂) :
    |fderiv ℝ (fun y => ℓ (F y) * bpzTildeWeight γ χ α₁ α₂ z y) x v| ≤
      ‖ℓ‖ * ‖v‖ * ((|γ * χ| + |γ * α₁| + |γ * α₂|) * B₁ + B₂) *
        bpzTildeWeight γ χ α₁ α₂ z x := by
  obtain ⟨L, hL, -, hLn⟩ :=
    bpz_tildeWeight_hasFDerivAt (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hx
  have hℓF : HasFDerivAt (fun y => ℓ (F y)) (ℓ.comp (fderiv ℝ F x)) x :=
    ℓ.hasFDerivAt.comp x hF.hasFDerivAt
  have hprod : HasFDerivAt (fun y => ℓ (F y) * bpzTildeWeight γ χ α₁ α₂ z y)
      (ℓ (F x) • L + bpzTildeWeight γ χ α₁ α₂ z x • ℓ.comp (fderiv ℝ F x)) x := hℓF.mul hL
  rw [hprod.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  set t : ℝ := bpzTildeWeight γ χ α₁ α₂ z x with ht
  have ht0 : 0 ≤ t := bpzTildeWeight_nonneg z x
  set S : ℝ := |γ * χ| / ‖x - z‖ + |γ * α₁| / ‖x‖ + |γ * α₂| / ‖x - 1‖ with hS
  set C : ℝ := |γ * χ| + |γ * α₁| + |γ * α₂| with hC
  have hFS : ‖F x‖ * S ≤ C * B₁ := by
    have e : ‖F x‖ * S = |γ * χ| * (‖F x‖ / ‖x - z‖) + |γ * α₁| * (‖F x‖ / ‖x‖) +
        |γ * α₂| * (‖F x‖ / ‖x - 1‖) := by
      rw [hS]
      ring
    have ha : 0 ≤ ‖F x‖ / ‖x - z‖ := by positivity
    have hb : 0 ≤ ‖F x‖ / ‖x‖ := by positivity
    have hc : 0 ≤ ‖F x‖ / ‖x - 1‖ := by positivity
    have hp : 0 ≤ |γ * χ| := abs_nonneg _
    have hq : 0 ≤ |γ * α₁| := abs_nonneg _
    have hr : 0 ≤ |γ * α₂| := abs_nonneg _
    have h1 : |γ * χ| * (‖F x‖ / ‖x - z‖) + |γ * α₁| * (‖F x‖ / ‖x‖) +
        |γ * α₂| * (‖F x‖ / ‖x - 1‖) ≤
        C * (‖F x‖ / ‖x - z‖ + ‖F x‖ / ‖x‖ + ‖F x‖ / ‖x - 1‖) := by
      rw [hC]
      linarith [mul_nonneg hq ha, mul_nonneg hr ha, mul_nonneg hp hb, mul_nonneg hr hb,
        mul_nonneg hp hc, mul_nonneg hq hc]
    rw [e]
    exact h1.trans (mul_le_mul_of_nonneg_left hB₁ (by positivity))
  have hℓ1 : |ℓ (F x)| ≤ ‖ℓ‖ * ‖F x‖ := by
    have := ℓ.le_opNorm (F x)
    rwa [Real.norm_eq_abs] at this
  have hL1 : |L v| ≤ ‖L‖ * ‖v‖ := by
    have := L.le_opNorm v
    rwa [Real.norm_eq_abs] at this
  have hℓ2 : |ℓ (fderiv ℝ F x v)| ≤ ‖ℓ‖ * (‖fderiv ℝ F x‖ * ‖v‖) := by
    have h1 := ℓ.le_opNorm (fderiv ℝ F x v)
    have h2 := (fderiv ℝ F x).le_opNorm v
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have hLt : ‖L‖ ≤ t * S := hLn
  calc |ℓ (F x) * L v + t * ℓ (fderiv ℝ F x v)|
      ≤ |ℓ (F x) * L v| + |t * ℓ (fderiv ℝ F x v)| := abs_add_le _ _
    _ = |ℓ (F x)| * |L v| + t * |ℓ (fderiv ℝ F x v)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ht0]
    _ ≤ (‖ℓ‖ * ‖F x‖) * (‖L‖ * ‖v‖) + t * (‖ℓ‖ * (‖fderiv ℝ F x‖ * ‖v‖)) :=
        add_le_add (mul_le_mul hℓ1 hL1 (abs_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left hℓ2 ht0)
    _ ≤ (‖ℓ‖ * ‖F x‖) * ((t * S) * ‖v‖) + t * (‖ℓ‖ * (B₂ * ‖v‖)) := by gcongr
    _ = ‖ℓ‖ * ‖v‖ * t * (‖F x‖ * S) + ‖ℓ‖ * ‖v‖ * t * B₂ := by ring
    _ ≤ ‖ℓ‖ * ‖v‖ * t * (C * B₁) + ‖ℓ‖ * ‖v‖ * t * B₂ := by gcongr
    _ = ‖ℓ‖ * ‖v‖ * (C * B₁ + B₂) * t := by ring

/-- A uniform gradient bound for a family `F i` dominated by `g`, with gradients bounded by the
singular weight. -/
theorem bpzWardG_exists_fderiv_bound {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    {ι : Type*} (F : ι → ℂ → ℂ) {A₁ : ℝ} (hA₁ : 0 ≤ A₁)
    (hdiff : ∀ i, ∀ x ∈ bpzRegular z, DifferentiableAt ℝ (F i) x)
    (hdom : ∀ i x, ‖F i x‖ ≤ ‖bpzG z x‖)
    (hgrad : ∀ i, ∀ x ∈ bpzRegular z,
      ‖fderiv ℝ (F i) x‖ ≤ A₁ * (1 + ‖x - z‖ ^ (-2 : ℝ))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ i, ∀ x ∈ bpzRegular z,
      |fderiv ℝ (fun y => ℓ (F i y) * bpzTildeWeight γ χ α₁ α₂ z y) x v| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzTildeWeight γ χ α₁ α₂ z x := by
  obtain ⟨A₂, hA₂0, hA₂⟩ := norm_bpzG_div_le hz0 hz1
  refine ⟨‖ℓ‖ * ‖v‖ * ((|γ * χ| + |γ * α₁| + |γ * α₂|) * A₂ + A₁), by positivity, ?_⟩
  intro i x hx
  have hd := hdom i x
  have hb := bpzWardG_abs_fderiv_le (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hx ℓ v
    (hdiff i x hx) (B₁ := A₂ * (1 + ‖x - z‖ ^ (-2 : ℝ))) (B₂ := A₁ * (1 + ‖x - z‖ ^ (-2 : ℝ)))
    (le_trans (by gcongr) (hA₂ x hx.2.2 hx.1 hx.2.1)) (hgrad i x hx)
  refine hb.trans (le_of_eq ?_)
  ring

/-- The truncations `ℓ (g χₙ)` satisfy the gradient bound uniformly in `n`. -/
theorem bpzWardG_fderiv_bound_trunc {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ∀ x ∈ bpzRegular z,
      |fderiv ℝ (fun x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ)) *
          bpzTildeWeight γ χ α₁ α₂ z x) x v| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzTildeWeight γ χ α₁ α₂ z x := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := norm_fderiv_bpzG_mul_cutoff_le hz0 hz1
  exact bpzWardG_exists_fderiv_bound (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hz0 hz1 ℓ v
    (fun n x => bpzG z x * (bpzCutoffSeq z n x : ℂ)) hA₁0
    (fun n x _ => ((contDiff_bpzG_mul_cutoff z n).differentiable (by simp)) x)
    (fun n x => by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (bpzCutoffSeq_nonneg z n x)]
      exact mul_le_of_le_one_right (norm_nonneg _) (bpzCutoffSeq_le_one z n x))
    (fun n x hx => hA₁ n x hx.2.2)

/-- Gradient bound for the Ward test function `ℓ ∘ g` against `k̃`. -/
theorem bpz_g_fderiv_bound {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ bpzRegular z,
      |fderiv ℝ (fun x => ℓ (bpzG z x) * bpzTildeWeight γ χ α₁ α₂ z x) x v| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzTildeWeight γ χ α₁ α₂ z x := by
  obtain ⟨A, hA0, hA⟩ := bpzWardG_fderiv_bound_trunc (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    hz0 hz1 ℓ v
  refine ⟨A, hA0, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := (bpzWardG_eventually_eq z ℓ hx).exists
  have hev : (fun y => ℓ (bpzG z y * (bpzCutoffSeq z n y : ℂ)) *
      bpzTildeWeight γ χ α₁ α₂ z y) =ᶠ[𝓝 x] fun y => ℓ (bpzG z y) *
        bpzTildeWeight γ χ α₁ α₂ z y := by
    filter_upwards [hn] with y hy
    rw [hy]
  rw [← hev.fderiv_eq]
  exact hA n x hx

/-! ### The kernel bound -/

/-- A Lipschitz-type bound `‖a − b‖ ≤ B ‖x − y‖` gives a bound for the kernel pairing. -/
theorem bpzWardG_abs_sub_mul_kern_le (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) {a b x y : ℂ} {B : ℝ}
    (hB : 0 ≤ B) (h : ‖a - b‖ ≤ B * ‖x - y‖) :
    |(ℓ a - ℓ b) * bpzKern v (x - y)| ≤ ‖ℓ‖ * ‖v‖ * B := by
  have hnn : 0 ≤ ‖ℓ‖ * ‖v‖ * B := by positivity
  rcases eq_or_ne x y with rfl | hxy
  · rw [sub_self, bpzKern_zero, mul_zero, abs_zero]
    exact hnn
  · have hd : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    have h1 : |ℓ a - ℓ b| ≤ ‖ℓ‖ * (B * ‖x - y‖) := by
      rw [← map_sub]
      calc |ℓ (a - b)| = ‖ℓ (a - b)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖ℓ‖ * ‖a - b‖ := ℓ.le_opNorm _
        _ ≤ ‖ℓ‖ * (B * ‖x - y‖) := by gcongr
    have h2 := abs_bpzKern_le v (x - y)
    rw [abs_mul]
    calc |ℓ a - ℓ b| * |bpzKern v (x - y)| ≤ (‖ℓ‖ * (B * ‖x - y‖)) * (‖v‖ / ‖x - y‖) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ‖ℓ‖ * ‖v‖ * B := by field_simp

/-- The truncations `ℓ (g χₙ)` satisfy the kernel bound uniformly in `n`. -/
theorem bpzWardG_kern_bound_trunc {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ)) - ℓ (bpzG z y * (bpzCutoffSeq z n y : ℂ))) *
          bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := norm_bpzG_mul_cutoff_sub_le hz0 hz1
  refine ⟨‖ℓ‖ * ‖v‖ * A, by positivity, fun n x hx y hy => ?_⟩
  have hs : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  have ht : 0 ≤ ‖y - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  have h := bpzWardG_abs_sub_mul_kern_le ℓ v (x := x) (y := y)
    (B := A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)))
    (by positivity) (hA n x y hx.2.2 hy.2.2)
  refine h.trans (le_of_eq ?_)
  ring

/-- Kernel bound for the Ward test function `ℓ ∘ g`. -/
theorem bpz_g_kern_bound {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)) := by
  obtain ⟨A, hA0, hA⟩ := bpzWardG_kern_bound_trunc hz0 hz1 ℓ v
  refine ⟨A, hA0, fun x hx y hy => ?_⟩
  obtain ⟨n, hnx, hny⟩ := ((bpzWardG_eventually_eq z ℓ hx).and
    (bpzWardG_eventually_eq z ℓ hy)).exists
  have h := hA n x hx y hy
  rwa [hnx.eq_of_nhds, hny.eq_of_nhds] at h

/-! ### The Ward identity for `ℓ ∘ g` -/

/-- The Ward identity for the test function `ℓ ∘ g`, `g(x) = x(x-1)/(z-x)`. -/
theorem bpz_fourPoint_ward_g {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 0 ≤ fourPointSExp γ (-χ) α₁ α₂ α₃)
    {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∫ ω, (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-(fourPointSExp γ (-χ) α₁ α₂ α₃ + 1)) *
        ∫ x, fderiv ℝ (fun x => ℓ (bpzG z x) * bpzTildeWeight γ χ α₁ α₂ z x) x v *
          normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) ∂M ω ∂P =
      ∫ ω, (fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) *
        ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^
          (-(fourPointSExp γ (-χ) α₁ α₂ α₃ + 1) - 1) *
        (γ ^ 2 * ∫ x, ∫ y, (ℓ (bpzG z x) - ℓ (bpzG z y)) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x *
          bpzSoftWeight γ χ α₁ α₂ α₃ 0 z y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω)) ∂P := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := bpzWardG_fderiv_bound_trunc (γ := γ) (χ := χ) (α₁ := α₁)
    (α₂ := α₂) hz0 hz1 ℓ v
  obtain ⟨A₂, hA₂0, hA₂⟩ := bpzWardG_kern_bound_trunc hz0 hz1 ℓ v
  refine bpz_fourPoint_ward_extend P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hs hz0 hz1
    (φ := fun x => ℓ (bpzG z x)) (φn := fun n x => ℓ (bpzG z x * (bpzCutoffSeq z n x : ℂ)))
    (fun n => bpzWardG_contDiff z n ℓ) (fun n => bpzWardG_hasCompactSupport z n ℓ)
    (fun n => bpzWardG_tsupport_subset z n ℓ) (bpzWardG_measurable z ℓ)
    (fun x hx => bpzWardG_eventually_eq z ℓ hx) v (A := A₁ + A₂) ?_ ?_
  · intro n x hx
    refine (hA₁ n x hx).trans ?_
    have h1 : 0 ≤ 1 + ‖x - z‖ ^ (-2 : ℝ) := by positivity
    have h2 := bpzTildeWeight_nonneg (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) z x
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) h1) h2
  · intro n x hx y hy
    refine (hA₂ n x hx y hy).trans ?_
    have h1 : 0 ≤ 1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right (by linarith) h1

end DOZZ.Proofs
