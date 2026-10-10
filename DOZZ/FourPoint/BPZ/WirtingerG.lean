/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.FourPointWard

/-! # Wirtinger derivatives of the Ward-identity weights

Deterministic derivative computations in the plane, used for the Ward identity with the rational
function `g(x) = x (x - 1) / (z - x)`:

* the real derivative of `x ↦ ‖x − c‖ ^ p` and its Wirtinger combination
  `(p/2) ‖x − c‖^p / (x − c)`;
* the derivative of the degenerate four-point weight `k̃`, its Wirtinger form and its norm bound;
* the complex derivative of `g`, and the Wirtinger derivative of the products `Re g · k̃`,
  `Im g · k̃`, together with the partial-fraction form of its coefficient;
* the complex combination of the limit kernels `K_1`, `K_I`, and the difference quotient of `g`.
-/

@[expose] public section

namespace DOZZ.Proofs

/-- The rational function of the Ward identity (same as in GCutoff, defined here independently). -/
noncomputable def bpzGfun (z x : ℂ) : ℂ := x * (x - 1) / (z - x)

/-- Real derivative of `x ↦ ‖x − c‖ ^ p` away from `c`. -/
theorem bpz_hasFDerivAt_norm_sub_rpow (c : ℂ) (p : ℝ) {x : ℂ} (hx : x ≠ c) :
    HasFDerivAt (fun y => ‖y - c‖ ^ p)
      ((p * ‖x - c‖ ^ (p - 2)) • innerSL ℝ (x - c)) x := by
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have h1 : HasFDerivAt (fun y : ℂ => y - c) (ContinuousLinearMap.id ℝ ℂ) x :=
    (hasFDerivAt_id x).sub_const c
  have h2 : HasFDerivAt (fun y : ℂ => ‖y - c‖ ^ 2) (2 • innerSL ℝ (x - c)) x := by
    have := ((hasStrictFDerivAt_norm_sq (x - c)).hasFDerivAt).comp x h1
    rwa [ContinuousLinearMap.comp_id] at this
  have h3 := h2.rpow_const (p := p / 2) (Or.inl (pow_ne_zero 2 hn.ne'))
  have e : (fun y : ℂ => ‖y - c‖ ^ p) = fun y => (‖y - c‖ ^ 2) ^ (p / 2) := by
    funext y
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    push_cast
    ring
  have e2 : (‖x - c‖ ^ 2) ^ (p / 2 - 1) = ‖x - c‖ ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    push_cast
    ring
  rw [e]
  refine h3.congr_fderiv ?_
  rw [e2]
  ext h
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
  ring

/-- `(Re u − i Im u) · u = ‖u‖²`, i.e. `conj u · u = ‖u‖²`. -/
theorem bpz_conj_mul_self (u : ℂ) :
    ((u.re : ℂ) - Complex.I * (u.im : ℂ)) * u = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext
  · simp
  · simp
    ring

/-- The Wirtinger combination of the derivative of `x ↦ ‖x − c‖ ^ p` is
`(p / 2) ‖x − c‖ ^ p / (x − c)`. -/
theorem bpz_wirtinger_norm_sub_rpow (c : ℂ) (p : ℝ) {x : ℂ} (hx : x ≠ c) :
    ((((p * ‖x - c‖ ^ (p - 2)) • innerSL ℝ (x - c)) 1 : ℝ) - Complex.I *
      (((p * ‖x - c‖ ^ (p - 2)) • innerSL ℝ (x - c)) Complex.I : ℝ)) / 2 =
      ((p / 2 * ‖x - c‖ ^ p : ℝ) : ℂ) / (x - c) := by
  have hu : x - c ≠ 0 := sub_ne_zero.mpr hx
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr hu
  have hpow : ‖x - c‖ ^ p = ‖x - c‖ ^ (p - 2) * ‖x - c‖ ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]
    congr 1
    push_cast
    ring
  simp only [smul_apply, smul_eq_mul, bpzSoft_innerSL_apply, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  rw [hpow, eq_div_iff hu]
  have key := bpz_conj_mul_self (x - c)
  push_cast at key ⊢
  linear_combination ((p : ℂ) * ((‖x - c‖ ^ (p - 2) : ℝ) : ℂ) / 2) * key

/-- The Wirtinger combination `(L 1 − i L i) / 2` of a real-linear functional on `ℂ`. -/
noncomputable def bpzWirt (L : ℂ →L[ℝ] ℝ) : ℂ := ((L 1 : ℂ) - Complex.I * (L Complex.I : ℂ)) / 2

/-- The Wirtinger combination is additive. -/
theorem bpzWirt_add (L M : ℂ →L[ℝ] ℝ) : bpzWirt (L + M) = bpzWirt L + bpzWirt M := by
  unfold bpzWirt
  simp only [add_apply]
  push_cast
  ring

/-- The Wirtinger combination is homogeneous for real scalars. -/
theorem bpzWirt_smul (a : ℝ) (L : ℂ →L[ℝ] ℝ) : bpzWirt (a • L) = (a : ℂ) * bpzWirt L := by
  unfold bpzWirt
  simp only [smul_apply, smul_eq_mul]
  push_cast
  ring

/-- The operator norm of the derivative of `y ↦ ‖y − c‖ ^ p`. -/
theorem bpz_norm_normSubRpowDeriv (c : ℂ) (p : ℝ) {x : ℂ} (hx : x ≠ c) :
    ‖(p * ‖x - c‖ ^ (p - 2)) • innerSL ℝ (x - c)‖ = |p| * ‖x - c‖ ^ p / ‖x - c‖ := by
  have hn : 0 < ‖x - c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hn _), Real.rpow_sub hn, Real.rpow_two]
  field_simp

/-- The Wirtinger combination of the derivative of a product of three factors. -/
theorem bpzWirt_triple (a b c : ℝ) (D₁ D₂ D₃ : ℂ →L[ℝ] ℝ) :
    bpzWirt ((a * b) • D₃ + c • (a • D₂ + b • D₁)) =
      ((a * b : ℝ) : ℂ) * bpzWirt D₃ + (c : ℂ) * ((a : ℂ) * bpzWirt D₂ + (b : ℂ) * bpzWirt D₁) := by
  rw [bpzWirt_add, bpzWirt_smul, bpzWirt_smul, bpzWirt_add, bpzWirt_smul, bpzWirt_smul]

/-- The norm of the derivative of a product of three factors. -/
theorem bpz_norm_triple {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (D₁ D₂ D₃ : ℂ →L[ℝ] ℝ) :
    ‖(a * b) • D₃ + c • (a • D₂ + b • D₁)‖ ≤ a * b * ‖D₃‖ + c * (a * ‖D₂‖ + b * ‖D₁‖) := by
  have e1 : ‖(a * b) • D₃‖ = a * b * ‖D₃‖ := by
    rw [norm_smul, Real.norm_of_nonneg (mul_nonneg ha hb)]
  have e2 : ‖a • D₂ + b • D₁‖ ≤ a * ‖D₂‖ + b * ‖D₁‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  refine (norm_add_le _ _).trans ?_
  rw [e1, norm_smul, Real.norm_of_nonneg hc]
  gcongr

/-- The derivative of `k̃`, its Wirtinger form and a bound. -/
theorem bpz_tildeWeight_hasFDerivAt {γ χ α₁ α₂ : ℝ} {z x : ℂ} (hx : x ∈ bpzRegular z) :
    ∃ L : ℂ →L[ℝ] ℝ, HasFDerivAt (bpzTildeWeight γ χ α₁ α₂ z) L x ∧
      ((L 1 : ℂ) - Complex.I * (L Complex.I : ℂ)) / 2 =
        (bpzTildeWeight γ χ α₁ α₂ z x : ℂ) *
          ((γ * χ / 2 : ℝ) / (x - z) - (γ * α₁ / 2 : ℝ) / x - (γ * α₂ / 2 : ℝ) / (x - 1)) ∧
      ‖L‖ ≤ bpzTildeWeight γ χ α₁ α₂ z x *
        (|γ * χ| / ‖x - z‖ + |γ * α₁| / ‖x‖ + |γ * α₂| / ‖x - 1‖) := by
  obtain ⟨h0, h1, hz⟩ := hx
  have hA := bpz_hasFDerivAt_norm_sub_rpow z (γ * χ) hz
  have hB := bpz_hasFDerivAt_norm_sub_rpow 0 (-(γ * α₁)) h0
  have hC := bpz_hasFDerivAt_norm_sub_rpow 1 (-(γ * α₂)) h1
  simp only [sub_zero] at hB
  have wA := bpz_wirtinger_norm_sub_rpow z (γ * χ) hz
  have wB := bpz_wirtinger_norm_sub_rpow 0 (-(γ * α₁)) h0
  have wC := bpz_wirtinger_norm_sub_rpow 1 (-(γ * α₂)) h1
  simp only [sub_zero] at wB
  have nA := bpz_norm_normSubRpowDeriv z (γ * χ) hz
  have nB := bpz_norm_normSubRpowDeriv 0 (-(γ * α₁)) h0
  have nC := bpz_norm_normSubRpowDeriv 1 (-(γ * α₂)) h1
  simp only [sub_zero, abs_neg] at nB
  simp only [abs_neg] at nC
  have hnA : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hnB : 0 < ‖x‖ := norm_pos_iff.mpr h0
  have hnC : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h1)
  have pA : 0 < ‖x - z‖ ^ (γ * χ) := Real.rpow_pos_of_pos hnA _
  have pB : 0 < ‖x‖ ^ (-(γ * α₁)) := Real.rpow_pos_of_pos hnB _
  have pC : 0 < ‖x - 1‖ ^ (-(γ * α₂)) := Real.rpow_pos_of_pos hnC _
  refine ⟨(‖x - z‖ ^ (γ * χ) * ‖x‖ ^ (-(γ * α₁))) •
      ((-(γ * α₂) * ‖x - 1‖ ^ (-(γ * α₂) - 2)) • innerSL ℝ (x - 1)) +
    ‖x - 1‖ ^ (-(γ * α₂)) • (‖x - z‖ ^ (γ * χ) •
      ((-(γ * α₁) * ‖x‖ ^ (-(γ * α₁) - 2)) • innerSL ℝ x) +
      ‖x‖ ^ (-(γ * α₁)) • ((γ * χ * ‖x - z‖ ^ (γ * χ - 2)) • innerSL ℝ (x - z))), ?_, ?_, ?_⟩
  · exact (hA.mul hB).mul hC
  · show bpzWirt _ = _
    rw [bpzWirt_triple]
    change bpzWirt _ = _ at wA wB wC
    rw [wA, wB, wC]
    unfold bpzTildeWeight
    push_cast
    ring
  · refine (bpz_norm_triple pA.le pB.le pC.le _ _ _).trans ?_
    rw [nA, nB, nC]
    unfold bpzTildeWeight
    apply le_of_eq
    ring

/-- Complex derivative of `g` and its algebraic form. -/
theorem bpz_hasDerivAt_bpzGfun {z x : ℂ} (hx : x ≠ z) :
    HasDerivAt (bpzGfun z) (-1 + z * (z - 1) / (z - x) ^ 2) x := by
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have hN : HasDerivAt (fun y : ℂ => y * (y - 1)) (1 * (x - 1) + x * 1) x :=
    (hasDerivAt_id x).mul ((hasDerivAt_id x).sub_const 1)
  have hD : HasDerivAt (fun y : ℂ => z - y) (-1) x := (hasDerivAt_id x).const_sub z
  have h := hN.div hD hzx
  unfold bpzGfun
  convert h using 1
  field_simp
  ring

/-- The four directional derivatives of `Re g · k̃` and `Im g · k̃` combine, by the product rule,
into `k̃ g' + g (L 1 − i L i) / 2`. -/
theorem bpz_wirt_product_alg (d g : ℂ) (t L1 LI : ℝ) :
    (((g.re * L1 + t * (1 * d).re : ℝ) : ℂ) + Complex.I * ((g.im * L1 + t * (1 * d).im : ℝ) : ℂ) -
      Complex.I * ((g.re * LI + t * (Complex.I * d).re : ℝ) : ℂ) +
      ((g.im * LI + t * (Complex.I * d).im : ℝ) : ℂ)) / 2 =
    (t : ℂ) * d + g * (((L1 : ℂ) - Complex.I * (LI : ℂ)) / 2) := by
  apply Complex.ext <;> simp <;> ring

/-- The four real directional derivatives of `Re g · k̃`, `Im g · k̃` combine into the Wirtinger
derivative of `g k̃`. -/
theorem bpz_wirtinger_g_tildeWeight {γ χ α₁ α₂ : ℝ} {z x : ℂ} (hx : x ∈ bpzRegular z) :
    (((fderiv ℝ (fun y => (bpzGfun z y).re * bpzTildeWeight γ χ α₁ α₂ z y) x 1 : ℝ) : ℂ) +
        Complex.I * (fderiv ℝ (fun y => (bpzGfun z y).im * bpzTildeWeight γ χ α₁ α₂ z y) x 1 : ℝ) -
        Complex.I * (fderiv ℝ (fun y => (bpzGfun z y).re * bpzTildeWeight γ χ α₁ α₂ z y) x
          Complex.I : ℝ) +
        (fderiv ℝ (fun y => (bpzGfun z y).im * bpzTildeWeight γ χ α₁ α₂ z y) x Complex.I : ℝ)) / 2 =
      (bpzTildeWeight γ χ α₁ α₂ z x : ℂ) *
        ((-1 + z * (z - 1) / (z - x) ^ 2) + bpzGfun z x *
          ((γ * χ / 2 : ℝ) / (x - z) - (γ * α₁ / 2 : ℝ) / x - (γ * α₂ / 2 : ℝ) / (x - 1))) := by
  obtain ⟨L, hL, hW, -⟩ := bpz_tildeWeight_hasFDerivAt (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hx
  have hg := bpz_hasDerivAt_bpzGfun hx.2.2
  have hg' := hg.hasFDerivAt.restrictScalars ℝ
  have hre : HasFDerivAt (fun y => (bpzGfun z y).re)
      (Complex.reCLM.comp (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-1 + z * (z - 1) / (z - x) ^ 2)))) x :=
    Complex.reCLM.hasFDerivAt.comp x hg'
  have him : HasFDerivAt (fun y => (bpzGfun z y).im)
      (Complex.imCLM.comp (ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ (-1 + z * (z - 1) / (z - x) ^ 2)))) x :=
    Complex.imCLM.hasFDerivAt.comp x hg'
  have hF : HasFDerivAt (fun y => (bpzGfun z y).re * bpzTildeWeight γ χ α₁ α₂ z y)
      ((bpzGfun z x).re • L + bpzTildeWeight γ χ α₁ α₂ z x •
        Complex.reCLM.comp (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (-1 + z * (z - 1) / (z - x) ^ 2)))) x :=
    hre.mul hL
  have hG : HasFDerivAt (fun y => (bpzGfun z y).im * bpzTildeWeight γ χ α₁ α₂ z y)
      ((bpzGfun z x).im • L + bpzTildeWeight γ χ α₁ α₂ z x •
        Complex.imCLM.comp (ContinuousLinearMap.restrictScalars ℝ
          (ContinuousLinearMap.toSpanSingleton ℂ (-1 + z * (z - 1) / (z - x) ^ 2)))) x :=
    him.mul hL
  rw [hF.fderiv, hG.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  rw [bpz_wirt_product_alg, hW]
  ring

/-- The coefficient identity, for abstract complex coefficients `a b c`. -/
theorem bpz_g_coefficients_alg (x z a b c : ℂ) (h0 : x ≠ 0) (h1 : x - 1 ≠ 0) (hz : x - z ≠ 0)
    (hzx : z - x ≠ 0) :
    (-1 + z * (z - 1) / (z - x) ^ 2) + x * (x - 1) / (z - x) *
        (a / (x - z) - b / x - c / (x - 1)) =
      (-1 - a + b + c) + (a * (2 * z - 1) - b * (z - 1) - c * z) / (z - x) +
        (1 - a) * (z * (z - 1)) / (z - x) ^ 2 := by
  field_simp
  ring

/-- The coefficient identity. -/
theorem bpz_g_coefficients {γ χ α₁ α₂ : ℝ} {z x : ℂ} (hx : x ∈ bpzRegular z) :
    (-1 + z * (z - 1) / (z - x) ^ 2) + bpzGfun z x *
        ((γ * χ / 2 : ℝ) / (x - z) - (γ * α₁ / 2 : ℝ) / x - (γ * α₂ / 2 : ℝ) / (x - 1)) =
      ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) +
        (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
          ((γ * α₂ / 2 : ℝ) : ℂ) * z) / (z - x) +
        ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) / (z - x) ^ 2 := by
  obtain ⟨h0, h1, hz⟩ := hx
  have h := bpz_g_coefficients_alg x z ((γ * χ / 2 : ℝ) : ℂ) ((γ * α₁ / 2 : ℝ) : ℂ)
    ((γ * α₂ / 2 : ℝ) : ℂ) h0 (sub_ne_zero.mpr h1) (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hz.symm)
  unfold bpzGfun
  rw [h]
  push_cast
  ring

/-- The complex combination of the limit kernels. -/
theorem bpz_kern_wirtinger {w : ℂ} (hw : w ≠ 0) :
    (((bpzKern 1 w : ℝ) : ℂ) - Complex.I * (bpzKern Complex.I w : ℝ)) / 2 = -1 / (2 * w) := by
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  have key := bpz_conj_mul_self w
  unfold bpzKern
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im]
  push_cast at key ⊢
  field_simp
  linear_combination (-1 : ℂ) * key

/-- The combination of the four real products `Re D · k₁`, `Im D · k₁`, `Re D · k₂`, `Im D · k₂`
is `D (k₁ − i k₂) / 2`. -/
theorem bpz_wirt_kern_alg (D : ℂ) (k₁ k₂ : ℝ) :
    (((D.re * k₁ : ℝ) : ℂ) + Complex.I * ((D.im * k₁ : ℝ) : ℂ) -
        Complex.I * ((D.re * k₂ : ℝ) : ℂ) + ((D.im * k₂ : ℝ) : ℂ)) / 2 =
      D * (((k₁ : ℂ) - Complex.I * (k₂ : ℂ)) / 2) := by
  apply Complex.ext <;> simp <;> ring

/-- The real kernels of `Re g`, `Im g` combine into the difference quotient of `g`. -/
theorem bpz_g_kern_combination {z x y : ℂ} (hxy : x ≠ y) :
    (((((bpzGfun z x).re - (bpzGfun z y).re) * bpzKern 1 (x - y) : ℝ) : ℂ) +
        Complex.I * (((bpzGfun z x).im - (bpzGfun z y).im) * bpzKern 1 (x - y) : ℝ) -
        Complex.I * (((bpzGfun z x).re - (bpzGfun z y).re) * bpzKern Complex.I (x - y) : ℝ) +
        (((bpzGfun z x).im - (bpzGfun z y).im) * bpzKern Complex.I (x - y) : ℝ)) / 2 =
      -(bpzGfun z x - bpzGfun z y) / (2 * (x - y)) := by
  rw [← Complex.sub_re, ← Complex.sub_im, bpz_wirt_kern_alg,
    bpz_kern_wirtinger (sub_ne_zero.mpr hxy)]
  ring

/-- The difference quotient of `g`. -/
theorem bpz_g_diff_quot {z x y : ℂ} (hxy : x ≠ y) (hx : x ≠ z) (hy : y ≠ z) :
    (bpzGfun z x - bpzGfun z y) / (x - y) = -1 + z * (z - 1) / ((z - x) * (z - y)) := by
  have h1 : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have h2 : z - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have h3 : z - y ≠ 0 := sub_ne_zero.mpr hy.symm
  unfold bpzGfun
  field_simp
  ring
