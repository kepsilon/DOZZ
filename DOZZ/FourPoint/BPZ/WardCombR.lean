/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardDefs

/-! # The right side of the Ward identity for the four-point combination

For the test function `ℓ ∘ g`, `g(x) = x (x - 1)/(z - x)`, the real Ward integrand is
`H(x, y) = (ℓ g(x) - ℓ g(y)) k(x) k(y) K_v(x - y) / 2`.  The four directions `(Re, 1)`,
`(Im, 1)`, `(Re, i)`, `(Im, i)` combine pointwise into
`k(x) k(y) (1 - z (z - 1) / ((z - x) (z - y))) / 4`, off the diagonal.  Since the chaos measure
has no atoms, the combination of the four double integrals is
`(I² - z (z - 1) D²) / 4` with `I = ∫ k dM` and `D = ∫ k/(z - x) dM`, and taking expectations
yields the combination of the moments `J` and `D₂`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The real Ward integrand `(ℓ g(x) - ℓ g(y)) k(x) k(y) K_v(x - y) / 2`. -/
noncomputable def bpzWCR_H (z : ℂ) (k : ℂ → ℝ) (ℓ : ℂ →L[ℝ] ℝ) (v x y : ℂ) : ℝ :=
  (ℓ (bpzG z x) - ℓ (bpzG z y)) * (k x * k y) * bpzKern v (x - y) / 2

/-! ### Elementary inequalities -/

/-- The elementary inequality `1/u ≤ 1 + 1/u²`. -/
theorem bpzWCR_inv_le (u : ℝ) : u⁻¹ ≤ 1 + (u ^ 2)⁻¹ := by
  rw [← inv_pow]
  linarith [sq_nonneg (u⁻¹ - 1 / 2)]

/-- `‖t/(z - x)‖ ≤ (1 + ‖x - z‖^{-2}) t` for `t ≥ 0`. -/
theorem bpzWCR_norm_div_le {z x : ℂ} (hx : x ≠ z) {t : ℝ} (ht : 0 ≤ t) :
    ‖(t : ℂ) / (z - x)‖ ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * t := by
  have hu : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ht, norm_sub_rev z x,
    Real.rpow_neg hu.le, Real.rpow_two]
  calc t / ‖x - z‖ = ‖x - z‖⁻¹ * t := by ring
    _ ≤ (1 + (‖x - z‖ ^ 2)⁻¹) * t :=
        mul_le_mul_of_nonneg_right (bpzWCR_inv_le _) ht

/-- The algebra behind the domination of the Ward integrand by `A/2 (g(x) k(y) + k(x) g(y))`. -/
theorem bpzWCR_alg_bound {A r s a b : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    A * (1 + r + s) * (a * b) / 2 ≤ A / 2 * ((1 + r) * a * b + a * ((1 + s) * b)) := by
  have h : 0 ≤ A * (a * b) := mul_nonneg hA (mul_nonneg ha hb)
  have e : A / 2 * ((1 + r) * a * b + a * ((1 + s) * b)) - A * (1 + r + s) * (a * b) / 2 =
      A * (a * b) / 2 := by ring
  linarith

/-! ### The pointwise combination -/

/-- The four real products `a_j w / 2` combine through the four real coefficients `a_j`. -/
theorem bpzWCR_alg (a₁ a₂ a₃ a₄ w : ℝ) :
    (((a₁ * w / 2 : ℝ) : ℂ) + Complex.I * ((a₂ * w / 2 : ℝ) : ℂ) -
        Complex.I * ((a₃ * w / 2 : ℝ) : ℂ) + ((a₄ * w / 2 : ℝ) : ℂ)) / 2 =
      ((w : ℂ) / 2) *
        (((a₁ : ℂ) + Complex.I * (a₂ : ℂ) - Complex.I * (a₃ : ℂ) + (a₄ : ℂ)) / 2) := by
  push_cast
  ring

/-- The Ward integrand with the kernel pairing factored out. -/
theorem bpzWCR_H_eq (z : ℂ) (k : ℂ → ℝ) (ℓ : ℂ →L[ℝ] ℝ) (v x y : ℂ) :
    bpzWCR_H z k ℓ v x y =
      (ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y) * (k x * k y) / 2 := by
  unfold bpzWCR_H
  ring

/-- Off the diagonal, the four real Ward integrands combine into
`(k(x) k(y) - z (z - 1) (k(x)/(z - x)) (k(y)/(z - y))) / 4`. -/
theorem bpzWCR_pointwise {z x y : ℂ} (k : ℂ → ℝ) (hxy : x ≠ y) (hx : x ≠ z) (hy : y ≠ z) :
    (((bpzWCR_H z k Complex.reCLM 1 x y : ℝ) : ℂ) +
        Complex.I * ((bpzWCR_H z k Complex.imCLM 1 x y : ℝ) : ℂ) -
        Complex.I * ((bpzWCR_H z k Complex.reCLM Complex.I x y : ℝ) : ℂ) +
        ((bpzWCR_H z k Complex.imCLM Complex.I x y : ℝ) : ℂ)) / 2 =
      ((k x : ℂ) * (k y : ℂ) - z * (z - 1) * (((k x : ℂ) / (z - x)) * ((k y : ℂ) / (z - y)))) /
        4 := by
  have h1 : ((((bpzG z x).re - (bpzG z y).re) * bpzKern 1 (x - y) : ℝ) +
        Complex.I * ((((bpzG z x).im - (bpzG z y).im) * bpzKern 1 (x - y) : ℝ) : ℂ) -
        Complex.I * ((((bpzG z x).re - (bpzG z y).re) * bpzKern Complex.I (x - y) : ℝ) : ℂ) +
        ((((bpzG z x).im - (bpzG z y).im) * bpzKern Complex.I (x - y) : ℝ) : ℂ)) / 2 =
      -(bpzG z x - bpzG z y) / (2 * (x - y)) := bpz_g_kern_combination hxy
  have h2 : (bpzG z x - bpzG z y) / (x - y) =
      -1 + z * (z - 1) / ((z - x) * (z - y)) := bpz_g_diff_quot hxy hx hy
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hzx : z - x ≠ 0 := sub_ne_zero.mpr hx.symm
  have hzy : z - y ≠ 0 := sub_ne_zero.mpr hy.symm
  rw [bpzWCR_H_eq, bpzWCR_H_eq, bpzWCR_H_eq, bpzWCR_H_eq, bpzWCR_alg]
  simp only [Complex.reCLM_apply, Complex.imCLM_apply]
  rw [h1, show -(bpzG z x - bpzG z y) / (2 * (x - y)) =
    -((bpzG z x - bpzG z y) / (x - y)) / 2 by field_simp, h2]
  push_cast
  field_simp
  ring

/-! ### Measurability and integrability on the product -/

/-- The Ward integrand is jointly measurable. -/
theorem bpzWCR_H_measurable (z : ℂ) {k : ℂ → ℝ} (hk : Measurable k) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Measurable (Function.uncurry (bpzWCR_H z k ℓ v)) := by
  have hg : Measurable (fun x => ℓ (bpzG z x)) := bpzWardG_measurable z ℓ
  exact ((((hg.comp measurable_fst).sub (hg.comp measurable_snd)).mul
    ((hk.comp measurable_fst).mul (hk.comp measurable_snd))).mul
      ((measurable_bpzKern v).comp (measurable_fst.sub measurable_snd))).div_const _

/-- The weight `k` is integrable once the singular weight `(1 + ‖x - z‖^{-2}) k` is. -/
theorem bpzWCR_integrable_k {z : ℂ} {m : Measure ℂ} {k : ℂ → ℝ} (hkm : Measurable k)
    (hk0 : ∀ x, 0 ≤ k x) (hgi : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m) :
    Integrable k m := by
  refine hgi.mono' hkm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hk0 x)]
  have h : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  exact le_mul_of_one_le_left (hk0 x) (by linarith)

/-- An almost sure property of the points of `m` holds for both coordinates `m ⊗ m`-a.e. -/
theorem bpzWCR_ae_prod {m : Measure ℂ} [IsFiniteMeasure m] {s : Set ℂ} (h : ∀ᵐ x ∂m, x ∈ s) :
    ∀ᵐ p ∂(m.prod m), p.1 ∈ s ∧ p.2 ∈ s := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := m) (ν := m)).ae h
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := m) (ν := m)).ae h
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- For a measure without atoms the diagonal is null for the product measure. -/
theorem bpzWCR_ae_prod_ne {m : Measure ℂ} [IsFiniteMeasure m] (hno : ∀ x, m {x} = 0) :
    ∀ᵐ p ∂(m.prod m), p.1 ≠ p.2 := by
  have hm : MeasurableSet {p : ℂ × ℂ | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [Measure.ae_prod_iff_ae_ae hm]
  refine Eventually.of_forall fun x => ?_
  rw [ae_iff]
  have : {y : ℂ | ¬ ((x, y).1 ≠ (x, y).2)} = {x} := by
    ext y
    simp [eq_comm]
  rw [this]
  exact hno x

/-- Pointwise domination of the Ward integrand on the regular set. -/
theorem bpzWCR_abs_H_le {z : ℂ} {k : ℂ → ℝ} (hk0 : ∀ x, 0 ≤ k x) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ)))
    {x y : ℂ} (hx : x ∈ bpzRegular z) (hy : y ∈ bpzRegular z) :
    |bpzWCR_H z k ℓ v x y| ≤
      A / 2 * ((1 + ‖x - z‖ ^ (-2 : ℝ)) * k x * k y + k x * ((1 + ‖y - z‖ ^ (-2 : ℝ)) * k y)) := by
  have hkk : 0 ≤ k x * k y := mul_nonneg (hk0 x) (hk0 y)
  rw [bpzWCR_H_eq, abs_div, abs_two, abs_mul, abs_of_nonneg hkk]
  refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hA x hx y hy) hkk)
    zero_le_two).trans ?_
  have := bpzWCR_alg_bound (A := A) (r := ‖x - z‖ ^ (-2 : ℝ)) (s := ‖y - z‖ ^ (-2 : ℝ))
    hA0 (hk0 x) (hk0 y)
  linarith

/-- Integrability of the Ward integrand on the product and the bound for its double integral. -/
theorem bpzWCR_integrable_double {z : ℂ} {m : Measure ℂ} [IsFiniteMeasure m] {k : ℂ → ℝ}
    (hkm : Measurable k) (hk0 : ∀ x, 0 ≤ k x) (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z)
    (hgi : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ))) :
    Integrable (fun p : ℂ × ℂ => bpzWCR_H z k ℓ v p.1 p.2) (m.prod m) ∧
      |∫ x, ∫ y, bpzWCR_H z k ℓ v x y ∂m ∂m| ≤
        A * ((∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m) * ∫ x, k x ∂m) := by
  have hki : Integrable k m := bpzWCR_integrable_k hkm hk0 hgi
  have hbi : Integrable (fun p : ℂ × ℂ => A / 2 * ((1 + ‖p.1 - z‖ ^ (-2 : ℝ)) * k p.1 * k p.2 +
      k p.1 * ((1 + ‖p.2 - z‖ ^ (-2 : ℝ)) * k p.2))) (m.prod m) :=
    ((hgi.mul_prod hki).add (hki.mul_prod hgi)).const_mul _
  have hbd : ∀ᵐ p ∂(m.prod m), ‖bpzWCR_H z k ℓ v p.1 p.2‖ ≤
      A / 2 * ((1 + ‖p.1 - z‖ ^ (-2 : ℝ)) * k p.1 * k p.2 +
        k p.1 * ((1 + ‖p.2 - z‖ ^ (-2 : ℝ)) * k p.2)) := by
    filter_upwards [bpzWCR_ae_prod hreg] with p hp
    rw [Real.norm_eq_abs]
    exact bpzWCR_abs_H_le hk0 ℓ v hA0 hA hp.1 hp.2
  have hint : Integrable (fun p : ℂ × ℂ => bpzWCR_H z k ℓ v p.1 p.2) (m.prod m) :=
    hbi.mono' (bpzWCR_H_measurable z hkm ℓ v).aestronglyMeasurable hbd
  refine ⟨hint, ?_⟩
  rw [show ∫ x, ∫ y, bpzWCR_H z k ℓ v x y ∂m ∂m =
    ∫ p : ℂ × ℂ, bpzWCR_H z k ℓ v p.1 p.2 ∂(m.prod m) from
      (integral_prod (fun p : ℂ × ℂ => bpzWCR_H z k ℓ v p.1 p.2) hint).symm,
    ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hbi hbd).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add (hgi.mul_prod hki) (hki.mul_prod hgi),
    integral_prod_mul (f := fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) (g := k),
    integral_prod_mul (f := k) (g := fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x)]
  ring

/-! ### The combination of the four double integrals -/

/-- A combination of four integrable real functions, as a complex integral. -/
theorem bpzWCR_integral_comb {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ : α → ℝ} (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) :
    (((∫ a, f₁ a ∂μ : ℝ) : ℂ) + Complex.I * ((∫ a, f₂ a ∂μ : ℝ) : ℂ) -
        Complex.I * ((∫ a, f₃ a ∂μ : ℝ) : ℂ) + ((∫ a, f₄ a ∂μ : ℝ) : ℂ)) / 2 =
      ∫ a, (((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ) - Complex.I * ((f₃ a : ℝ) : ℂ) +
        ((f₄ a : ℝ) : ℂ)) / 2 ∂μ := by
  have i₁ : Integrable (fun a => ((f₁ a : ℝ) : ℂ)) μ := h₁.ofReal
  have i₂ : Integrable (fun a => Complex.I * ((f₂ a : ℝ) : ℂ)) μ := h₂.ofReal.const_mul _
  have i₃ : Integrable (fun a => Complex.I * ((f₃ a : ℝ) : ℂ)) μ := h₃.ofReal.const_mul _
  have i₄ : Integrable (fun a => ((f₄ a : ℝ) : ℂ)) μ := h₄.ofReal
  have i₁₂ : Integrable (fun a => ((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ)) μ := i₁.add i₂
  have i₁₂₃ : Integrable (fun a => ((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ) -
      Complex.I * ((f₃ a : ℝ) : ℂ)) μ := i₁₂.sub i₃
  rw [integral_div, integral_add i₁₂₃ i₄, integral_sub i₁₂ i₃, integral_add i₁ i₂,
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]

/-- The combination of four integrable real functions is integrable. -/
theorem bpzWCR_integrable_comb {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f₁ f₂ f₃ f₄ : α → ℝ} (h₁ : Integrable f₁ μ) (h₂ : Integrable f₂ μ) (h₃ : Integrable f₃ μ)
    (h₄ : Integrable f₄ μ) :
    Integrable (fun a => (((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ) -
      Complex.I * ((f₃ a : ℝ) : ℂ) + ((f₄ a : ℝ) : ℂ)) / 2) μ := by
  have i₁ : Integrable (fun a => ((f₁ a : ℝ) : ℂ)) μ := h₁.ofReal
  have i₂ : Integrable (fun a => Complex.I * ((f₂ a : ℝ) : ℂ)) μ := h₂.ofReal.const_mul _
  have i₃ : Integrable (fun a => Complex.I * ((f₃ a : ℝ) : ℂ)) μ := h₃.ofReal.const_mul _
  have i₄ : Integrable (fun a => ((f₄ a : ℝ) : ℂ)) μ := h₄.ofReal
  have i₁₂ : Integrable (fun a => ((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ)) μ := i₁.add i₂
  have i₁₂₃ : Integrable (fun a => ((f₁ a : ℝ) : ℂ) + Complex.I * ((f₂ a : ℝ) : ℂ) -
      Complex.I * ((f₃ a : ℝ) : ℂ)) μ := i₁₂.sub i₃
  exact (i₁₂₃.add i₄).div_const _

/-- The combination of the four real Ward integrals, for a measure without atoms. -/
theorem bpzWCR_combo {z : ℂ} {m : Measure ℂ} [IsFiniteMeasure m] (hno : ∀ x, m {x} = 0)
    (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z) {k : ℂ → ℝ} (hki : Integrable k m)
    (hdi : Integrable (fun x => (k x : ℂ) / (z - x)) m)
    (h₁ : Integrable (fun p : ℂ × ℂ => bpzWCR_H z k Complex.reCLM 1 p.1 p.2) (m.prod m))
    (h₂ : Integrable (fun p : ℂ × ℂ => bpzWCR_H z k Complex.imCLM 1 p.1 p.2) (m.prod m))
    (h₃ : Integrable (fun p : ℂ × ℂ => bpzWCR_H z k Complex.reCLM Complex.I p.1 p.2)
      (m.prod m))
    (h₄ : Integrable (fun p : ℂ × ℂ => bpzWCR_H z k Complex.imCLM Complex.I p.1 p.2)
      (m.prod m)) :
    (((∫ x, ∫ y, bpzWCR_H z k Complex.reCLM 1 x y ∂m ∂m : ℝ) : ℂ) +
        Complex.I * ((∫ x, ∫ y, bpzWCR_H z k Complex.imCLM 1 x y ∂m ∂m : ℝ) : ℂ) -
        Complex.I * ((∫ x, ∫ y, bpzWCR_H z k Complex.reCLM Complex.I x y ∂m ∂m : ℝ) : ℂ) +
        ((∫ x, ∫ y, bpzWCR_H z k Complex.imCLM Complex.I x y ∂m ∂m : ℝ) : ℂ)) / 2 =
      ((((∫ x, k x ∂m : ℝ) : ℂ)) ^ 2 - z * (z - 1) * (∫ x, (k x : ℂ) / (z - x) ∂m) ^ 2) / 4 := by
  have e : ∀ (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ),
      Integrable (fun p : ℂ × ℂ => bpzWCR_H z k ℓ v p.1 p.2) (m.prod m) →
      ∫ x, ∫ y, bpzWCR_H z k ℓ v x y ∂m ∂m =
        ∫ p : ℂ × ℂ, bpzWCR_H z k ℓ v p.1 p.2 ∂(m.prod m) := fun ℓ v h =>
    (integral_prod (fun p : ℂ × ℂ => bpzWCR_H z k ℓ v p.1 p.2) h).symm
  rw [e _ _ h₁, e _ _ h₂, e _ _ h₃, e _ _ h₄, bpzWCR_integral_comb h₁ h₂ h₃ h₄]
  have hae : ∀ᵐ p ∂(m.prod m), (((bpzWCR_H z k Complex.reCLM 1 p.1 p.2 : ℝ) : ℂ) +
        Complex.I * ((bpzWCR_H z k Complex.imCLM 1 p.1 p.2 : ℝ) : ℂ) -
        Complex.I * ((bpzWCR_H z k Complex.reCLM Complex.I p.1 p.2 : ℝ) : ℂ) +
        ((bpzWCR_H z k Complex.imCLM Complex.I p.1 p.2 : ℝ) : ℂ)) / 2 =
      ((k p.1 : ℂ) * (k p.2 : ℂ) - z * (z - 1) *
        (((k p.1 : ℂ) / (z - p.1)) * ((k p.2 : ℂ) / (z - p.2)))) / 4 := by
    filter_upwards [bpzWCR_ae_prod hreg, bpzWCR_ae_prod_ne hno] with p hp hne
    exact bpzWCR_pointwise k hne hp.1.2.2 hp.2.2.2
  have j₁ : Integrable (fun p : ℂ × ℂ => (k p.1 : ℂ) * (k p.2 : ℂ)) (m.prod m) :=
    hki.ofReal.mul_prod hki.ofReal
  have j₂ : Integrable (fun p : ℂ × ℂ => z * (z - 1) *
      (((k p.1 : ℂ) / (z - p.1)) * ((k p.2 : ℂ) / (z - p.2)))) (m.prod m) :=
    (hdi.mul_prod hdi).const_mul _
  rw [integral_congr_ae hae, integral_div, integral_sub j₁ j₂, integral_const_mul,
    integral_prod_mul (f := fun x => (k x : ℂ)) (g := fun x => (k x : ℂ)),
    integral_prod_mul (f := fun x => (k x : ℂ) / (z - x)) (g := fun x => (k x : ℂ) / (z - x)),
    integral_complex_ofReal]
  ring

/-! ### The expectation over the randomness -/

/-- The integrand of the right side of the Ward identity, as a function of the measure. -/
noncomputable def bpzWCR_F (k : ℂ → ℝ) (γ s : ℝ) (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    (m : Measure ℂ) : ℝ :=
  (s + 1) * ((∫ x, k x ∂m) ^ (-(s + 1) - 1) * (γ ^ 2 * ∫ x, ∫ y, bpzWCR_H z k ℓ v x y ∂m ∂m))

/-- The standing hypotheses of the Ward combination, for a weight `k` and a random measure `M`. -/
structure bpzWCR_Data {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (k : ℂ → ℝ) (z : ℂ) (s : ℝ) : Prop where
  meas : Measurable M
  fin : ∀ ω, IsFiniteMeasure (M ω)
  km : Measurable k
  nonneg : ∀ x, 0 ≤ k x
  s_nonneg : 0 ≤ s
  noAtoms : ∀ᵐ ω ∂P, ∀ x, M ω {x} = 0
  regular : ∀ᵐ ω ∂P, ∀ᵐ x ∂M ω, x ∈ bpzRegular z
  sing : ∀ᵐ ω ∂P, Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) (M ω)
  pos : ∀ᵐ ω ∂P, 0 < ∫ x, k x ∂M ω
  dom : Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-(s + 1)) *
    ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂M ω) P

/-- The integrand of the right side of the Ward identity is measurable in `ω`. -/
theorem bpzWCR_F_measurable {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) (hfin : ∀ ω, IsFiniteMeasure (M ω)) {k : ℂ → ℝ} (hkm : Measurable k)
    (γ s : ℝ) (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Measurable (fun ω => bpzWCR_F k γ s z ℓ v (M ω)) :=
  measurable_const.mul ((((measurable_integral_measure hkm).comp hMm).pow_const _).mul
    (measurable_const.mul
      (bpz_measurable_double_integral hMm hfin hMm hfin _ (bpzWCR_H_measurable z hkm ℓ v))))

/-- The algebra behind the domination of the Ward integrand in `ω`. -/
theorem bpzWCR_dom_alg {a b I G T A c γ : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hab : b = a * I)
    (hT : |T| ≤ A * (G * I)) :
    |c * (a * (γ ^ 2 * T))| ≤ c * γ ^ 2 * A * (b * G) := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hc, abs_of_nonneg ha, abs_of_nonneg (sq_nonneg γ)]
  calc c * (a * (γ ^ 2 * |T|)) ≤ c * (a * (γ ^ 2 * (A * (G * I)))) := by gcongr
    _ = c * γ ^ 2 * A * (b * G) := by rw [hab]; ring

/-- `I^{-(s+1)} = I^{-(s+1)-1} I`. -/
theorem bpzWCR_rpow_mul {I : ℝ} (hI : 0 < I) (s : ℝ) :
    I ^ (-(s + 1)) = I ^ (-(s + 1) - 1) * I := by
  rw [← Real.rpow_add_one hI.ne']
  ring_nf

/-- The integrand of the right side of the Ward identity is integrable, dominated by
`I^{-(s+1)} ∫ (1 + ‖x - z‖^{-2}) k dM`. -/
theorem bpzWCR_F_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℂ}
    {k : ℂ → ℝ} {z : ℂ} {s : ℝ} (D : bpzWCR_Data P M k z s) (γ : ℝ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ x ∈ bpzRegular z, ∀ y ∈ bpzRegular z,
      |(ℓ (bpzG z x) - ℓ (bpzG z y)) * bpzKern v (x - y)| ≤
        A * (1 + ‖x - z‖ ^ (-2 : ℝ) + ‖y - z‖ ^ (-2 : ℝ))) :
    Integrable (fun ω => bpzWCR_F k γ s z ℓ v (M ω)) P := by
  refine (D.dom.const_mul ((s + 1) * γ ^ 2 * A)).mono'
    (bpzWCR_F_measurable D.meas D.fin D.km γ s z ℓ v).aestronglyMeasurable ?_
  filter_upwards [D.regular, D.sing, D.pos] with ω hr hg hp
  have := D.fin ω
  rw [Real.norm_eq_abs]
  exact bpzWCR_dom_alg (Real.rpow_nonneg hp.le _) (by linarith [D.s_nonneg]) (bpzWCR_rpow_mul hp s)
    (bpzWCR_integrable_double D.km D.nonneg hr hg ℓ v hA0 hA).2

/-! ### The expectation of the combination -/

/-- The weight `k/(z - x)` is integrable once the singular weight is. -/
theorem bpzWCR_integrable_div {z : ℂ} {m : Measure ℂ} {k : ℂ → ℝ} (hkm : Measurable k)
    (hk0 : ∀ x, 0 ≤ k x) (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z)
    (hgi : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m) :
    Integrable (fun x => (k x : ℂ) / (z - x)) m := by
  refine hgi.mono' ((Complex.measurable_ofReal.comp hkm).div
    (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  filter_upwards [hreg] with x hx
  exact bpzWCR_norm_div_le hx.2.2 (hk0 x)

/-- The mass is bounded by the singular mass. -/
theorem bpzWCR_integral_le {z : ℂ} {m : Measure ℂ} {k : ℂ → ℝ} (hkm : Measurable k)
    (hk0 : ∀ x, 0 ≤ k x) (hgi : Integrable (fun x => (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x) m) :
    ∫ x, k x ∂m ≤ ∫ x, (1 + ‖x - z‖ ^ (-2 : ℝ)) * k x ∂m := by
  refine integral_mono (bpzWCR_integrable_k hkm hk0 hgi) hgi fun x => ?_
  have h : 0 ≤ ‖x - z‖ ^ (-2 : ℝ) := bpz_rpow_neg_two_nonneg (norm_nonneg _)
  exact le_mul_of_one_le_left (hk0 x) (by linarith)

/-- The algebra behind the identification of the combination with `J` and `D₂`. -/
theorem bpzWCR_alg2 (c a γ I T₁ T₂ T₃ T₄ : ℝ) (z D : ℂ)
    (h : ((T₁ : ℂ) + Complex.I * (T₂ : ℂ) - Complex.I * (T₃ : ℂ) + (T₄ : ℂ)) / 2 =
      ((I : ℂ) ^ 2 - z * (z - 1) * D ^ 2) / 4) :
    (((c * (a * (γ ^ 2 * T₁)) : ℝ) : ℂ) + Complex.I * ((c * (a * (γ ^ 2 * T₂)) : ℝ) : ℂ) -
        Complex.I * ((c * (a * (γ ^ 2 * T₃)) : ℝ) : ℂ) +
        ((c * (a * (γ ^ 2 * T₄)) : ℝ) : ℂ)) / 2 =
      (c : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        (((a * I ^ 2 : ℝ) : ℂ) - z * (z - 1) * ((a : ℂ) * D ^ 2)) := by
  push_cast at h ⊢
  linear_combination ((c : ℂ) * a * γ ^ 2) * h

/-- `I^{-s} = I^{-s-2} I²`. -/
theorem bpzWCR_rpow_neg_two {I : ℝ} (hI : 0 < I) (s : ℝ) :
    I ^ (-s) = I ^ (-s - 2) * I ^ 2 := by
  rw [← Real.rpow_two, ← Real.rpow_add hI]
  ring_nf

/-- The integrand of `J = E[I^{-s}]` is integrable. -/
theorem bpzWCR_J_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℂ}
    {k : ℂ → ℝ} {z : ℂ} {s : ℝ} (D : bpzWCR_Data P M k z s) :
    Integrable (fun ω => (∫ x, k x ∂M ω) ^ (-s)) P := by
  refine D.dom.mono' (((measurable_integral_measure D.km).comp D.meas).pow_const _
    ).aestronglyMeasurable ?_
  filter_upwards [D.sing, D.pos] with ω hg hp
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), show (∫ x, k x ∂M ω) ^ (-s) =
    (∫ x, k x ∂M ω) ^ (-(s + 1)) * ∫ x, k x ∂M ω by
      rw [← Real.rpow_add_one hp.ne']; ring_nf]
  exact mul_le_mul_of_nonneg_left (bpzWCR_integral_le D.km D.nonneg hg)
    (Real.rpow_nonneg hp.le _)

/-- The almost sure identity for the combination of the four Ward integrands. -/
theorem bpzWCR_ae_comb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℂ}
    {k : ℂ → ℝ} {z : ℂ} {s γ : ℝ} (D : bpzWCR_Data P M k z s) (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    ∀ᵐ ω ∂P, (((bpzWCR_F k γ s z Complex.reCLM 1 (M ω) : ℝ) : ℂ) +
        Complex.I * ((bpzWCR_F k γ s z Complex.imCLM 1 (M ω) : ℝ) : ℂ) -
        Complex.I * ((bpzWCR_F k γ s z Complex.reCLM Complex.I (M ω) : ℝ) : ℂ) +
        ((bpzWCR_F k γ s z Complex.imCLM Complex.I (M ω) : ℝ) : ℂ)) / 2 =
      ((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        ((((∫ x, k x ∂M ω) ^ (-s) : ℝ) : ℂ) - z * (z - 1) *
          ((((∫ x, k x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) * (∫ x, (k x : ℂ) / (z - x) ∂M ω) ^ 2)) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := bpz_g_kern_bound hz0 hz1 Complex.reCLM 1
  obtain ⟨A₂, hA₂0, hA₂⟩ := bpz_g_kern_bound hz0 hz1 Complex.imCLM 1
  obtain ⟨A₃, hA₃0, hA₃⟩ := bpz_g_kern_bound hz0 hz1 Complex.reCLM Complex.I
  obtain ⟨A₄, hA₄0, hA₄⟩ := bpz_g_kern_bound hz0 hz1 Complex.imCLM Complex.I
  filter_upwards [D.noAtoms, D.regular, D.sing, D.pos] with ω hno hr hg hp
  have := D.fin ω
  have hki := bpzWCR_integrable_k D.km D.nonneg hg
  have hdi := bpzWCR_integrable_div D.km D.nonneg hr hg
  have hc := bpzWCR_combo hno hr hki hdi
    (bpzWCR_integrable_double D.km D.nonneg hr hg Complex.reCLM 1 hA₁0 hA₁).1
    (bpzWCR_integrable_double D.km D.nonneg hr hg Complex.imCLM 1 hA₂0 hA₂).1
    (bpzWCR_integrable_double D.km D.nonneg hr hg Complex.reCLM Complex.I hA₃0 hA₃).1
    (bpzWCR_integrable_double D.km D.nonneg hr hg Complex.imCLM Complex.I hA₄0 hA₄).1
  unfold bpzWCR_F
  rw [show -(s + 1) - 1 = -s - 2 by ring, bpzWCR_rpow_neg_two hp s]
  exact bpzWCR_alg2 _ _ _ _ _ _ _ _ _ _ hc

/-- The combination of the four expectations, for abstract data. -/
theorem bpzWCR_main {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℂ}
    {k : ℂ → ℝ} {z : ℂ} {s γ : ℝ} (D : bpzWCR_Data P M k z s) (hγ : γ ≠ 0) (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    (((∫ ω, bpzWCR_F k γ s z Complex.reCLM 1 (M ω) ∂P : ℝ) : ℂ) +
        Complex.I * ((∫ ω, bpzWCR_F k γ s z Complex.imCLM 1 (M ω) ∂P : ℝ) : ℂ) -
        Complex.I * ((∫ ω, bpzWCR_F k γ s z Complex.reCLM Complex.I (M ω) ∂P : ℝ) : ℂ) +
        ((∫ ω, bpzWCR_F k γ s z Complex.imCLM Complex.I (M ω) ∂P : ℝ) : ℂ)) / 2 =
      ((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        (((∫ ω, (∫ x, k x ∂M ω) ^ (-s) ∂P : ℝ) : ℂ) -
          z * (z - 1) * ∫ ω, (((∫ x, k x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) *
            (∫ x, (k x : ℂ) / (z - x) ∂M ω) ^ 2 ∂P) := by
  obtain ⟨A₁, hA₁0, hA₁⟩ := bpz_g_kern_bound hz0 hz1 Complex.reCLM 1
  obtain ⟨A₂, hA₂0, hA₂⟩ := bpz_g_kern_bound hz0 hz1 Complex.imCLM 1
  obtain ⟨A₃, hA₃0, hA₃⟩ := bpz_g_kern_bound hz0 hz1 Complex.reCLM Complex.I
  obtain ⟨A₄, hA₄0, hA₄⟩ := bpz_g_kern_bound hz0 hz1 Complex.imCLM Complex.I
  have F₁ := bpzWCR_F_integrable D γ Complex.reCLM 1 hA₁0 hA₁
  have F₂ := bpzWCR_F_integrable D γ Complex.imCLM 1 hA₂0 hA₂
  have F₃ := bpzWCR_F_integrable D γ Complex.reCLM Complex.I hA₃0 hA₃
  have F₄ := bpzWCR_F_integrable D γ Complex.imCLM Complex.I hA₄0 hA₄
  have hae := bpzWCR_ae_comb D (γ := γ) hz0 hz1
  have hs1 : ((s + 1 : ℝ) : ℂ) ≠ 0 := by
    have := D.s_nonneg
    exact_mod_cast (by positivity : (s + 1 : ℝ) ≠ 0)
  have hγ4 : ((γ ^ 2 / 4 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (γ ^ 2 / 4 : ℝ) ≠ 0)
  have hc' := mul_ne_zero hs1 hγ4
  have hJc : Integrable (fun ω => (((∫ x, k x ∂M ω) ^ (-s) : ℝ) : ℂ)) P :=
    (bpzWCR_J_integrable D).ofReal
  have hcomb := bpzWCR_integrable_comb F₁ F₂ F₃ F₄
  have hD2 : Integrable (fun ω => z * (z - 1) *
      ((((∫ x, k x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) * (∫ x, (k x : ℂ) / (z - x) ∂M ω) ^ 2)) P := by
    refine (hJc.sub (hcomb.div_const (((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ)))).congr ?_
    filter_upwards [hae] with ω hω
    simp only [Pi.sub_apply]
    rw [hω, mul_div_cancel_left₀ _ hc']
    ring
  rw [bpzWCR_integral_comb F₁ F₂ F₃ F₄, integral_congr_ae hae, integral_const_mul,
    integral_sub hJc hD2, integral_const_mul, integral_complex_ofReal]

/-- **The combination of the four Ward right sides.** For the test function `g(x) = x(x-1)/(z-x)`
the combination `(R_{Re,1} + i R_{Im,1} - i R_{Re,i} + R_{Im,i}) / 2` of the right sides of the
real Ward identity equals `(s + 1) (γ² / 4) (J - z (z - 1) D₂)`. -/
theorem bpz_wardRHS_combination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ((bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM 1 : ℂ) +
        Complex.I * (bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM 1 : ℂ) -
        Complex.I * (bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM Complex.I : ℂ) +
        (bpzWardRHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM Complex.I : ℂ)) / 2 =
      ((s + 1 : ℝ) : ℂ) * ((γ ^ 2 / 4 : ℝ) : ℂ) *
        ((bpzMomJ P M γ χ α₁ α₂ α₃ s z : ℂ) - z * (z - 1) * bpzMomD2 P M γ χ α₁ α₂ α₃ s z) := by
  have hq1 : 1 ≤ s + 1 := by linarith
  have hgood := bpz_singular_integrable_ae (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hdom := bpz_singular_dom_integrable (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) P X hX hγ hγ2 M hM
    hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hkm := measurable_bpzSoftWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have hk0 := bpzSoftWeight_nonneg (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 z
  have D : bpzWCR_Data P M (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) z s :=
    { meas := hMm
      fin := hM.1
      km := hkm
      nonneg := hk0
      s_nonneg := hs
      noAtoms := gmc_noAtoms_ae P X hX γ hγ hγ2 M hM hMm
      regular := bpz_ae_regular P X hX hγ hγ2 M hM z
      sing := hgood.mono fun ω h => h.1
      pos := by
        filter_upwards [hgood] with ω h
        obtain ⟨-, hpos, hfin⟩ := h
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hk0)
          hkm.aestronglyMeasurable]
        exact ENNReal.toReal_pos hpos.ne' hfin.ne
      dom := hdom }
  exact bpzWCR_main D hγ.ne' hz0 hz1

end DOZZ.Proofs
