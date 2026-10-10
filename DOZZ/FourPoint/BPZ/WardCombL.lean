/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.MomentMeas
public import DOZZ.FourPoint.BPZ.WardDefs

/-! # The complex combination of the four real Ward left sides

For the test functions `Re g` and `Im g` in the directions `1` and `i`, the combination
`(L_{Re,1} + i L_{Im,1} - i L_{Re,i} + L_{Im,i}) / 2` of the four real left sides `bpzWardLHS` is
the explicit combination `c₀ J + c₁ E₁ + c₂ D₁` of the moments `J`, `E₁`, `D₁`.

The proof is a pointwise identity (the Wirtinger derivative of `g k̃`), integrated first against
the chaos measure and then against the probability measure. The integrability needed to split the
integrals comes from the dominating weight `(1 + |x - z|^{-2}) k`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {γ χ α₁ α₂ α₃ : ℝ}

/-- The complex combination `(a + i b - i c + d) / 2` of four real numbers. -/
noncomputable def bpzWCL_comb (a b c d : ℝ) : ℂ :=
  ((a : ℂ) + Complex.I * (b : ℂ) - Complex.I * (c : ℂ) + (d : ℂ)) / 2

/-- The `x`-integrand of the real Ward identity for `ℓ ∘ g` in the direction `v`. -/
noncomputable def bpzWCL_F (γ χ α₁ α₂ α₃ : ℝ) (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) (v x : ℂ) : ℝ :=
  fderiv ℝ (fun x => ℓ (bpzG z x) * bpzTildeWeight γ χ α₁ α₂ z x) x v *
    normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ))

/-- The dominating weight `(1 + |x - z|^{-2}) k(x)`. -/
noncomputable def bpzWCL_g (γ χ α₁ α₂ α₃ : ℝ) (z x : ℂ) : ℝ :=
  (1 + ‖x - z‖ ^ (-2 : ℝ)) * bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x

/-! ### Integration of the combination -/

/-- The combination commutes with integration. -/
theorem bpzWCL_integral_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b c d : α → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : Integrable c μ) (hd : Integrable d μ) :
    bpzWCL_comb (∫ t, a t ∂μ) (∫ t, b t ∂μ) (∫ t, c t ∂μ) (∫ t, d t ∂μ) =
      ∫ t, bpzWCL_comb (a t) (b t) (c t) (d t) ∂μ := by
  unfold bpzWCL_comb
  have h1 : Integrable (fun t => (a t : ℂ)) μ := ha.ofReal
  have h2 : Integrable (fun t => Complex.I * (b t : ℂ)) μ := hb.ofReal.const_mul _
  have h3 : Integrable (fun t => Complex.I * (c t : ℂ)) μ := hc.ofReal.const_mul _
  have h4 : Integrable (fun t => (d t : ℂ)) μ := hd.ofReal
  have h12 : Integrable (fun t => (a t : ℂ) + Complex.I * (b t : ℂ)) μ := h1.add h2
  have h123 : Integrable (fun t => (a t : ℂ) + Complex.I * (b t : ℂ) - Complex.I * (c t : ℂ)) μ :=
    h12.sub h3
  rw [integral_div, integral_add h123 h4, integral_sub h12 h3, integral_add h1 h2,
    integral_const_mul, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
    integral_complex_ofReal, integral_complex_ofReal]

/-- The combination is homogeneous. -/
theorem bpzWCL_comb_mul (r a b c d : ℝ) :
    bpzWCL_comb (r * a) (r * b) (r * c) (r * d) = (r : ℂ) * bpzWCL_comb a b c d := by
  unfold bpzWCL_comb
  push_cast
  ring

/-! ### Elementary bounds -/

/-- The weight `k` is dominated by the dominating weight. -/
theorem bpzWCL_le_g (z x : ℂ) :
    bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ≤ bpzWCL_g γ χ α₁ α₂ α₃ z x := by
  have h := bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))
  exact le_mul_of_one_le_left (bpzSoftWeight_nonneg 0 z x) (by linarith)

/-- `|k / (z - x)| ≤ (1 + |x - z|^{-2}) k`. -/
theorem bpzWCL_norm_div_le {k : ℝ} (hk : 0 ≤ k) (x z : ℂ) :
    ‖(k : ℂ) / (z - x)‖ ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * k := by
  have h0 := bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))
  rcases eq_or_ne x z with rfl | hxz
  · refine le_trans (le_of_eq ?_) (mul_nonneg (by linarith) hk)
    rw [sub_self, div_zero, norm_zero]
  · have ht : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk, norm_sub_rev z x,
      bpz_rpow_neg_two ht.le]
    have h1 : ‖x - z‖⁻¹ ≤ 1 + (‖x - z‖ ^ 2)⁻¹ := by
      rw [← inv_pow]
      linarith [sq_nonneg (‖x - z‖⁻¹ - 1 / 2)]
    calc k / ‖x - z‖ = ‖x - z‖⁻¹ * k := by rw [div_eq_inv_mul]
      _ ≤ (1 + (‖x - z‖ ^ 2)⁻¹) * k := mul_le_mul_of_nonneg_right h1 hk

/-- `|k / (z - x)²| ≤ (1 + |x - z|^{-2}) k`. -/
theorem bpzWCL_norm_div_sq_le {k : ℝ} (hk : 0 ≤ k) (x z : ℂ) :
    ‖(k : ℂ) / (z - x) ^ 2‖ ≤ (1 + ‖x - z‖ ^ (-2 : ℝ)) * k := by
  have h0 := bpz_rpow_neg_two_nonneg (norm_nonneg (x - z))
  rcases eq_or_ne x z with rfl | hxz
  · refine le_trans (le_of_eq ?_) (mul_nonneg (by linarith) hk)
    rw [sub_self, zero_pow two_ne_zero, div_zero, norm_zero]
  · have ht : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hk, norm_sub_rev z x,
      bpz_rpow_neg_two ht.le]
    calc k / ‖x - z‖ ^ 2 = (‖x - z‖ ^ 2)⁻¹ * k := by rw [div_eq_inv_mul]
      _ ≤ (1 + (‖x - z‖ ^ 2)⁻¹) * k :=
          mul_le_mul_of_nonneg_right (by linarith [inv_nonneg.mpr (sq_nonneg ‖x - z‖)]) hk

/-! ### The pointwise identity -/

/-- Pointwise, the combination of the four integrands is the weight `k` times a partial-fraction
expression in `1 / (z - x)`. -/
theorem bpzWCL_pointwise {z x : ℂ} (hx : x ∈ bpzRegular z) :
    bpzWCL_comb (bpzWCL_F γ χ α₁ α₂ α₃ z Complex.reCLM 1 x)
        (bpzWCL_F γ χ α₁ α₂ α₃ z Complex.imCLM 1 x)
        (bpzWCL_F γ χ α₁ α₂ α₃ z Complex.reCLM Complex.I x)
        (bpzWCL_F γ χ α₁ α₂ α₃ z Complex.imCLM Complex.I x) =
      (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℂ) *
        (((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) +
          (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
            ((γ * α₂ / 2 : ℝ) : ℂ) * z) / (z - x) +
          ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) / (z - x) ^ 2) := by
  have hW := bpz_wirtinger_g_tildeWeight (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hx
  rw [bpz_g_coefficients hx] at hW
  unfold bpzWCL_comb bpzWCL_F
  simp only [Complex.reCLM_apply, Complex.imCLM_apply, show bpzG = bpzGfun from rfl]
  rw [bpzSoftWeight_zero_eq]
  generalize normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) = r
  push_cast at hW ⊢
  linear_combination (r : ℂ) * hW

/-! ### Integrability of the `x`-integrands -/

/-- On the regular region the integrand is dominated by a multiple of the weight `g`. -/
theorem bpzWCL_F_bound {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x ∈ bpzRegular z,
      |bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v x| ≤ A * bpzWCL_g γ χ α₁ α₂ α₃ z x := by
  obtain ⟨A, hA0, hA⟩ := bpz_g_fderiv_bound (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) hz0 hz1 ℓ v
  refine ⟨A, hA0, fun x hx => ?_⟩
  have hn : 0 ≤ normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) :=
    Real.rpow_nonneg (bpz_normPlus_pos x).le _
  unfold bpzWCL_F bpzWCL_g
  rw [abs_mul, abs_of_nonneg hn, bpzSoftWeight_zero_eq]
  refine (mul_le_mul_of_nonneg_right (hA x hx) hn).trans (le_of_eq ?_)
  ring

/-- The integrand is measurable. -/
theorem bpzWCL_F_measurable (z : ℂ) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Measurable (bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v) :=
  (measurable_fderiv_apply_const ℝ _ v).mul (bpz_measurable_normPlus.pow_const _)

/-- The integrand is integrable against any measure for which `g` is integrable and which charges
only the regular region. -/
theorem bpzWCL_F_integrable {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {m : Measure ℂ}
    (hg : Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m) (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : Integrable (bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v) m := by
  obtain ⟨A, -, hA⟩ := bpzWCL_F_bound (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
    hz0 hz1 ℓ v
  refine (hg.const_mul A).mono' (bpzWCL_F_measurable z ℓ v).aestronglyMeasurable ?_
  filter_upwards [hreg] with x hx
  rw [Real.norm_eq_abs]
  exact hA x hx

/-- A bound for the integral of the integrand, uniform in the measure. -/
theorem bpzWCL_norm_integral_F_le {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m : Measure ℂ, Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m →
      (∀ᵐ x ∂m, x ∈ bpzRegular z) →
        ‖∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v x ∂m‖ ≤ A * ∫ x, bpzWCL_g γ χ α₁ α₂ α₃ z x ∂m := by
  obtain ⟨A, hA0, hA⟩ := bpzWCL_F_bound (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
    hz0 hz1 ℓ v
  refine ⟨A, hA0, fun m hg hreg => ?_⟩
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hg.const_mul A) ?_
  filter_upwards [hreg] with x hx
  rw [Real.norm_eq_abs]
  exact hA x hx

/-- Integrability of `k` from integrability of `g`. -/
theorem bpzWCL_integrable_k {z : ℂ} {m : Measure ℂ}
    (hg : Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m) :
    Integrable (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z) m :=
  hg.mono' (measurable_bpzSoftWeight 0 z).aestronglyMeasurable (Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (bpzSoftWeight_nonneg 0 z x)]
    exact bpzWCL_le_g z x)

/-- Integrability of `k(x) / (z - x)` from integrability of `g`. -/
theorem bpzWCL_integrable_div {z : ℂ} {m : Measure ℂ}
    (hg : Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m) :
    Integrable (fun x => ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x)) m :=
  hg.mono' (((Complex.measurable_ofReal.comp (measurable_bpzSoftWeight 0 z)).div
    (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Eventually.of_forall fun x => bpzWCL_norm_div_le (bpzSoftWeight_nonneg 0 z x) x z)

/-- Integrability of `k(x) / (z - x)²` from integrability of `g`. -/
theorem bpzWCL_integrable_div_sq {z : ℂ} {m : Measure ℂ}
    (hg : Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m) :
    Integrable (fun x => ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ^ 2) m :=
  hg.mono' (((Complex.measurable_ofReal.comp (measurable_bpzSoftWeight 0 z)).div
    ((measurable_const.sub measurable_id).pow_const 2)).aestronglyMeasurable)
    (Eventually.of_forall fun x => bpzWCL_norm_div_sq_le (bpzSoftWeight_nonneg 0 z x) x z)

/-! ### The inner integral -/

/-- Integration of a combination `c₀ f + c₁ g + c₂ h` of integrable complex functions. -/
theorem bpzWCL_integral_three {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g h : α → ℂ}
    (c₀ c₁ c₂ : ℂ) (hf : Integrable f μ) (hg : Integrable g μ) (hh : Integrable h μ) :
    ∫ t, (c₀ * f t + c₁ * g t + c₂ * h t) ∂μ =
      c₀ * ∫ t, f t ∂μ + c₁ * ∫ t, g t ∂μ + c₂ * ∫ t, h t ∂μ := by
  have h0 : Integrable (fun t => c₀ * f t) μ := hf.const_mul c₀
  have h1 : Integrable (fun t => c₁ * g t) μ := hg.const_mul c₁
  have h2 : Integrable (fun t => c₂ * h t) μ := hh.const_mul c₂
  have h01 : Integrable (fun t => c₀ * f t + c₁ * g t) μ := h0.add h1
  rw [integral_add h01 h2, integral_add h0 h1, integral_const_mul, integral_const_mul,
    integral_const_mul]

/-- For a measure charging only the regular region and integrating `g`, the combination of the four
real integrals is `c₀ I + c₁ ∫ k/(z - x) + c₂ ∫ k/(z - x)²`. -/
theorem bpzWCL_inner {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {m : Measure ℂ}
    (hg : Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m) (hreg : ∀ᵐ x ∂m, x ∈ bpzRegular z) :
    bpzWCL_comb (∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.reCLM 1 x ∂m)
        (∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.imCLM 1 x ∂m)
        (∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.reCLM Complex.I x ∂m)
        (∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.imCLM Complex.I x ∂m) =
      ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) *
          ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m : ℝ) : ℂ) +
        (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
          ((γ * α₂ / 2 : ℝ) : ℂ) * z) *
          ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂m +
        ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) *
          ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ^ 2 ∂m := by
  have hF := bpzWCL_F_integrable (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) hz0 hz1 hg hreg
  rw [bpzWCL_integral_comb (hF Complex.reCLM 1) (hF Complex.imCLM 1)
    (hF Complex.reCLM Complex.I) (hF Complex.imCLM Complex.I)]
  have hk : Integrable (fun x => ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ)) m :=
    (bpzWCL_integrable_k hg).ofReal
  rw [← integral_complex_ofReal, ← bpzWCL_integral_three _ _ _ hk (bpzWCL_integrable_div hg)
    (bpzWCL_integrable_div_sq hg)]
  refine integral_congr_ae ?_
  filter_upwards [hreg] with x hx
  rw [bpzWCL_pointwise hx]
  ring

/-! ### The good samples and the dominating function -/

/-- The properties of a sample `m` of the chaos used in the pathwise computation: the weight `g`
is integrable, the four-point mass is positive, and `m` charges only the regular region. -/
def bpzWCL_Good (γ χ α₁ α₂ α₃ : ℝ) (z : ℂ) (m : Measure ℂ) : Prop :=
  Integrable (bpzWCL_g γ χ α₁ α₂ α₃ z) m ∧
    0 < ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m ∧ ∀ᵐ x ∂m, x ∈ bpzRegular z

/-- The dominating function `I^e ∫ g dm` of the outer integrands. -/
noncomputable def bpzWCL_dom (γ χ α₁ α₂ α₃ : ℝ) (z : ℂ) (e : ℝ) (m : Measure ℂ) : ℝ :=
  (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ e * ∫ x, bpzWCL_g γ χ α₁ α₂ α₃ z x ∂m

/-- Almost every sample is good, and the dominating function is integrable. -/
theorem bpzWCL_good {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {q : ℝ} (hq1 : 1 ≤ q) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    (∀ᵐ ω ∂P, bpzWCL_Good γ χ α₁ α₂ α₃ z (M ω)) ∧
      Integrable (fun ω => bpzWCL_dom γ χ α₁ α₂ α₃ z (-q) (M ω)) P := by
  refine ⟨?_, bpz_singular_dom_integrable P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1⟩
  filter_upwards [bpz_singular_integrable_ae P X hX hγ hγ2 M hM hχ hα₁ hα₂ hα₃ hq1 hz0 hz1,
    bpz_ae_regular P X hX hγ hγ2 M hM z] with ω hω hreg
  obtain ⟨hg, hpos, hfin⟩ := hω
  refine ⟨hg, ?_, hreg⟩
  have h := bpzSoftI_eq_toReal (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) 0 (M ω) z
  rw [bpzSoftI_eq_integral] at h
  rw [h]
  exact ENNReal.toReal_pos hpos.ne' hfin.ne

/-! ### Integrability of the `ω`-integrands -/

/-- The four-point mass is a measurable function of the sample. -/
theorem bpzWCL_measurable_I {Ω : Type*} [MeasurableSpace Ω] {M : Ω → Measure ℂ}
    (hMm : Measurable M) (z : ℂ) :
    Measurable fun ω => ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω :=
  (measurable_integral_measure (measurable_bpzSoftWeight 0 z)).comp hMm

/-- The outer integrands built from the real `x`-integrals are integrable. -/
theorem bpzWCL_outer_F {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℂ}
    (hMm : Measurable M) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) {e : ℝ}
    (hgood : ∀ᵐ ω ∂P, bpzWCL_Good γ χ α₁ α₂ α₃ z (M ω))
    (hdom : Integrable (fun ω => bpzWCL_dom γ χ α₁ α₂ α₃ z e (M ω)) P)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    Integrable (fun ω => (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e *
      ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v x ∂M ω) P := by
  obtain ⟨A, -, hA⟩ := bpzWCL_norm_integral_F_le (γ := γ) (χ := χ) (α₁ := α₁) (α₂ := α₂)
    (α₃ := α₃) hz0 hz1 ℓ v
  have hFm : Measurable fun ω => ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v x ∂M ω :=
    (measurable_integral_measure (bpzWCL_F_measurable z ℓ v)).comp hMm
  refine (hdom.const_mul A).mono'
    (((bpzWCL_measurable_I hMm z).pow_const e).mul hFm).aestronglyMeasurable ?_
  filter_upwards [hgood] with ω hω
  obtain ⟨hg, hpos, hreg⟩ := hω
  have h0 : 0 ≤ (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e := Real.rpow_nonneg hpos.le e
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, ← Real.norm_eq_abs]
  unfold bpzWCL_dom
  calc (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e *
        ‖∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v x ∂M ω‖
      ≤ (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e *
        (A * ∫ x, bpzWCL_g γ χ α₁ α₂ α₃ z x ∂M ω) :=
        mul_le_mul_of_nonneg_left (hA (M ω) hg hreg) h0
    _ = A * ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e *
        ∫ x, bpzWCL_g γ χ α₁ α₂ α₃ z x ∂M ω) := by ring

/-- The outer integrands built from a complex `x`-integral dominated by `g` are integrable. -/
theorem bpzWCL_outer_complex {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {M : Ω → Measure ℂ} (hMm : Measurable M) {z : ℂ} {e : ℝ} {f : ℂ → ℂ} (hf : Measurable f)
    (hfg : ∀ x, ‖f x‖ ≤ bpzWCL_g γ χ α₁ α₂ α₃ z x)
    (hgood : ∀ᵐ ω ∂P, bpzWCL_Good γ χ α₁ α₂ α₃ z (M ω))
    (hdom : Integrable (fun ω => bpzWCL_dom γ χ α₁ α₂ α₃ z e (M ω)) P) :
    Integrable (fun ω => (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e : ℝ) : ℂ) *
      ∫ x, f x ∂M ω) P := by
  have hfm : StronglyMeasurable fun ω => ∫ x, f x ∂M ω :=
    (bpz_stronglyMeasurable_integral_measure hf.stronglyMeasurable).comp_measurable hMm
  refine hdom.mono' ((Complex.measurable_ofReal.comp
    ((bpzWCL_measurable_I hMm z).pow_const e)).aestronglyMeasurable.mul hfm.aestronglyMeasurable) ?_
  filter_upwards [hgood] with ω hω
  obtain ⟨hg, hpos, -⟩ := hω
  have h0 : 0 ≤ (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ e := Real.rpow_nonneg hpos.le e
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le hg (Eventually.of_forall hfg)) h0

/-- The power `I^r` of the four-point mass is integrable if `I^{r-1} ∫ g` is. -/
theorem bpzWCL_outer_pow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {M : Ω → Measure ℂ}
    (hMm : Measurable M) {z : ℂ} {r : ℝ}
    (hgood : ∀ᵐ ω ∂P, bpzWCL_Good γ χ α₁ α₂ α₃ z (M ω))
    (hdom : Integrable (fun ω => bpzWCL_dom γ χ α₁ α₂ α₃ z (r - 1) (M ω)) P) :
    Integrable (fun ω => (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ r) P := by
  refine hdom.mono' ((bpzWCL_measurable_I hMm z).pow_const r).aestronglyMeasurable ?_
  filter_upwards [hgood] with ω hω
  obtain ⟨hg, hpos, -⟩ := hω
  have hk := bpzWCL_integrable_k hg
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hpos.le r)]
  unfold bpzWCL_dom
  calc (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ r
      = (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (r - 1) *
        ∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω := (bpzRpow_pred_mul hpos r).symm
    _ ≤ (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (r - 1) *
        ∫ x, bpzWCL_g γ χ α₁ α₂ α₃ z x ∂M ω :=
        mul_le_mul_of_nonneg_left (integral_mono hk hg (fun x => bpzWCL_le_g z x))
          (Real.rpow_nonneg hpos.le _)

/-! ### The pathwise identity and the main theorem -/

/-- The pathwise identity: for a good sample, the combination of the four `ω`-integrands is
`c₀ I^{-s} + c₁ I^{-s-1} ∫ k/(z - x) + c₂ I^{-s-1} ∫ k/(z - x)²`. -/
theorem bpzWCL_pathwise {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) (s : ℝ) {m : Measure ℂ}
    (hm : bpzWCL_Good γ χ α₁ α₂ α₃ z m) :
    bpzWCL_comb ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-(s + 1)) *
          ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.reCLM 1 x ∂m)
        ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-(s + 1)) *
          ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.imCLM 1 x ∂m)
        ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-(s + 1)) *
          ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.reCLM Complex.I x ∂m)
        ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-(s + 1)) *
          ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z Complex.imCLM Complex.I x ∂m) =
      ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) *
          (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-s) : ℝ) : ℂ) +
        (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
          ((γ * α₂ / 2 : ℝ) : ℂ) * z) *
          ((((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
            ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂m) +
        ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) *
          ((((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
            ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ^ 2 ∂m) := by
  obtain ⟨hg, hpos, hreg⟩ := hm
  rw [bpzWCL_comb_mul, bpzWCL_inner hz0 hz1 hg hreg, show -(s + 1) = -s - 1 by ring]
  have hI := bpzRpow_pred_mul hpos (-s)
  have hIc : (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-s - 1) : ℝ) : ℂ) *
      ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m : ℝ) : ℂ) =
        (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂m) ^ (-s) : ℝ) : ℂ) := by
    exact_mod_cast hI
  linear_combination (((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ)) * hIc

/-- **The combination of the four real Ward left sides.** For the test functions `Re g`, `Im g`
in the directions `1`, `i`, the combination `(L_{Re,1} + i L_{Im,1} - i L_{Re,i} + L_{Im,i}) / 2`
of the left sides `bpzWardLHS` is the explicit combination of the moments `J`, `E₁`, `D₁`. -/
theorem bpz_wardLHS_combination {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hMm : Measurable M) (hχ : 0 < χ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz0 : z ≠ 0)
    (hz1 : z ≠ 1) :
    ((bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM 1 : ℂ) +
        Complex.I * (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM 1 : ℂ) -
        Complex.I * (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM Complex.I : ℂ) +
        (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM Complex.I : ℂ)) / 2 =
      ((-1 - γ * χ / 2 + γ * (α₁ + α₂) / 2 : ℝ) : ℂ) * (bpzMomJ P M γ χ α₁ α₂ α₃ s z : ℂ) +
        (((γ * χ / 2 : ℝ) : ℂ) * (2 * z - 1) - ((γ * α₁ / 2 : ℝ) : ℂ) * (z - 1) -
          ((γ * α₂ / 2 : ℝ) : ℂ) * z) * bpzMomE1 P M γ χ α₁ α₂ α₃ s z +
        ((1 - γ * χ / 2 : ℝ) : ℂ) * (z * (z - 1)) * bpzMomD1 P M γ χ α₁ α₂ α₃ s z := by
  have hq1 : 1 ≤ s + 1 := by linarith
  obtain ⟨hgood, hdom⟩ := bpzWCL_good P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hq1 hz0 hz1
  have hdom' : Integrable (fun ω => bpzWCL_dom γ χ α₁ α₂ α₃ z (-s - 1) (M ω)) P := by
    rwa [show -s - 1 = -(s + 1) by ring]
  have hF := fun (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) => bpzWCL_outer_F hMm hz0 hz1 hgood hdom ℓ v
  have hJ : Integrable (fun ω => (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s) : ℝ) : ℂ))
      P := (bpzWCL_outer_pow hMm hgood (r := -s) hdom').ofReal
  have hkm : Measurable fun x => ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_bpzSoftWeight 0 z)
  have hE := bpzWCL_outer_complex hMm (f := fun x => ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) /
    (z - x)) (hkm.div (measurable_const.sub measurable_id))
    (fun x => bpzWCL_norm_div_le (bpzSoftWeight_nonneg 0 z x) x z) hgood hdom'
  have hD := bpzWCL_outer_complex hMm (f := fun x => ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) /
    (z - x) ^ 2) (hkm.div ((measurable_const.sub measurable_id).pow_const 2))
    (fun x => bpzWCL_norm_div_sq_le (bpzSoftWeight_nonneg 0 z x) x z) hgood hdom'
  have hLHS : ∀ (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ), bpzWardLHS P M γ χ α₁ α₂ α₃ s z ℓ v =
      ∫ ω, (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-(s + 1)) *
        ∫ x, bpzWCL_F γ χ α₁ α₂ α₃ z ℓ v x ∂M ω ∂P := fun _ _ => rfl
  show bpzWCL_comb (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM 1)
    (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM 1)
    (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.reCLM Complex.I)
    (bpzWardLHS P M γ χ α₁ α₂ α₃ s z Complex.imCLM Complex.I) = _
  rw [hLHS, hLHS, hLHS, hLHS, bpzWCL_integral_comb (hF _ _) (hF _ _) (hF _ _) (hF _ _)]
  rw [integral_congr_ae (hgood.mono fun ω hω => bpzWCL_pathwise hz0 hz1 s hω)]
  rw [bpzWCL_integral_three _ _ _ hJ hE hD, integral_complex_ofReal]
  rfl

end DOZZ.Proofs
