/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftFarCont
public import DOZZ.FourPoint.BPZ.SoftLimitC

/-! # Wirtinger combinations of the derivative masses

The Wirtinger functional `L ↦ (L 1 − i L i) / 2` on real-linear functionals `ℂ →L[ℝ] ℝ` and its
second-order analogue `B ↦ (B 1 1 − i B 1 i − i B i 1 − B i i) / 4` on real bilinear forms are
continuous real-linear maps into `ℂ`, hence commute with Bochner integration. For `ε = 0`, a
nonnegative measurable weight `w` and a measure `m` with no atom at the root `z`, this turns the
derivative masses `bpzSoftMassDeriv a 0 w m z` and `bpzSoftMassDeriv2 a 0 w m z` into the
meromorphic integrals `a ∫ |x − z|^{2a} w(x) / (z − x) dm(x)` and
`a (a − 1) ∫ |x − z|^{2a} w(x) / (z − x)² dm(x)`. -/

@[expose] public section

open MeasureTheory

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

/-! ### The Wirtinger functionals -/

/-- The Wirtinger functional `L ↦ (L 1 − i L i)/2` as a continuous real-linear map. -/
noncomputable def bpzWirtL : (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ :=
  (1 / 2 : ℝ) • (Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ (1 : ℂ)) -
    Complex.I • Complex.ofRealCLM.comp (ContinuousLinearMap.apply ℝ ℝ Complex.I))

/-- The Wirtinger functional evaluated at `L`. -/
theorem bpzWirtL_apply (L : ℂ →L[ℝ] ℝ) :
    bpzWirtL L = ((L 1 : ℂ) - Complex.I * (L Complex.I : ℂ)) / 2 := by
  simp [bpzWirtL]
  ring

/-- Evaluation of a real bilinear form at a pair of vectors, as a continuous linear functional on
the space of bilinear forms. -/
noncomputable def bpzEvalBilin (h k : ℂ) : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ k).comp (ContinuousLinearMap.apply ℝ (ℂ →L[ℝ] ℝ) h)

/-- The evaluation functional `bpzEvalBilin h k` evaluates a bilinear form at `(h, k)`. -/
theorem bpzEvalBilin_apply (h k : ℂ) (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) : bpzEvalBilin h k B = B h k :=
  rfl

/-- The second Wirtinger functional on real bilinear forms. -/
noncomputable def bpzWirt2L : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →L[ℝ] ℂ :=
  (1 / 4 : ℝ) • (Complex.ofRealCLM.comp (bpzEvalBilin 1 1) -
    Complex.I • Complex.ofRealCLM.comp (bpzEvalBilin 1 Complex.I) -
    Complex.I • Complex.ofRealCLM.comp (bpzEvalBilin Complex.I 1) -
    Complex.ofRealCLM.comp (bpzEvalBilin Complex.I Complex.I))

/-- The second Wirtinger functional evaluated at `B`. -/
theorem bpzWirt2L_apply (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :
    bpzWirt2L B = ((B 1 1 : ℂ) - Complex.I * (B 1 Complex.I : ℂ) -
      Complex.I * (B Complex.I 1 : ℂ) - (B Complex.I Complex.I : ℂ)) / 4 := by
  simp [bpzWirt2L, bpzEvalBilin_apply]
  ring

/-- On the rank-one form `(h, k) ↦ L h * L k` the second Wirtinger functional is the square of
the first. -/
theorem bpzWirt2L_smulRight (L : ℂ →L[ℝ] ℝ) : bpzWirt2L (L.smulRight L) = bpzWirtL L ^ 2 := by
  rw [bpzWirt2L_apply, bpzWirtL_apply]
  simp only [ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  push_cast
  linear_combination (-((L Complex.I : ℂ) ^ 2) / 4) * Complex.I_sq

/-! ### Integrability of the meromorphic integrands -/

/-- `|u|^{2a} = ‖u‖^{2a}`, with `|u|` the complex modulus written through `normSq`. -/
theorem bpz_normSq_rpow_eq (a : ℝ) (u : ℂ) : Complex.normSq u ^ a = ‖u‖ ^ (2 * a) := by
  rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1

/-- Off the root, the modulus of the meromorphic integrand is the weight times a power of the
distance to the root. -/
theorem bpz_norm_div_root_pow (a : ℝ) (n : ℕ) {w : ℝ} (hw : 0 ≤ w) {x z : ℂ} (hxz : x ≠ z) :
    ‖((Complex.normSq (x - z) ^ a * w : ℝ) : ℂ) / (z - x) ^ n‖ =
      w * ‖x - z‖ ^ (2 * a - n) := by
  have hu : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hnn : 0 ≤ Complex.normSq (x - z) ^ a * w :=
    mul_nonneg (Real.rpow_nonneg (Complex.normSq_nonneg _) a) hw
  rw [norm_div, norm_pow, norm_sub_rev, Complex.norm_real, Real.norm_of_nonneg hnn,
    bpz_normSq_rpow_eq, Real.rpow_sub hu, Real.rpow_natCast]
  field_simp

/-- A measure with no atom at `z` gives full mass to `{x | x ≠ z}`. -/
theorem bpz_ae_ne_of_measure_singleton {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0) :
    ∀ᵐ x ∂m, x ≠ z := by
  rw [ae_iff]
  simpa using hz

/-- The meromorphic integrand is measurable. -/
theorem bpz_measurable_div_root_pow (a : ℝ) {w : ℂ → ℝ} (hw : Measurable w) (z : ℂ) (n : ℕ) :
    Measurable (fun x : ℂ => ((Complex.normSq (x - z) ^ a * w x : ℝ) : ℂ) / (z - x) ^ n) := by
  have h1 : Measurable (fun x : ℂ => Complex.normSq (x - z) ^ a * w x) :=
    ((Complex.continuous_normSq.measurable.comp (measurable_id.sub_const z)).pow_const a).mul hw
  exact (Complex.measurable_ofReal.comp h1).div ((measurable_const.sub measurable_id).pow_const n)

/-- For a measure without an atom at the root `z`, the meromorphic integrand
`|x − z|^{2a} w(x) / (z − x)` is integrable as soon as `w(x) |x − z|^{2a−1}` is. -/
theorem bpz_integrable_div_root {a : ℝ} {w : ℂ → ℝ} (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 1)) m) :
    Integrable (fun x => ((Complex.normSq (x - z) ^ a * w x : ℝ) : ℂ) / (z - x)) m := by
  refine Integrable.mono' hint ?_ ?_
  · simpa using (bpz_measurable_div_root_pow a hw z 1).aestronglyMeasurable
  · filter_upwards [bpz_ae_ne_of_measure_singleton hz] with x hx
    have h := bpz_norm_div_root_pow a 1 (hw0 x) hx
    simpa using h.le

/-- For a measure without an atom at the root `z`, the meromorphic integrand
`|x − z|^{2a} w(x) / (z − x)²` is integrable as soon as `w(x) |x − z|^{2a−2}` is. -/
theorem bpz_integrable_div_root_sq {a : ℝ} {w : ℂ → ℝ} (hw : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 2)) m) :
    Integrable (fun x => ((Complex.normSq (x - z) ^ a * w x : ℝ) : ℂ) / (z - x) ^ 2) m := by
  refine Integrable.mono' hint ?_ ?_
  · exact (bpz_measurable_div_root_pow a hw z 2).aestronglyMeasurable
  · filter_upwards [bpz_ae_ne_of_measure_singleton hz] with x hx
    have h := bpz_norm_div_root_pow a 2 (hw0 x) hx
    simpa using h.le

/-! ### Integrability of the derivative integrands at `ε = 0` -/

/-- For `0 < a ≤ 1` and a measure without an atom at the root `z`, the first-derivative integrand
at `ε = 0` is integrable as soon as `w(x) |x − z|^{2a−1}` is. -/
theorem bpz_integrable_softDeriv_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 1)) m) :
    Integrable (fun x => w x • bpzSoftDeriv a 0 x z) m := by
  refine Integrable.mono' (hint.const_mul (2 * a))
    (hw.aestronglyMeasurable.smul (bpzSoftDeriv_aestronglyMeasurable a 0 z m)) ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton hz] with x hx
  rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  calc w x * ‖bpzSoftDeriv a 0 x z‖ ≤ w x * (2 * a * ‖x - z‖ ^ (2 * a - 1)) :=
        mul_le_mul_of_nonneg_left (norm_bpzSoftDeriv_le_uniform ha ha1 hx) (hw0 x)
    _ = 2 * a * (w x * ‖x - z‖ ^ (2 * a - 1)) := by ring

/-- For `0 < a ≤ 1` and a measure without an atom at the root `z`, the second-derivative
integrand at `ε = 0` is integrable as soon as `w(x) |x − z|^{2a−2}` is. (Its statement involves
the local instance shortcuts for the space of bilinear forms.) -/
theorem bpz_integrable_softDeriv2_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 2)) m) :
    Integrable (fun x => w x • bpzSoftDeriv2 a 0 x z) m := by
  refine Integrable.mono' (hint.const_mul (4 * a * (1 - a) + 2 * a))
    (hw.aestronglyMeasurable.smul (bpzSoftDeriv2_aestronglyMeasurable a 0 z m)) ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton hz] with x hx
  rw [norm_smul, Real.norm_of_nonneg (hw0 x)]
  calc w x * ‖bpzSoftDeriv2 a 0 x z‖
      ≤ w x * ((4 * a * (1 - a) + 2 * a) * ‖x - z‖ ^ (2 * a - 2)) :=
        mul_le_mul_of_nonneg_left (norm_bpzSoftDeriv2_le_uniform ha ha1 hx) (hw0 x)
    _ = (4 * a * (1 - a) + 2 * a) * (w x * ‖x - z‖ ^ (2 * a - 2)) := by ring

/-! ### The Wirtinger combinations of the derivative masses -/

/-- At `ε = 0` the Wirtinger combination of the first derivative mass is the meromorphic integral
`a ∫ |x − z|^{2a} w(x) / (z − x) dm(x)`. -/
theorem bpzWirtL_softMassDeriv_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 1)) m) :
    bpzWirtL (bpzSoftMassDeriv a 0 w m z) =
      (a : ℂ) * ∫ x, ((Complex.normSq (x - z) ^ a * w x : ℝ) : ℂ) / (z - x) ∂m := by
  unfold bpzSoftMassDeriv
  rw [← ContinuousLinearMap.integral_comp_comm bpzWirtL
    (bpz_integrable_softDeriv_zero ha ha1 hw hw0 hz hint), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton hz] with x hx
  rw [map_smul, Complex.real_smul, bpzWirtL_apply, bpzSoftDeriv_wirtinger_zero a hx]
  push_cast
  ring

/-- At `ε = 0` the second Wirtinger combination of the second derivative mass is the meromorphic
integral `a (a − 1) ∫ |x − z|^{2a} w(x) / (z − x)² dm(x)`. -/
theorem bpzWirt2L_softMassDeriv2_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {w : ℂ → ℝ}
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) {m : Measure ℂ} {z : ℂ} (hz : m {z} = 0)
    (hint : Integrable (fun x => w x * ‖x - z‖ ^ (2 * a - 2)) m) :
    bpzWirt2L (bpzSoftMassDeriv2 a 0 w m z) =
      ((a * (a - 1) : ℝ) : ℂ) *
        ∫ x, ((Complex.normSq (x - z) ^ a * w x : ℝ) : ℂ) / (z - x) ^ 2 ∂m := by
  unfold bpzSoftMassDeriv2
  rw [← ContinuousLinearMap.integral_comp_comm bpzWirt2L
    (bpz_integrable_softDeriv2_zero ha ha1 hw hw0 hz hint), ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [bpz_ae_ne_of_measure_singleton hz] with x hx
  have hsym := bpzSoftDeriv2_symm a 0 x z Complex.I 1
  have hw2 := bpzSoftDeriv2_wirtinger_zero a hx
  rw [map_smul, Complex.real_smul, bpzWirt2L_apply, hsym]
  push_cast at hw2 ⊢
  linear_combination (w x : ℂ) * hw2

end DOZZ.Proofs
