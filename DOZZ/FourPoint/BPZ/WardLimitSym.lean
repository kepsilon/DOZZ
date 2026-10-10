/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimitKernel
public import DOZZ.FourPoint.BPZ.WeakConvGMC

/-! # Symmetrization of the cutoff Ward identity

The right side of the cutoff Ward identity integrates `φ k₁ Ŷ_v` against the cutoff chaos, where
`Ŷ_v` integrates the kernel derivatives against the cutoff chaos (cutoff region) and the limit
chaos (far region). Since `Λ_r'` is odd, the cutoff-region double integral equals the double
integral of the antisymmetrized kernel `(φ(x)ρ(y) − φ(y)ρ(x)) k₁(x) k₁(y) Λ_r'(x − y)v / 2`,
which is bounded uniformly in the cutoff because `φ(x)ρ(y) − φ(y)ρ(x) = φ(x) − φ(y)` near the
diagonal. The far-region part is a test function of `x` built from the limit chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The antisymmetrized kernel `(φ(x)ρ(y) − φ(y)ρ(x)) k(x) k(y) L(x − y) / 2`. -/
noncomputable def bpzSymKer (φ ρ k L : ℂ → ℝ) (x y : ℂ) : ℝ :=
  (φ x * ρ y - φ y * ρ x) * (k x * k y) * L (x - y) / 2

/-- The far-region test function `x ↦ ∫ (1 − ρ(y)) k₂(y) φ(x) k(x) L(x − y) dm(y)`. -/
noncomputable def bpzMixTest (φ ρ k k₂ L : ℂ → ℝ) (m : Measure ℂ) (x : ℂ) : ℝ :=
  ∫ y, (1 - ρ y) * k₂ y * (φ x * k x * L (x - y)) ∂m

theorem measurable_bpzSymKer {φ ρ k L : ℂ → ℝ} (hφ : Measurable φ) (hρ : Measurable ρ)
    (hk : Measurable k) (hL : Measurable L) : Measurable (Function.uncurry (bpzSymKer φ ρ k L)) := by
  unfold bpzSymKer
  have hd : Measurable (fun p : ℂ × ℂ => p.1 - p.2) := measurable_fst.sub measurable_snd
  exact (((((hφ.comp measurable_fst).mul (hρ.comp measurable_snd)).sub
    ((hφ.comp measurable_snd).mul (hρ.comp measurable_fst))).mul
      ((hk.comp measurable_fst).mul (hk.comp measurable_snd))).mul (hL.comp hd)).div_const _

/-- Antisymmetrization of a double integral. -/
theorem bpz_integral_integral_symm {m : Measure ℂ} [SFinite m] {F : ℂ → ℂ → ℝ}
    (hF : Integrable (Function.uncurry F) (m.prod m)) :
    ∫ x, ∫ y, F x y ∂m ∂m = ∫ x, ∫ y, (F x y + F y x) / 2 ∂m ∂m := by
  have hF' : Integrable (fun p : ℂ × ℂ => F p.1 p.2) (m.prod m) := hF
  have hFs : Integrable (fun p : ℂ × ℂ => F p.2 p.1) (m.prod m) := hF.swap
  have hsum : Integrable (fun p : ℂ × ℂ => (F p.1 p.2 + F p.2 p.1) / 2) (m.prod m) :=
    (hF'.add hFs).div_const 2
  rw [← integral_prod (fun p : ℂ × ℂ => F p.1 p.2) hF',
    ← integral_prod (fun p : ℂ × ℂ => (F p.1 p.2 + F p.2 p.1) / 2) hsum,
    integral_div, integral_add hF' hFs]
  have hswap : ∫ p : ℂ × ℂ, F p.2 p.1 ∂(m.prod m) = ∫ p : ℂ × ℂ, F p.1 p.2 ∂(m.prod m) :=
    integral_prod_swap (fun p : ℂ × ℂ => F p.1 p.2)
  rw [hswap]
  ring

theorem bpz_integrable_prod_of_bdd {m : Measure ℂ} [IsFiniteMeasure m] {F : ℂ → ℂ → ℝ}
    (hF : Measurable (Function.uncurry F)) {C : ℝ} (hC : ∀ x y, |F x y| ≤ C) :
    Integrable (Function.uncurry F) (m.prod m) :=
  Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall fun p => by
    rw [Real.norm_eq_abs]; exact hC p.1 p.2)

/-- The cutoff-region double integral equals the antisymmetrized one. -/
theorem bpz_integral_symKer {m : Measure ℂ} [IsFiniteMeasure m] {φ ρ k L : ℂ → ℝ}
    (hφ : Measurable φ) (hρ : Measurable ρ) (hk : Measurable k) (hL : Measurable L)
    (hodd : ∀ w, L (-w) = -L w) {C : ℝ}
    (hC : ∀ x y, |φ x * k x * (ρ y * k y) * L (x - y)| ≤ C) :
    ∫ x, ∫ y, φ x * k x * (ρ y * k y) * L (x - y) ∂m ∂m =
      ∫ x, ∫ y, bpzSymKer φ ρ k L x y ∂m ∂m := by
  have hFm : Measurable (Function.uncurry fun x y => φ x * k x * (ρ y * k y) * L (x - y)) :=
    (((hφ.comp measurable_fst).mul (hk.comp measurable_fst)).mul
      ((hρ.comp measurable_snd).mul (hk.comp measurable_snd))).mul
      (hL.comp (measurable_fst.sub measurable_snd))
  rw [bpz_integral_integral_symm (bpz_integrable_prod_of_bdd hFm hC)]
  congr 1
  funext x
  congr 1
  funext y
  unfold bpzSymKer
  rw [show y - x = -(x - y) by ring, hodd]
  ring

/-- **Pathwise symmetrization of the right side of the cutoff Ward identity.** -/
theorem bpz_cutoff_sym_identity {γ r : ℝ} {φ ρ k₁ k₂ : ℂ → ℝ} {m₁ m₂ : Measure ℂ}
    [IsFiniteMeasure m₁] [IsFiniteMeasure m₂] (hφ : Measurable φ) (hρ : Measurable ρ) (hk₁ : Measurable k₁)
    (hk₂ : Measurable k₂) {C₁ C₂ : ℝ} (hφk : ∀ x, |φ x * k₁ x| ≤ C₁)
    (hρk : ∀ y, |ρ y * k₁ y| ≤ C₂) (h₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂) (v : ℂ) :
    ∫ x, φ x * k₁ x * bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂ ∂m₁ =
      γ ^ 2 * (∫ x, ∫ y, bpzSymKer φ ρ k₁ (fun w => bpzLamDeriv r w v) x y ∂m₁ ∂m₁ +
        ∫ x, bpzMixTest φ ρ k₁ k₂ (fun w => bpzTruncLogDeriv r w v) m₂ x ∂m₁) := by
  set L : ℂ → ℝ := fun w => bpzLamDeriv r w v with hLdef
  set T : ℂ → ℝ := fun w => bpzTruncLogDeriv r w v with hTdef
  have hLm : Measurable L :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzLamDeriv r)
  have hTm : Measurable T :=
    (ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp (measurable_bpzTruncLogDeriv r)
  have hLb : ∀ w, |L w| ≤ Real.exp r * ‖v‖ := fun w => by
    rw [← Real.norm_eq_abs]
    exact ((bpzLamDeriv r w).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_bpzLamDeriv_le_exp r w) (norm_nonneg v))
  have hTb : ∀ w, |T w| ≤ Real.exp r * ‖v‖ := fun w => by
    rw [← Real.norm_eq_abs]
    exact ((bpzTruncLogDeriv r w).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_bpzTruncLogDeriv_le r w).1 (norm_nonneg v))
  have hC₁ : 0 ≤ C₁ := (abs_nonneg _).trans (hφk 0)
  have hC₂ : 0 ≤ C₂ := (abs_nonneg _).trans (hρk 0)
  set Cb : ℝ := C₁ * C₂ * (Real.exp r * ‖v‖)
  have hFb : ∀ x y, |φ x * k₁ x * (ρ y * k₁ y) * L (x - y)| ≤ Cb := fun x y => by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hφk x) (hρk y) (abs_nonneg _) hC₁) (hLb _) (abs_nonneg _)
      (by positivity)
  have hFm : Measurable (Function.uncurry fun x y => φ x * k₁ x * (ρ y * k₁ y) * L (x - y)) :=
    (((hφ.comp measurable_fst).mul (hk₁.comp measurable_fst)).mul
      ((hρ.comp measurable_snd).mul (hk₁.comp measurable_snd))).mul
      (hLm.comp (measurable_fst.sub measurable_snd))
  -- pointwise decomposition
  have hpt : ∀ x, φ x * k₁ x * bpzMixedDerivReal γ r ρ k₁ k₂ x v m₁ m₂ =
      γ ^ 2 * ((∫ y, φ x * k₁ x * (ρ y * k₁ y) * L (x - y) ∂m₁) +
        bpzMixTest φ ρ k₁ k₂ T m₂ x) := by
    intro x
    unfold bpzMixedDerivReal bpzMixTest
    rw [mul_add, mul_add, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul]
    congr 1
    · congr 1; funext y; simp only [hLdef]; ring
    · congr 1; funext y; simp only [hTdef]; ring
  simp_rw [hpt]
  have hI1 : Integrable (fun x => ∫ y, φ x * k₁ x * (ρ y * k₁ y) * L (x - y) ∂m₁) m₁ :=
    bpz_integrable_inner hFm hFb
  have hMm : Measurable (fun x => bpzMixTest φ ρ k₁ k₂ T m₂ x) := by
    have hj : Measurable (fun p : ℂ × ℂ => (1 - ρ p.2) * k₂ p.2 * (φ p.1 * k₁ p.1 * T (p.1 - p.2))) :=
      (((measurable_const.sub (hρ.comp measurable_snd)).mul (hk₂.comp measurable_snd)).mul
        (((hφ.comp measurable_fst).mul (hk₁.comp measurable_fst)).mul
          (hTm.comp (measurable_fst.sub measurable_snd))))
    unfold bpzMixTest
    exact (hj.stronglyMeasurable.integral_prod_right' (ν := m₂)).measurable
  have hI2 : Integrable (fun x => bpzMixTest φ ρ k₁ k₂ T m₂ x) m₁ := by
    refine integrable_of_bdd_finite hMm (C := C₁ * (Real.exp r * ‖v‖) *
      ∫ y, |(1 - ρ y) * k₂ y| ∂m₂) fun x => ?_
    unfold bpzMixTest
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
      (h₂.abs.const_mul _) (Eventually.of_forall fun y => ?_)
    dsimp only
    have := mul_le_mul (hφk x) (hTb (x - y)) (abs_nonneg _) hC₁
    rw [Real.norm_eq_abs, abs_mul ((1 - ρ y) * k₂ y), abs_mul (φ x * k₁ x)]
    calc |(1 - ρ y) * k₂ y| * (|φ x * k₁ x| * |T (x - y)|)
        ≤ |(1 - ρ y) * k₂ y| * (C₁ * (Real.exp r * ‖v‖)) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = C₁ * (Real.exp r * ‖v‖) * |(1 - ρ y) * k₂ y| := by ring
  rw [integral_const_mul, integral_add hI1 hI2,
    bpz_integral_symKer hφ hρ hk₁ hLm (fun w => by simp only [hLdef]; rw [bpzLamDeriv_neg]; rfl)
      hFb]

end DOZZ.Proofs
