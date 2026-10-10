/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardLimit

/-! # The Ward identity without the auxiliary cutoff

In the limit both the cutoff region and the far region are integrated against the limit chaos, so
the far-region term can be antisymmetrized as well. Adding the two antisymmetrized kernels removes
the cutoff function `ρ`:

  `E[I^{-q} ∫ ∂_v(φ k̃) |x|₊^{4+γ²q} dM] = q E[I^{-q-1} γ² ∬ (φ(x) − φ(y)) k(x) k(y) K_v(x − y)/2 dM dM]`

with `I = ∫ k dM`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]
variable {γ q δ : ℝ} {ρ kt k₂ φ : ℂ → ℝ} {D : Set ℂ}
variable {P : Measure Ω} {X : Ω → Distr} {M : Ω → Measure ℂ} {Xc : Ω → ℂ → ℝ → ℝ}

namespace BPZLimitData

/-- The difference-quotient kernel is bounded by `Lip(φ)|v|/2` times the weights. -/
theorem abs_diffKer_le (hd : BPZLimitData γ q δ ρ kt k₂ φ D) {Lφ : ℝ≥0} (hLφ : LipschitzWith Lφ φ)
    (v x y : ℂ) :
    |(φ x - φ y) * (k₂ x * k₂ y) * bpzKern v (x - y) / 2| ≤
      (Lφ : ℝ) * ‖v‖ / 2 * (k₂ x * k₂ y) := by
  have hk : 0 ≤ k₂ x * k₂ y := mul_nonneg (hd.k₂_nonneg x) (hd.k₂_nonneg y)
  rcases eq_or_ne x y with rfl | hxy
  · simp only [sub_self, zero_mul, zero_div, abs_zero]; positivity
  have hxy' : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hlip : |φ x - φ y| ≤ Lφ * ‖x - y‖ := by
    rw [← Real.dist_eq, ← dist_eq_norm]; exact hLφ.dist_le_mul x y
  rw [abs_div, abs_two, abs_mul, abs_mul, abs_of_nonneg hk]
  calc |φ x - φ y| * (k₂ x * k₂ y) * |bpzKern v (x - y)| / 2
      ≤ (Lφ * ‖x - y‖) * (k₂ x * k₂ y) * (‖v‖ / ‖x - y‖) / 2 := by
        gcongr
        exact abs_bpzKern_le v _
    _ = (Lφ : ℝ) * ‖v‖ / 2 * (k₂ x * k₂ y) := by field_simp

/-- Pathwise: the two antisymmetrized limit terms combine into the difference-quotient kernel. -/
theorem sym_add_mix_eq (hd : BPZLimitData γ q δ ρ kt k₂ φ D) (v : ℂ) {m : Measure ℂ}
    [IsFiniteMeasure m] (hk₂ : Integrable k₂ m) :
    (∫ x, ∫ y, bpzSymKer φ ρ k₂ (bpzKern v) x y ∂m ∂m) +
        ∫ x, bpzMixTest φ ρ k₂ k₂ (bpzKern v) m x ∂m =
      ∫ x, ∫ y, (φ x - φ y) * (k₂ x * k₂ y) * bpzKern v (x - y) / 2 ∂m ∂m := by
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  obtain ⟨B, hB0, hB⟩ := hd.phi_bdd
  obtain ⟨Lφ, hLφ⟩ := hd.φ_lip
  have hδ := hd.δ_pos
  have hk₂m := hd.k₂_meas
  have hφm := hd.phi_cont.measurable
  have hKm := measurable_bpzKern v
  have hρk : ∀ x, ρ x * |k₂ x| ≤ K := fun x => (hd.rho_abs_cutWeight_le hK hK0 0 x).2
  -- the three kernels as functions on the product
  set S : ℂ → ℂ → ℝ := bpzSymKer φ ρ k₂ (bpzKern v) with hSdef
  set F : ℂ → ℂ → ℝ := fun x y => (1 - ρ y) * k₂ y * (φ x * k₂ x * bpzKern v (x - y)) with hF
  set G : ℂ → ℂ → ℝ := fun x y => (φ x - φ y) * (k₂ x * k₂ y) * bpzKern v (x - y) / 2 with hG
  have hSm : Measurable (Function.uncurry S) :=
    measurable_bpzSymKer hφm hd.ρ_meas hk₂m hKm
  have hFm : Measurable (Function.uncurry F) :=
    (((measurable_const.sub (hd.ρ_meas.comp measurable_snd)).mul (hk₂m.comp measurable_snd)).mul
      (((hφm.comp measurable_fst).mul (hk₂m.comp measurable_fst)).mul
        (hKm.comp (measurable_fst.sub measurable_snd))))
  have hGm : Measurable (Function.uncurry G) :=
    (((((hφm.comp measurable_fst).sub (hφm.comp measurable_snd)).mul
      ((hk₂m.comp measurable_fst).mul (hk₂m.comp measurable_snd))).mul
        (hKm.comp (measurable_fst.sub measurable_snd))).div_const _)
  have hprod : Integrable (fun p : ℂ × ℂ => k₂ p.1 * k₂ p.2) (m.prod m) := hk₂.mul_prod hk₂
  -- integrability on the product
  have hSi : Integrable (fun p : ℂ × ℂ => S p.1 p.2) (m.prod m) := by
    have hb : ∀ x y, |S x y| ≤ 2 * ‖v‖ * ((Lφ : ℝ) + B / δ) * (K * K) := by
      intro x y
      refine (hd.abs_symKer_le hB hLφ zero_le_two v (fun w => (abs_bpzKern_le v w).trans
        (div_le_div_of_nonneg_right (by linarith [norm_nonneg v]) (norm_nonneg w))) x y).trans ?_
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hρk x) (hρk y)
        (mul_nonneg (hd.ρ_nonneg y) (abs_nonneg _)) hK0) (by positivity)
    exact bpz_integrable_prod_of_bdd hSm hb
  have hFi : Integrable (fun p : ℂ × ℂ => F p.1 p.2) (m.prod m) := by
    refine ((integrable_const (1 : ℝ)).mul_prod hk₂).const_mul (1 * ‖v‖ / (2 * δ) * B * K)
      |>.mono' hFm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]
    have h := hd.abs_mixIntegrand_le hB zero_le_one v (L := bpzKern v) (k := k₂)
      (fun w => by rw [one_mul]; exact abs_bpzKern_le v w) hρk p.1 p.2
    refine h.trans ?_
    have hw : (1 - ρ p.2) * k₂ p.2 ≤ k₂ p.2 := by
      have := hd.ρ_nonneg p.2; have := hd.k₂_nonneg p.2; nlinarith
    calc 1 * ‖v‖ / (2 * δ) * B * K * ((1 - ρ p.2) * k₂ p.2)
        ≤ 1 * ‖v‖ / (2 * δ) * B * K * k₂ p.2 :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = 1 * ‖v‖ / (2 * δ) * B * K * (1 * k₂ p.2) := by ring
  have hGi : Integrable (fun p : ℂ × ℂ => G p.1 p.2) (m.prod m) :=
    (hprod.const_mul ((Lφ : ℝ) * ‖v‖ / 2)).mono' hGm.aestronglyMeasurable
      (Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]; exact hd.abs_diffKer_le hLφ v p.1 p.2)
  -- the mixed term as a double integral and its antisymmetrization
  have hmix : ∫ x, bpzMixTest φ ρ k₂ k₂ (bpzKern v) m x ∂m = ∫ x, ∫ y, F x y ∂m ∂m := rfl
  rw [hmix, bpz_integral_integral_symm (F := F) hFi]
  have hFs : Integrable (fun p : ℂ × ℂ => (F p.1 p.2 + F p.2 p.1) / 2) (m.prod m) :=
    (hFi.add hFi.swap).div_const 2
  rw [← integral_prod (fun p : ℂ × ℂ => S p.1 p.2) hSi,
    ← integral_prod (fun p : ℂ × ℂ => (F p.1 p.2 + F p.2 p.1) / 2) hFs,
    ← integral_prod (fun p : ℂ × ℂ => G p.1 p.2) hGi, ← integral_add hSi hFs]
  congr 1
  funext p
  simp only [hSdef, hF, hG, bpzSymKer]
  rw [show p.2 - p.1 = -(p.1 - p.2) by ring, bpzKern_neg]
  ring

/-- **The Ward identity in the limit, without the auxiliary cutoff.** -/
theorem ward_limit_clean (hd : BPZLimitData γ q δ ρ kt k₂ φ D)
    (hp : BPZWardProb P X γ M Xc ρ k₂ D) (v : ℂ) :
    ∫ ω, (∫ x, k₂ x ∂M ω) ^ (-q) *
        ∫ x, fderiv ℝ (fun x => φ x * kt x) x v * normPlus x ^ (4 + γ ^ 2 * q) ∂M ω ∂P =
      ∫ ω, q * ((∫ x, k₂ x ∂M ω) ^ (-q - 1) *
        (γ ^ 2 * ∫ x, ∫ y, (φ x - φ y) * (k₂ x * k₂ y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω))
        ∂P := by
  have hlim := hd.ward_limit hp v
  obtain ⟨K, hK0, hK⟩ := hd.cutWeight_bound
  have hρk2 : ∀ y, |ρ y * k₂ y| ≤ K := fun y => by
    rw [abs_mul, abs_of_nonneg (hd.ρ_nonneg y)]
    exact (hd.rho_abs_cutWeight_le hK hK0 0 y).2
  -- almost surely the weight is integrable and the masses add up
  have hgood : ∀ᵐ ω ∂P, Integrable k₂ (M ω) ∧
      ∫ y, ρ y * k₂ y ∂M ω + ∫ y, (1 - ρ y) * k₂ y ∂M ω = ∫ x, k₂ x ∂M ω := by
    filter_upwards [hp.k₂_int] with ω hω
    have := hp.hM.1 ω
    have h1 : Integrable (fun y => ρ y * k₂ y) (M ω) :=
      integrable_of_bdd_finite (hd.ρ_meas.mul hd.k₂_meas) hρk2
    have hsum : Integrable (fun y => ρ y * k₂ y + (1 - ρ y) * k₂ y) (M ω) := h1.add hω
    have heq : (fun y => ρ y * k₂ y + (1 - ρ y) * k₂ y) = k₂ := by funext y; ring
    rw [heq] at hsum
    refine ⟨hsum, ?_⟩
    rw [← integral_add h1 hω]
    congr 1
  calc _ = ∫ ω, (∫ y, ρ y * k₂ y ∂M ω + ∫ y, (1 - ρ y) * k₂ y ∂M ω) ^ (-q) *
        ∫ x, fderiv ℝ (fun x => φ x * kt x) x v * normPlus x ^ (4 + γ ^ 2 * q) ∂M ω ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hgood] with ω hω
        rw [hω.2]
    _ = _ := hlim
    _ = _ := by
        refine integral_congr_ae ?_
        filter_upwards [hgood] with ω hω
        have := hp.hM.1 ω
        rw [hω.2, hd.sym_add_mix_eq v hω.1]

end BPZLimitData

end DOZZ.Proofs
