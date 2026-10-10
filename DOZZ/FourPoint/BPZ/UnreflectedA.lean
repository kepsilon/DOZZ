/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.HypergeomNearZero
public import DOZZ.FourPoint.Fusion.KRVRestrictedFusion
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.GaussCutPlane
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC

/-! # The unreflected `γ/2` formula: reduction to the shift relation

With `a, b, c` the Gauss parameters at `χ = γ/2`, `C∓ = C(α₁ ∓ γ/2, α₂, α₃)` and
`ρ = gaussCoefficientRatio a b c`, the diagonal classification at `χ = γ/2` reads
`T = C₋ (|F₋|² + ρ |F₊|²)` on the cut plane. The unreflected formula is then equivalent to the
shift relation `ρ C₋ = -μ Re(planar constant) C₊`.

On the KRV interval `γ/2 + 1/γ < α₁ < 2/γ` (nonempty when `γ² < 2`) the shift relation follows by
comparing the diagonal formula along `t ↓ 0` with the restricted fusion expansion
`T(t) = C₋ + B t^κ + o(t^κ)`, `κ = γ(Q - α₁) < 1`: there `|F₋(t)|² = 1 + O(t)` and
`|F₊(t)|² = t^κ |H'(t)|²` with `H'(0) = 1`. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The parameter `c` at `χ = γ/2` is `1 - κ/2` with `κ = γ(Q - α₁)`. -/
theorem bpz_gaussParameterC_half (γ α₁ : ℝ) :
    2 * (1 - gaussParameterC γ (γ / 2) α₁) = γ * (Q γ - α₁) := by
  unfold gaussParameterC
  ring

/-- `0 < c < 1` at `χ = γ/2` on the unreflected interval. -/
theorem bpz_gaussParameterC_half_mem {γ α₁ : ℝ} (hγ : 0 < γ) (hαlo : γ / 2 < α₁)
    (hαhi : α₁ < 2 / γ) :
    0 < gaussParameterC γ (γ / 2) α₁ ∧ gaussParameterC γ (γ / 2) α₁ < 1 := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  unfold gaussParameterC
  rw [hQ]
  have h1 : γ / 2 * (2 / γ + γ / 2 - α₁) = 1 + γ / 2 * (γ / 2 - α₁) := by
    field_simp
    ring
  have h2 : γ / 2 * (2 / γ + γ / 2 - α₁) = γ / 2 * (2 / γ - α₁) + γ ^ 2 / 4 := by ring
  constructor
  · have : γ / 2 * (γ / 2 - α₁) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) (by linarith)
    linarith
  · have h3 : 0 < γ / 2 * (2 / γ - α₁) := mul_pos (by positivity) (by linarith)
    have h4 : 0 < γ ^ 2 / 4 := by positivity
    linarith

/-- A real number `> 0` is not a nonpositive integer, as a complex number. -/
theorem bpz_ne_neg_nat_of_pos {c : ℝ} (hc : 0 < c) : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
  intro n h
  have h' : c = -(n : ℝ) := by exact_mod_cast h
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- **Reduction.** The diagonal formula at `χ = γ/2` and the shift relation give the unreflected
formula. -/
theorem bpz_unreflected_of_shift {Ω : Type*} [MeasurableSpace Ω] {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hdiag : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
        (‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃) (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
          gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
            ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2))
    (hshift : gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
        (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ =
        -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
          structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃) :
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            ‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
                (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 := by
  intro z hz
  rw [neg_div, hdiag z hz]
  linear_combination
    ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃) (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
      (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 * hshift

/-- `(φ(t) - φ(0))/t^κ → 0` as `t ↓ 0` for `φ` differentiable at `0` and `κ < 1`. -/
theorem bpz_tendsto_sub_div_rpow {φ : ℝ → ℝ} {κ : ℝ} (hκ : κ < 1) (hφ : DifferentiableAt ℝ φ 0) :
    Tendsto (fun t => (φ t - φ 0) / t ^ κ) (𝓝[>] 0) (𝓝 0) := by
  have hslope : Tendsto (fun t => (φ t - φ 0) / t) (𝓝[>] 0) (𝓝 (deriv φ 0)) := by
    have h := hφ.hasDerivAt.tendsto_slope_zero_right
    simpa [zero_add, smul_eq_mul, div_eq_inv_mul] using h
  have hpow : Tendsto (fun t : ℝ => t ^ (1 - κ)) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
    exact h0.rpow_const_nhds_zero (by linarith)
  have hprod := hslope.mul hpow
  rw [mul_zero] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  have hk : t ^ (1 - κ) * t ^ κ = t := by
    rw [← Real.rpow_add ht, sub_add_cancel, Real.rpow_one]
  have htk : 0 < t ^ κ := Real.rpow_pos_of_pos ht κ
  field_simp
  rw [mul_assoc, hk]

/-- **The shift relation on the KRV interval.** -/
theorem bpz_shift_restricted {Ω : Type*} [MeasurableSpace Ω] {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγsq : γ ^ 2 < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 + 1 / γ < α₁) (hαhi : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiag : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
        (‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃) (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
          gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
            ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2)) :
    gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
        (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ =
        -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
          structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ := by
  set a := gaussParameterA γ (γ / 2) α₁ α₂ α₃ with ha
  set b := gaussParameterB γ (γ / 2) α₁ α₂ α₃ with hb
  set c := gaussParameterC γ (γ / 2) α₁ with hc
  set ρ := gaussCoefficientRatio a b c with hρ
  set Cm := structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ with hCm
  set B := -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
    structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ with hB
  set κ := γ * (Q γ - α₁) with hκ
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hκ1 : κ < 1 := by
    have h : γ * α₁ > γ * (γ / 2 + 1 / γ) := mul_lt_mul_of_pos_left hαlo hγ
    have e : γ * (γ / 2 + 1 / γ) = γ ^ 2 / 2 + 1 := by field_simp
    have e2 : κ = 2 + γ ^ 2 / 2 - γ * α₁ := by rw [hκ, hQ]; field_simp
    linarith
  have hlo : γ / 2 < α₁ := by
    have : 0 < 1 / γ := by positivity
    linarith
  obtain ⟨hc0, hc1⟩ := bpz_gaussParameterC_half_mem hγ hlo hαhi
  have h2c : 2 * (1 - c) = κ := bpz_gaussParameterC_half γ α₁
  -- the functions near zero
  set φ : ℝ → ℝ := fun t => Complex.normSq (H (a : ℂ) (b : ℂ) (c : ℂ) (t : ℂ)) with hφ
  set ψ : ℝ → ℝ := fun t => Complex.normSq (H ((a : ℂ) - c + 1) ((b : ℂ) - c + 1)
    (2 - (c : ℂ)) (t : ℂ)) with hψ
  have hcφ : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := bpz_ne_neg_nat_of_pos hc0
  have hcψ : ∀ n : ℕ, (2 - (c : ℂ)) ≠ -(n : ℂ) := by
    have h := bpz_ne_neg_nat_of_pos (c := 2 - c) (by linarith)
    intro n; push_cast at h; exact h n
  have hφd : ContDiffOn ℝ 2 φ (Set.Ioo (-1) 1) := bpzHG_contDiffOn_normSq hH hcφ
  have hψd : ContDiffOn ℝ 2 ψ (Set.Ioo (-1) 1) := bpzHG_contDiffOn_normSq hH hcψ
  have hmem : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hφ0 : φ 0 = 1 := by
    simp only [hφ, Complex.ofReal_zero, bpzHG_eq_one_at_zero hH hcφ, map_one]
  have hψ0 : ψ 0 = 1 := by
    simp only [hψ, Complex.ofReal_zero, bpzHG_eq_one_at_zero hH hcψ, map_one]
  have hφdiff : DifferentiableAt ℝ φ 0 :=
    (hφd.differentiableOn (by norm_num)).differentiableAt hmem
  have hψcont : ContinuousAt ψ 0 := hψd.continuousOn.continuousAt hmem
  -- the restricted fusion expansion
  obtain ⟨r, hr, hrlim⟩ := DOZZ.Proofs.gammaHalf_KRV_restricted_fusion P X M γ μ α₁ α₂ α₃ hγ
    hγsq hμ hαlo hαhi hα₂ hα₃ hs hX hM
  -- the identity along `(0, 1)`
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      ρ * Cm * ψ t = B + r t / t ^ κ - Cm * ((φ t - φ 0) / t ^ κ) := by
    intro t ht0 ht1
    have hz : (t : ℂ) ∈ gaussCutPlane := by
      show (t : ℂ).im ≠ 0 ∨ (0 < (t : ℂ).re ∧ (t : ℂ).re < 1)
      right
      simp only [Complex.ofReal_re]
      exact ⟨ht0, ht1⟩
    have h1 := hdiag (t : ℂ) hz
    have h2 := hr (t : ℂ)
    rw [neg_div] at h2
    rw [h1] at h2
    rw [bpzHG_norm_sq_eq_normSq, bpzHG_norm_sq_eq_normSq, bpzHG_normSq_gaussFMinus,
      bpzHG_normSq_gaussFPlus H a b c ht0, h2c, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      at h2
    have htk : 0 < t ^ κ := Real.rpow_pos_of_pos ht0 κ
    rw [hφ0]
    field_simp
    have e : Cm * (φ t + ρ * (t ^ κ * ψ t)) = Cm + B * t ^ κ + r t := h2
    linear_combination e
  -- limits along `t ↓ 0`
  have hlimL : Tendsto (fun t => ρ * Cm * ψ t) (𝓝[>] 0) (𝓝 (ρ * Cm)) := by
    have : Tendsto ψ (𝓝[>] 0) (𝓝 1) := by
      rw [← hψ0]
      exact hψcont.tendsto.mono_left nhdsWithin_le_nhds
    simpa using this.const_mul (ρ * Cm)
  have hr0 : Tendsto (fun t : ℝ => r t / t ^ κ) (𝓝[>] 0) (𝓝 0) := by
    have hof : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
          Complex.continuous_ofReal.tendsto 0
        rw [Complex.ofReal_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        exact Complex.ofReal_ne_zero.mpr ht.ne'
    refine (hrlim.comp hof).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Function.comp, Complex.norm_real, Real.norm_of_nonneg ht.le, hκ]
  have hlimR : Tendsto (fun t : ℝ => B + r t / t ^ κ - Cm * ((φ t - φ 0) / t ^ κ)) (𝓝[>] 0)
      (𝓝 (B + 0 - Cm * 0)) :=
    (tendsto_const_nhds.add hr0).sub ((bpz_tendsto_sub_div_rpow hκ1 hφdiff).const_mul Cm)
  rw [add_zero, mul_zero, sub_zero] at hlimR
  have hev : (fun t => ρ * Cm * ψ t) =ᶠ[𝓝[>] 0]
      fun t : ℝ => B + r t / t ^ κ - Cm * ((φ t - φ 0) / t ^ κ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact key t ht.1 ht.2
  exact tendsto_nhds_unique (hlimL.congr' hev) hlimR

end DOZZ.Proofs
