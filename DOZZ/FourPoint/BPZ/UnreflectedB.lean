/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.UnreflectedA
public import DOZZ.FourPoint.BPZ.StructureConstantAnalytic

/-! # The shift relation for `γ² < 2` by analytic continuation in `α₁`

For fixed `γ² < 2`, `μ`, `α₂`, `α₃`, both sides of the shift relation
`ρ(α₁) C(α₁ - γ/2) = -μ Re(planar constant)(α₁) C(α₁ + γ/2)` are real-analytic in `α₁` on the
interval `J = {γ/2 < α₁ < 2/γ, 2Q + γ/2 < α₁ + α₂ + α₃}`: the structure constants by
`bpz_analyticAt_structureConstant`, the explicit coefficients because all their Gamma arguments
are positive (respectively non-integer) there. They agree on the KRV subinterval
`α₁ > γ/2 + 1/γ`, which is nonempty, so they agree on `J` by the identity theorem. -/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The Gauss parameters at `χ = γ/2` as affine functions of `α₁`. -/
theorem bpz_gaussParameters_half (γ t α₂ α₃ : ℝ) :
    gaussParameterA γ (γ / 2) t α₂ α₃ = -(γ / 4) * (Q γ + γ - t - α₂ - α₃) - 1 / 2 ∧
    gaussParameterB γ (γ / 2) t α₂ α₃ = -(γ / 4) * (Q γ - t - α₂ + α₃) + 1 / 2 ∧
    gaussParameterC γ (γ / 2) t = 1 - γ / 2 * (Q γ - t) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gaussParameterA; ring
  · unfold gaussParameterB; ring
  · unfold gaussParameterC; ring

/-- On the unreflected domain all ten Gamma arguments of the coefficient ratio are positive. -/
theorem bpz_gauss_args_pos {γ t α₂ α₃ : ℝ} (hγ : 0 < γ) (hlo : γ / 2 < t)
    (hhi : t < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 2 * Q γ + γ / 2 < t + α₂ + α₃) :
    let a := gaussParameterA γ (γ / 2) t α₂ α₃
    let b := gaussParameterB γ (γ / 2) t α₂ α₃
    let c := gaussParameterC γ (γ / 2) t
    0 < c ∧ 0 < 1 - a ∧ 0 < 1 - b ∧ 0 < a - c + 1 ∧ 0 < b - c + 1 ∧ 0 < 2 - c ∧
      0 < c - a ∧ 0 < c - b ∧ 0 < a ∧ 0 < b := by
  intro a b c
  obtain ⟨ha, hb, hc⟩ := bpz_gaussParameters_half γ t α₂ α₃
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγi : γ * (2 / γ) = 2 := by field_simp
  -- auxiliary products
  have hγQ : γ * Q γ = 2 + γ ^ 2 / 2 := by rw [hQ]; field_simp
  have ht2 : γ * t < 2 := by
    have := mul_lt_mul_of_pos_left hhi hγ
    linarith only [this, hγi]
  have ht1 : γ ^ 2 / 2 < γ * t := by
    have := mul_lt_mul_of_pos_left hlo hγ
    linarith only [this]
  have hα₂γ : γ < α₂ := by
    have : t < 2 / γ := hhi
    have h3 : α₃ < 2 / γ + γ / 2 := by rw [← hQ]; exact hα₃
    rw [hQ] at hs
    linarith only [this, h3, hs]
  have hα₃γ : γ < α₃ := by
    have h2 : α₂ < 2 / γ + γ / 2 := by rw [← hQ]; exact hα₂
    rw [hQ] at hs
    linarith only [hhi, h2, hs]
  have hsum : γ * (t + α₂ + α₃) > 2 * (γ * Q γ) + γ ^ 2 / 2 := by
    have := mul_lt_mul_of_pos_left hs hγ
    linarith only [this]
  have hα₂' : γ * α₂ < γ * Q γ := mul_lt_mul_of_pos_left hα₂ hγ
  have hα₃' : γ * α₃ < γ * Q γ := mul_lt_mul_of_pos_left hα₃ hγ
  have hα₂'' : γ * γ < γ * α₂ := mul_lt_mul_of_pos_left hα₂γ hγ
  have hα₃'' : γ * γ < γ * α₃ := mul_lt_mul_of_pos_left hα₃γ hγ
  have hγsq : γ ^ 2 < 4 := by linarith only [hα₂'', hα₂', hγQ]
  simp only [a, b, c, ha, hb, hc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [hγQ, ht2, ht1, hsum, hα₂', hα₃', hα₂'', hα₃'', hγsq, sq_nonneg γ, hγ]

/-- The left side of the shift relation is real-analytic in `α₁` on the unreflected domain. -/
theorem bpz_analyticAt_shift_lhs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (M : Ω → Measure ℂ) (γ μ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hμ : 0 < μ) (hM : IsGMCOf P X γ M) {t : ℝ} (hlo : γ / 2 < t)
    (hhi : t < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 2 * Q γ + γ / 2 < t + α₂ + α₃) :
    AnalyticAt ℝ (fun t => gaussCoefficientRatio (gaussParameterA γ (γ / 2) t α₂ α₃)
      (gaussParameterB γ (γ / 2) t α₂ α₃) (gaussParameterC γ (γ / 2) t) *
        structureConstant P M γ μ (t - γ / 2) α₂ α₃) t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    bpz_gauss_args_pos hγ hlo hhi hα₂ hα₃ hs
  have hA : AnalyticAt ℝ (fun t => gaussParameterA γ (γ / 2) t α₂ α₃) t := by
    unfold gaussParameterA
    fun_prop
  have hB : AnalyticAt ℝ (fun t => gaussParameterB γ (γ / 2) t α₂ α₃) t := by
    unfold gaussParameterB
    fun_prop
  have hC : AnalyticAt ℝ (fun t => gaussParameterC γ (γ / 2) t) t := by
    unfold gaussParameterC
    fun_prop
  have hρ := bpz_analyticAt_gaussCoefficientRatio hA hB hC h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hES : ExtendedSeiberg3 γ (t - γ / 2) α₂ α₃ ∧ 0 < sExp γ (t - γ / 2) α₂ α₃ := by
    have hsE : 0 < sExp γ (t - γ / 2) α₂ α₃ := by
      unfold sExp
      exact div_pos (by linarith only [hs]) hγ
    have hmin : 0 < min (4 / γ ^ 2) (min (2 / γ * (Q γ - (t - γ / 2)))
        (min (2 / γ * (Q γ - α₂)) (2 / γ * (Q γ - α₃)))) := by
      have e1 : 0 < 2 / γ * (Q γ - (t - γ / 2)) := by
        apply mul_pos (by positivity)
        rw [hQ]
        have : t < 2 / γ := hhi
        linarith only [this, hγ]
      have e2 : 0 < 2 / γ * (Q γ - α₂) := mul_pos (by positivity) (by linarith only [hα₂])
      have e3 : 0 < 2 / γ * (Q γ - α₃) := mul_pos (by positivity) (by linarith only [hα₃])
      exact lt_min (by positivity) (lt_min e1 (lt_min e2 e3))
    refine ⟨⟨?_, hα₂, hα₃, by linarith only [hsE, hmin]⟩, hsE⟩
    rw [hQ]
    have : t < 2 / γ := hhi
    linarith only [this, hγ]
  have hCm := bpz_analyticAt_structureConstant P X hX M γ μ hγ hγ2 hμ hM hES.1 hES.2
  have hshift : AnalyticAt ℝ (fun t => t - γ / 2) t := by fun_prop
  exact hρ.mul (AnalyticAt.comp (g := fun s => structureConstant P M γ μ s α₂ α₃)
    (f := fun t => t - γ / 2) hCm hshift)

/-- The right side of the shift relation is real-analytic in `α₁` on the unreflected domain. -/
theorem bpz_analyticAt_shift_rhs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (M : Ω → Measure ℂ) (γ μ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hγ2 : γ < 2) (hμ : 0 < μ) (hM : IsGMCOf P X γ M) {t : ℝ} (hlo : γ / 2 < t)
    (hhi : t < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hs : 2 * Q γ + γ / 2 < t + α₂ + α₃) :
    AnalyticAt ℝ (fun t => -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * t)).re *
        structureConstant P M γ μ (t + γ / 2) α₂ α₃) t := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγt1 : γ * t / 2 < 1 := by
    have := mul_lt_mul_of_pos_left hhi hγ
    have e : γ * (2 / γ) = 2 := by field_simp
    linarith only [this, e]
  have hγt0 : γ ^ 2 / 4 < γ * t / 2 := by
    have := mul_lt_mul_of_pos_left hlo hγ
    linarith only [this]
  have hγsq : γ ^ 2 < 4 := by linarith only [hγt0, hγt1]
  have hpos : 0 < γ ^ 2 / 4 := by positivity
  -- the three arguments of `lFun` are not integers
  have hnot : ∀ {x : ℝ} {n : ℤ}, (n : ℝ) < x → x < n + 1 → x ≠ n := fun h1 _ h => by
    rw [h] at h1; exact lt_irrefl _ h1
  have harg1 : ∀ n : ℤ, γ * t / 2 ≠ n := by
    intro n hn
    have h0 : (0 : ℝ) < n := by rw [← hn]; linarith only [hγt0, hpos]
    have h1 : (n : ℝ) < 1 := by rw [← hn]; exact hγt1
    have : (0 : ℤ) < n := by exact_mod_cast h0
    have : n < (1 : ℤ) := by exact_mod_cast h1
    omega
  have harg2 : ∀ n : ℤ, -(γ ^ 2 / 2) / 2 ≠ n := by
    intro n hn
    have h0 : (-1 : ℝ) < n := by rw [← hn]; linarith only [hγsq]
    have h1 : (n : ℝ) < 0 := by rw [← hn]; linarith only [hpos]
    have : (-1 : ℤ) < n := by exact_mod_cast h0
    have : n < (0 : ℤ) := by exact_mod_cast h1
    omega
  have harg3 : ∀ n : ℤ, 2 - γ * t / 2 + γ ^ 2 / 2 / 2 ≠ n := by
    intro n hn
    have h0 : (1 : ℝ) < n := by rw [← hn]; linarith only [hγt1, hpos]
    have h1 : (n : ℝ) < 2 := by rw [← hn]; linarith only [hγt0]
    have : (1 : ℤ) < n := by exact_mod_cast h0
    have : n < (2 : ℤ) := by exact_mod_cast h1
    omega
  have hPGC := bpz_analyticAt_re_planarGaussConstant (k := fun _ => γ ^ 2 / 2)
    (β := fun t => γ * t) (x₀ := t) analyticAt_const (by fun_prop)
    (by simpa [mul_div_assoc] using harg1) (by simpa using harg2)
    (by simpa [mul_div_assoc] using harg3)
  have hES : ExtendedSeiberg3 γ (t + γ / 2) α₂ α₃ ∧ 0 < sExp γ (t + γ / 2) α₂ α₃ := by
    have hsE : 0 < sExp γ (t + γ / 2) α₂ α₃ := by
      unfold sExp
      exact div_pos (by linarith only [hs, hγ]) hγ
    have hmin : 0 < min (4 / γ ^ 2) (min (2 / γ * (Q γ - (t + γ / 2)))
        (min (2 / γ * (Q γ - α₂)) (2 / γ * (Q γ - α₃)))) := by
      have e1 : 0 < 2 / γ * (Q γ - (t + γ / 2)) := by
        apply mul_pos (by positivity)
        rw [hQ]
        have : t < 2 / γ := hhi
        linarith only [this]
      have e2 : 0 < 2 / γ * (Q γ - α₂) := mul_pos (by positivity) (by linarith only [hα₂])
      have e3 : 0 < 2 / γ * (Q γ - α₃) := mul_pos (by positivity) (by linarith only [hα₃])
      exact lt_min (by positivity) (lt_min e1 (lt_min e2 e3))
    refine ⟨⟨?_, hα₂, hα₃, by linarith only [hsE, hmin]⟩, hsE⟩
    rw [hQ]
    have : t < 2 / γ := hhi
    linarith only [this]
  have hCp := bpz_analyticAt_structureConstant P X hX M γ μ hγ hγ2 hμ hM hES.1 hES.2
  have hshift : AnalyticAt ℝ (fun t => t + γ / 2) t := by fun_prop
  exact (analyticAt_const.mul hPGC).mul (AnalyticAt.comp
    (g := fun s => structureConstant P M γ μ s α₂ α₃) (f := fun t => t + γ / 2) hCp hshift)

/-- **The shift relation for `γ² < 2`.** -/
theorem bpz_shift_small_gamma {Ω : Type*} [MeasurableSpace Ω] {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγsq : γ ^ 2 < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiag : ∀ t : ℝ, γ / 2 < t → t < 2 / γ → 2 * Q γ + γ / 2 < t + α₂ + α₃ →
      ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) t α₂ α₃ z =
        structureConstant P M γ μ (t - γ / 2) α₂ α₃ *
          (‖gaussFMinus H (gaussParameterA γ (γ / 2) t α₂ α₃)
              (gaussParameterB γ (γ / 2) t α₂ α₃) (gaussParameterC γ (γ / 2) t) z‖ ^ 2 +
            gaussCoefficientRatio (gaussParameterA γ (γ / 2) t α₂ α₃)
                (gaussParameterB γ (γ / 2) t α₂ α₃) (gaussParameterC γ (γ / 2) t) *
              ‖gaussFPlus H (gaussParameterA γ (γ / 2) t α₂ α₃)
                (gaussParameterB γ (γ / 2) t α₂ α₃) (gaussParameterC γ (γ / 2) t) z‖ ^ 2)) :
    gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
        (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ =
        -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
          structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ := by
  have hγ2 : γ < 2 := lt_of_pow_lt_pow_left₀ 2 zero_le_two (by linarith only [hγsq])
  set J : Set ℝ := {t | γ / 2 < t ∧ t < 2 / γ ∧ 2 * Q γ + γ / 2 < t + α₂ + α₃} with hJ
  have hJo : IsOpen J :=
    (isOpen_lt (f := fun _ : ℝ => γ / 2) (g := fun t : ℝ => t) continuous_const
      continuous_id).inter ((isOpen_lt (f := fun t : ℝ => t) (g := fun _ : ℝ => 2 / γ)
        continuous_id continuous_const).inter (isOpen_lt (f := fun _ : ℝ => 2 * Q γ + γ / 2)
          (g := fun t : ℝ => t + α₂ + α₃) continuous_const (by fun_prop)))
  have hJc : IsPreconnected J := by
    have hord : J.OrdConnected := ⟨fun x hx y hy z hz =>
      ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2.1, by linarith only [hx.2.2, hz.1]⟩⟩
    exact hord.isPreconnected
  have hL : AnalyticOnNhd ℝ (fun t => gaussCoefficientRatio (gaussParameterA γ (γ / 2) t α₂ α₃)
      (gaussParameterB γ (γ / 2) t α₂ α₃) (gaussParameterC γ (γ / 2) t) *
        structureConstant P M γ μ (t - γ / 2) α₂ α₃) J := fun t ht =>
    bpz_analyticAt_shift_lhs P X hX M γ μ α₂ α₃ hγ hγ2 hμ hM ht.1 ht.2.1 hα₂ hα₃ ht.2.2
  have hR : AnalyticOnNhd ℝ (fun t => -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * t)).re *
      structureConstant P M γ μ (t + γ / 2) α₂ α₃) J := fun t ht =>
    bpz_analyticAt_shift_rhs P X hX M γ μ α₂ α₃ hγ hγ2 hμ hM ht.1 ht.2.1 hα₂ hα₃ ht.2.2
  -- a point of the KRV subinterval inside `J`
  set lo : ℝ := max (γ / 2 + 1 / γ) (2 * Q γ + γ / 2 - α₂ - α₃) with hlo
  have hlo2 : lo < 2 / γ := by
    refine max_lt ?_ (by linarith only [hs, hαhi])
    have : γ * γ < 2 := by linarith only [hγsq]
    have e : γ / 2 + 1 / γ = (γ * γ + 2) / (2 * γ) := by field_simp
    have e2 : 2 / γ = 4 / (2 * γ) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [e, e2]
    exact div_lt_div_of_pos_right (by linarith only [this]) (by positivity)
  set t₀ : ℝ := (lo + 2 / γ) / 2 with ht₀
  have hKRV : ∀ t, lo < t → t < 2 / γ → t ∈ J ∧ γ / 2 + 1 / γ < t := by
    intro t h1 h2
    have hA : γ / 2 + 1 / γ ≤ lo := le_max_left _ _
    have hB : 2 * Q γ + γ / 2 - α₂ - α₃ ≤ lo := le_max_right _ _
    have h1γ : 0 < 1 / γ := by positivity
    exact ⟨⟨by linarith only [hA, h1, h1γ], h2, by linarith only [hB, h1]⟩,
      by linarith only [hA, h1]⟩
  have ht₀mem : lo < t₀ ∧ t₀ < 2 / γ := ⟨by linarith only [hlo2, ht₀], by linarith only [hlo2, ht₀]⟩
  have hev : (fun t => gaussCoefficientRatio (gaussParameterA γ (γ / 2) t α₂ α₃)
      (gaussParameterB γ (γ / 2) t α₂ α₃) (gaussParameterC γ (γ / 2) t) *
        structureConstant P M γ μ (t - γ / 2) α₂ α₃) =ᶠ[𝓝 t₀]
      fun t => -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * t)).re *
        structureConstant P M γ μ (t + γ / 2) α₂ α₃ := by
    filter_upwards [Ioo_mem_nhds ht₀mem.1 ht₀mem.2] with t ht
    obtain ⟨htJ, htK⟩ := hKRV t ht.1 ht.2
    exact bpz_shift_restricted hH P X M γ μ t α₂ α₃ hγ hγsq hμ htK htJ.2.1 hα₂ hα₃ htJ.2.2 hX hM
      (hdiag t htJ.1 htJ.2.1 htJ.2.2)
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hR hJc (hKRV t₀ ht₀mem.1 ht₀mem.2).1 hev
  exact heq ⟨hαlo, hαhi, hs⟩

end DOZZ.Proofs
