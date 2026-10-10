/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Rbar.Multiplier
public import DOZZ.Statements.ShiftEquations.RbarCoefficient
public import DOZZ.Statements.Brownian.ReflectionExponent

/-!
# The residue of the γ/2-crossing multiplier at `ε = γ/2`

With `B = (γ/4)(ε - γ/2)`, `(ε - γ/2) l(B) = (4/γ) Γ(B+1)/Γ(1-B) → 4/γ`, while the other factors are
continuous at `ε = γ/2`. At `A₀ = γα/2 - γ²/4 - 1 = -(γ²/4) p`, `Γ(A₀+1)/Γ(1-A₀) = A₀ l(A₀)`, so the
limit of `(ε - γ/2) T(α, ε, α)` is `2p · (2π/γ) l(A₀) / (l(C) l(-γ²/4) l(γ²/4))`, `p = 2(Q - α)/γ`:
twice the reflection exponent times the coefficient of [KRV, (formulaforbarR)] (erratum K29,
see docs/ERRATA-AND-DEVIATIONS.md).
-/

@[expose] public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- The real form of the `formulaforbarR` coefficient. -/
noncomputable def rbarCoefficientReal (γ α : ℝ) : ℝ :=
  2 * Real.pi / γ * lR (γ / 2 * α - γ ^ 2 / 4 - 1) /
    (lR (1 + γ / 2 * (α - Q γ)) * lR (-(γ ^ 2) / 4) * lR (γ ^ 2 / 4))

/-- **The coefficient is real at real charges.** -/
theorem rbarCoefficient_ofReal (γ α : ℝ) :
    rbarCoefficient γ (α : ℂ) = (rbarCoefficientReal γ α : ℂ) := by
  unfold rbarCoefficient rbarCoefficientReal
  rw [show (γ : ℂ) / 2 * α - (γ : ℂ) ^ 2 / 4 - 1 = ((γ / 2 * α - γ ^ 2 / 4 - 1 : ℝ) : ℂ) by
      push_cast; ring,
    show 1 + (γ : ℂ) / 2 * ((α : ℂ) - (Q γ : ℂ)) = ((1 + γ / 2 * (α - Q γ) : ℝ) : ℂ) by
      push_cast; ring,
    show -((γ : ℂ) ^ 2) / 4 = ((-(γ ^ 2) / 4 : ℝ) : ℂ) by push_cast; ring,
    show (γ : ℂ) ^ 2 / 4 = ((γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring,
    lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR]
  push_cast
  ring

/-- `Real.Gamma` is continuous at points off its poles. -/
theorem continuousAt_realGamma {r : ℝ} (h : ∀ m : ℕ, r ≠ -m) : ContinuousAt Real.Gamma r :=
  (Real.differentiableAt_Gamma h).continuousAt

/-- `l` is continuous on `(0, 1)`. -/
theorem continuousAt_lR {r : ℝ} (h0 : 0 < r) (h1 : r < 1) : ContinuousAt lR r := by
  unfold lR
  have hr : ∀ m : ℕ, r ≠ -m := real_ne_neg_nat_of_frac (k := 0) (by simpa using h0)
    (by simpa using h1)
  have h1r : ∀ m : ℕ, 1 - r ≠ -m := real_ne_neg_nat_of_frac (k := 0) (by push_cast; linarith)
    (by push_cast; linarith)
  exact (continuousAt_realGamma hr).div ((continuousAt_realGamma h1r).comp
    (continuous_const.sub continuous_id).continuousAt) (Real.Gamma_ne_zero h1r)

/-- A complex number with real part in `(-1, 0)` is not a non-positive integer. -/
theorem ne_neg_nat_of_re_mem_neg {w : ℂ} (h1 : -1 < w.re) (h2 : w.re < 0) :
    ∀ m : ℕ, w ≠ -m := by
  intro m hm
  rw [hm] at h1 h2
  simp only [Complex.neg_re, Complex.natCast_re] at h1 h2
  have h3 : m < 1 := by exact_mod_cast (show (m : ℝ) < 1 by linarith)
  have h4 : 0 < m := by exact_mod_cast (show (0 : ℝ) < m by linarith)
  omega

/-- `Γ ∘ φ` converges where `φ` does, off the poles. -/
theorem tendsto_realGamma_comp {l : Filter ℝ} {φ : ℝ → ℝ} {s : ℝ} (hφ : Tendsto φ l (𝓝 s))
    (h : ∀ m : ℕ, s ≠ -m) : Tendsto (fun ε => Real.Gamma (φ ε)) l (𝓝 (Real.Gamma s)) :=
  (continuousAt_realGamma h).tendsto.comp hφ

/-- `(ε - γ/2) l((γ/4)(ε - γ/2)) = (4/γ) Γ(B+1)/Γ(1-B)`. -/
theorem sub_mul_lR_eq {γ ε : ℝ} (hγ : 0 < γ) (hε : γ / 2 < ε) :
    (ε - γ / 2) * lR (γ / 4 * (ε - γ / 2)) =
      4 / γ * (Real.Gamma (γ / 4 * (ε - γ / 2) + 1) / Real.Gamma (1 - γ / 4 * (ε - γ / 2))) := by
  have hB : γ / 4 * (ε - γ / 2) ≠ 0 := (mul_pos (by positivity) (by linarith)).ne'
  rw [Real.Gamma_add_one hB]
  unfold lR
  field_simp

/-- **`(ε - γ/2) l(B) → 4/γ`** as `ε ↓ γ/2`. -/
theorem tendsto_sub_mul_lR {γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun ε => (ε - γ / 2) * lR (γ / 4 * (ε - γ / 2))) (𝓝[>] (γ / 2)) (𝓝 (4 / γ)) := by
  have h1 : ∀ m : ℕ, (1 : ℝ) ≠ -m := fun m h => by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hB : Tendsto (fun ε : ℝ => γ / 4 * (ε - γ / 2)) (𝓝 (γ / 2)) (𝓝 0) := by
    have h := (by fun_prop : Continuous fun ε : ℝ => γ / 4 * (ε - γ / 2)).tendsto (γ / 2)
    rwa [sub_self, mul_zero] at h
  have hG1 := tendsto_realGamma_comp (by simpa using hB.add_const 1) h1
  have hG2 := tendsto_realGamma_comp (by simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hB) h1
  have h := (hG1.div hG2 (by rw [Real.Gamma_one]; exact one_ne_zero)).const_mul (4 / γ)
  rw [Real.Gamma_one, div_one, mul_one] at h
  refine (h.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (sub_mul_lR_eq hγ hε).symm

/-- The Gauss parameter `A` at `ε = γ/2`. -/
theorem crossA_real_at_half {γ : ℝ} (hγ : 0 < γ) (a : ℝ) :
    γ ^ 2 / 4 * ((2 * a + γ / 2 - γ / 2 - 2 * Q γ) / γ) = γ / 2 * a - γ ^ 2 / 4 - 1 := by
  rw [Q]
  field_simp
  ring

/-- **The residue of the diagonal crossing multiplier at `ε = γ/2`**: twice the reflection exponent
times the `formulaforbarR` coefficient. -/
theorem tendsto_sub_mul_crossingMultiplierReal {γ a : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (ha1 : γ / 2 < a) (ha2 : a < Q γ) :
    Tendsto (fun ε => (ε - γ / 2) * crossingMultiplierReal γ ε a) (𝓝[>] (γ / 2))
      (𝓝 (2 * reflectionExponent γ a * rbarCoefficientReal γ a)) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hA₀q : γ / 2 * a - γ ^ 2 / 4 - 1 = -(γ / 2) * (Q γ - a) := by
    rw [hQ]
    field_simp
    ring
  have hqpos : 0 < γ / 2 * (Q γ - a) := mul_pos (by positivity) (by linarith)
  have hqlt : γ / 2 * (Q γ - a) < 1 := by
    calc γ / 2 * (Q γ - a) < γ / 2 * (2 / γ) :=
          mul_lt_mul_of_pos_left (by rw [hQ] at ha2 ⊢; linarith) (by positivity)
      _ = 1 := by field_simp
  have hA₀lo : -1 < γ / 2 * a - γ ^ 2 / 4 - 1 := by rw [hA₀q]; linarith
  have hA₀hi : γ / 2 * a - γ ^ 2 / 4 - 1 < 0 := by rw [hA₀q]; linarith
  -- the Gauss parameter `A` and the factor `Γ(A+1)/Γ(1-A)`
  have hA : Tendsto (fun ε : ℝ => γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ)) (𝓝 (γ / 2))
      (𝓝 (γ / 2 * a - γ ^ 2 / 4 - 1)) := by
    rw [← crossA_real_at_half hγ a]
    exact (by fun_prop : Continuous fun ε : ℝ =>
      γ ^ 2 / 4 * ((2 * a + ε - γ / 2 - 2 * Q γ) / γ)).tendsto (γ / 2)
  have hpA1 : ∀ m : ℕ, γ / 2 * a - γ ^ 2 / 4 - 1 + 1 ≠ -m :=
    real_ne_neg_nat_of_frac (k := 0) (by push_cast; linarith) (by push_cast; linarith)
  have hp1A : ∀ m : ℕ, 1 - (γ / 2 * a - γ ^ 2 / 4 - 1) ≠ -m :=
    real_ne_neg_nat_of_frac (k := 1) (by push_cast; linarith) (by push_cast; linarith)
  have hF1 := ((tendsto_realGamma_comp (hA.add_const 1) hpA1).const_mul
    (-(4 * Real.pi / γ ^ 2))).mul
      ((tendsto_realGamma_comp ((tendsto_const_nhds (x := (1 : ℝ))).sub hA) hp1A).inv₀
        (Real.Gamma_ne_zero hp1A))
  -- the constant factors
  have hlin : Tendsto (fun ε : ℝ => γ * ε / 2) (𝓝 (γ / 2)) (𝓝 (γ ^ 2 / 4)) := by
    rw [show γ ^ 2 / 4 = γ * (γ / 2) / 2 by ring]
    exact (by fun_prop : Continuous fun ε : ℝ => γ * ε / 2).tendsto (γ / 2)
  have hp0 : 0 < γ ^ 2 / 4 := by positivity
  have hp1 : γ ^ 2 / 4 < 1 := by nlinarith
  have hne : lR (-(γ ^ 2) / 4) * lR (γ ^ 2 / 4) ≠ 0 :=
    mul_ne_zero (lR_ne_zero_of_mem_neg (by linarith) (by linarith))
      (lR_ne_zero_of_mem_unit hp0 hp1)
  have hF3 := (tendsto_const_nhds (x := (lR (1 - γ / 2 * (Q γ - a)))⁻¹)).mul
    (((tendsto_const_nhds (x := lR (-(γ ^ 2) / 4))).mul
      ((continuousAt_lR hp0 hp1).tendsto.comp hlin)).inv₀ hne)
  have hprod := ((hF1.mono_left nhdsWithin_le_nhds).mul (tendsto_sub_mul_lR hγ)).mul
    (hF3.mono_left nhdsWithin_le_nhds)
  -- the limit value
  have hL : -(4 * Real.pi / γ ^ 2) * Real.Gamma (γ / 2 * a - γ ^ 2 / 4 - 1 + 1) *
      (Real.Gamma (1 - (γ / 2 * a - γ ^ 2 / 4 - 1)))⁻¹ * (4 / γ) *
      ((lR (1 - γ / 2 * (Q γ - a)))⁻¹ * (lR (-(γ ^ 2) / 4) * lR (γ ^ 2 / 4))⁻¹) =
      2 * reflectionExponent γ a * rbarCoefficientReal γ a := by
    rw [Real.Gamma_add_one hA₀hi.ne]
    unfold reflectionExponent rbarCoefficientReal
    rw [show lR (γ / 2 * a - γ ^ 2 / 4 - 1) = Real.Gamma (γ / 2 * a - γ ^ 2 / 4 - 1) /
        Real.Gamma (1 - (γ / 2 * a - γ ^ 2 / 4 - 1)) from rfl,
      show 1 - γ / 2 * (Q γ - a) = 1 + γ / 2 * (a - Q γ) by ring]
    generalize Real.Gamma (γ / 2 * a - γ ^ 2 / 4 - 1) = G0
    generalize Real.Gamma (1 - (γ / 2 * a - γ ^ 2 / 4 - 1)) = G1
    generalize lR (1 + γ / 2 * (a - Q γ)) = LC
    generalize lR (-(γ ^ 2) / 4) = Lm
    generalize lR (γ ^ 2 / 4) = Lp
    rw [hA₀q]
    field_simp
    ring
  rw [← hL]
  refine Tendsto.congr (fun ε => ?_) hprod
  simp only [Function.comp_apply]
  unfold crossingMultiplierReal
  ring

/-- **The `formulaforbarR` coefficient is holomorphic on the reflection strip.** -/
theorem differentiableOn_rbarCoefficient {γ : ℝ} (hγ : 0 < γ) :
    DifferentiableOn ℂ (rbarCoefficient γ) (reflectionStrip γ) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hw : DifferentiableAt ℂ (fun u : ℂ => (γ : ℂ) / 2 * u - (γ : ℂ) ^ 2 / 4 - 1) z := by
    fun_prop
  have hwre : ((γ : ℂ) / 2 * z - (γ : ℂ) ^ 2 / 4 - 1).re = γ / 2 * z.re - γ ^ 2 / 4 - 1 := by
    simp [Complex.mul_re, pow_two]
  have hw1 : -1 < γ / 2 * z.re - γ ^ 2 / 4 - 1 := by
    have : γ / 2 * (γ / 2) < γ / 2 * z.re := mul_lt_mul_of_pos_left hz.1 (by positivity)
    nlinarith
  have hw2 : γ / 2 * z.re - γ ^ 2 / 4 - 1 < 0 := by
    have : γ / 2 * z.re < γ / 2 * Q γ := mul_lt_mul_of_pos_left hz.2 (by positivity)
    have hγQ : γ / 2 * Q γ = 1 + γ ^ 2 / 4 := by
      rw [hQ]
      field_simp
      ring
    linarith
  have hnum : DifferentiableAt ℂ
      (fun u : ℂ => lFun ((γ : ℂ) / 2 * u - (γ : ℂ) ^ 2 / 4 - 1)) z := by
    unfold lFun
    simp_rw [div_eq_mul_inv]
    exact ((Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_mem_neg (by rw [hwre]; exact hw1)
      (by rw [hwre]; exact hw2))).comp z hw).mul
      ((Complex.differentiable_one_div_Gamma _).comp z ((differentiableAt_const _).sub hw))
  have hden : DifferentiableAt ℂ (fun u : ℂ => (lFun (crossC γ u))⁻¹) z := by
    simp_rw [lFun_inv]
    have h1 : DifferentiableAt ℂ (fun w : ℂ => 1 - crossC γ w) z := by
      unfold crossC
      fun_prop
    have h2 : DifferentiableAt ℂ (fun w : ℂ => crossC γ w) z := by
      unfold crossC
      fun_prop
    have hCpos : 0 < (1 - crossC γ z).re := by
      rw [one_sub_crossC_re]
      exact mul_pos (by positivity) (by linarith [hz.2])
    exact ((Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos hCpos)).comp z h1).mul
      ((Complex.differentiable_one_div_Gamma _).comp z h2)
  have hfun : rbarCoefficient γ = fun u : ℂ => 2 * (Real.pi : ℂ) / γ *
      lFun ((γ : ℂ) / 2 * u - (γ : ℂ) ^ 2 / 4 - 1) * (lFun (crossC γ u))⁻¹ *
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4))⁻¹ := by
    funext u
    unfold rbarCoefficient crossC
    rw [show (1 : ℂ) + (γ : ℂ) / 2 * (u - (Q γ : ℂ)) = 1 - (γ / 2 : ℂ) * (Q γ - u) by ring]
    ring
  rw [hfun]
  exact (((differentiableAt_const _).mul hnum).mul hden).mul (differentiableAt_const _)

end DOZZ.Proofs

end
