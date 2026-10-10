/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DozzFormula
public import DOZZ.Statements.Defs.IsUpsilon
public import DOZZ.Statements.Defs.SExp
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Upsilon.Uniqueness
import DOZZ.Upsilon.ZeroStructure
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The zero-mode limit of the DOZZ formula

As `α₁ → 2Q - α₂ - α₃` (so `s = (Σαᵢ - 2Q)/γ → 0`), the product `μ^s Γ(s)⁻¹ D(α₁, α₂, α₃)`
converges to `2/γ`: the simple zero of `Υ` at `0` in the denominator cancels the simple pole of
`Γ(s)`, the reflection `Υ(Q - x) = Υ(x)` cancels the remaining charge factors, and the
exponentials `μ^s B^(-s)` and `Γ(s + 1)⁻¹` tend to `1`.

The proof splits into four elementary limits (`cpow` at exponent `0`, `Γ` at `1`, the slope of
the entire function `Υ` at its zero `0`, and the ratio of the six non-singular `Υ`-values), a
pure-algebra rewrite of the product on the punctured neighbourhood, and the assembly.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- **The rewrite as pure algebra.** With `Γ(s + 1) = s Γ(s)`, `Υ(w) = w q` and `w = g s / 2`,
the product `m Γ(s)⁻¹ · (b D₀ u₁ u₂ u₃ / (v₀ v₁ v₂ v₃))` equals
`(m b) Γ(s + 1)⁻¹ (2 / g) (D₀ / q) (u₁ u₂ u₃ / (v₁ v₂ v₃))`. No nonvanishing hypotheses are
needed: only the distributivity of `⁻¹` over products. -/
theorem zeroMode_algebra {m b G G₁ s g D₀ u₁ u₂ u₃ v₀ v₁ v₂ v₃ w q : ℂ}
    (hG : G₁ = s * G) (hv : v₀ = w * q) (hw : w = g * s / 2) :
    m / G * (b * (D₀ * u₁ * u₂ * u₃) / (v₀ * v₁ * v₂ * v₃)) =
      m * b * G₁⁻¹ * (2 / g) * (D₀ / q) * (u₁ * u₂ * u₃ / (v₁ * v₂ * v₃)) := by
  subst hG hv hw
  ring

/-- A complex power with fixed nonzero base tends to `1` as the exponent tends to `0`. -/
theorem zeroMode_tendsto_cpow {ι : Type*} {l : Filter ι} {a : ℂ} (ha : a ≠ 0) {s : ι → ℂ}
    (hs : Tendsto s l (𝓝 0)) : Tendsto (fun i => a ^ s i) l (𝓝 1) := by
  have h := (continuousAt_const_cpow (a := a) (b := 0) ha).tendsto.comp hs
  simpa [Function.comp_def] using h

/-- `Γ(s + 1)⁻¹ → 1` as `s → 0`, since `Γ` is continuous at `1` with `Γ(1) = 1`. -/
theorem zeroMode_tendsto_inv_gamma {ι : Type*} {l : Filter ι} {s : ι → ℂ}
    (hs : Tendsto s l (𝓝 0)) : Tendsto (fun i => (Complex.Gamma (s i + 1))⁻¹) l (𝓝 1) := by
  have h1 : Tendsto (fun i => s i + 1) l (𝓝 1) := by simpa using hs.add_const 1
  have h2 := Complex.continuousAt_Gamma_one.tendsto.comp h1
  rw [Complex.Gamma_one] at h2
  simpa [Function.comp_def] using h2.inv₀ one_ne_zero

/-- The slope of an entire function vanishing at `0`: `U(x) / x → U'(0)` along real `x → 0`. -/
theorem zeroMode_tendsto_slope {U : ℂ → ℂ} (hU : Differentiable ℂ U) (h0 : U 0 = 0) :
    Tendsto (fun x : ℝ => U (x : ℂ) / (x : ℂ)) (𝓝[≠] 0) (𝓝 (deriv U 0)) := by
  have hd : HasDerivAt (fun x : ℝ => U (x : ℂ)) (deriv U 0) 0 := by
    have h := (hU 0).hasDerivAt
    exact HasDerivAt.comp_ofReal (z := 0) (by simpa using h)
  refine hd.tendsto_slope_zero.congr (fun x => ?_)
  simp [h0, Complex.real_smul, div_eq_inv_mul]

/-- The slope limit along the shifted variable `w = (t - t₀) / 2`, as `t → t₀` with `t ≠ t₀`. -/
theorem zeroMode_tendsto_slope_comp {U : ℂ → ℂ} (hU : Differentiable ℂ U) (h0 : U 0 = 0)
    (t₀ : ℝ) :
    Tendsto (fun t : ℝ => U (((t - t₀) / 2 : ℝ) : ℂ) / (((t - t₀) / 2 : ℝ) : ℂ))
      (𝓝[≠] t₀) (𝓝 (deriv U 0)) := by
  refine (zeroMode_tendsto_slope hU h0).comp ?_
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have hc : Continuous (fun t : ℝ => (t - t₀) / 2) := by fun_prop
    have h := hc.tendsto t₀
    rw [sub_self, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : t - t₀ ≠ 0 := sub_ne_zero.mpr ht
    simpa using ht'

/-- `Υ` does not vanish at a real point of the open strip `0 < x < Q`. -/
theorem zeroMode_ne_zero {γ : ℝ} {U : ℂ → ℂ} (hU : IsUpsilon γ U) {x : ℝ} (hx : 0 < x)
    (hx' : x < Q γ) : U (x : ℂ) ≠ 0 := by
  rw [hU.2 (x : ℂ) (by simpa using hx) (by simpa using hx')]
  exact Complex.exp_ne_zero _

/-- `Υ` vanishes at `0`: the lattice point `m = n = 0`. -/
theorem zeroMode_zero {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) :
    U 0 = 0 := by
  rw [IsUpsilon.eq_zero_iff hγ hγ2 hU]
  exact ⟨0, 0, Or.inl (by simp)⟩

/-- `Υ'(0) = Υ(γ / 2) ≠ 0`, since `γ / 2` lies in the open strip. -/
theorem zeroMode_deriv_ne_zero {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) : deriv U 0 ≠ 0 := by
  rw [IsUpsilon.deriv_zero hγ hγ2 hU]
  have h2 : 0 < 2 / γ := by positivity
  have h := zeroMode_ne_zero hU (x := γ / 2) (by positivity) (by unfold Q; linarith)
  simpa using h

/-- **The bracket of non-singular `Υ`-values tends to `1`.** At `t = t₀` (where
`t₀ + α₂ + α₃ = 2Q`) the half-sum is `Q`, so the denominator is `Υ(Q - t₀) Υ(Q - α₂) Υ(Q - α₃)
= Υ(t₀) Υ(α₂) Υ(α₃)` by reflection, which equals the (nonzero) numerator. -/
theorem zeroMode_bracket_limit {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) {α₂ α₃ t₀ : ℝ} (ht₀ : t₀ + α₂ + α₃ = 2 * Q γ) (h₁ : 0 < t₀)
    (h₁' : t₀ < Q γ) (h₂ : 0 < α₂) (h₂' : α₂ < Q γ) (h₃ : 0 < α₃) (h₃' : α₃ < Q γ) :
    Tendsto (fun t : ℝ => U t * U α₂ * U α₃ /
        (U (((t : ℂ) + α₂ + α₃) / 2 - t) * U (((t : ℂ) + α₂ + α₃) / 2 - α₂) *
          U (((t : ℂ) + α₂ + α₃) / 2 - α₃))) (𝓝[≠] t₀) (𝓝 1) := by
  have hUc : Continuous U := hU.1.continuous
  have hhalf : ((t₀ : ℂ) + α₂ + α₃) / 2 = (Q γ : ℂ) := by
    have h : ((t₀ : ℂ) + α₂ + α₃) = ((t₀ + α₂ + α₃ : ℝ) : ℂ) := by push_cast; ring
    rw [h, ht₀]
    push_cast
    ring
  have hN : Continuous (fun t : ℝ => U t * U α₂ * U α₃) := by fun_prop
  have hD : Continuous (fun t : ℝ => U (((t : ℂ) + α₂ + α₃) / 2 - t) *
      U (((t : ℂ) + α₂ + α₃) / 2 - α₂) * U (((t : ℂ) + α₂ + α₃) / 2 - α₃)) := by fun_prop
  have hDt₀ : U (((t₀ : ℂ) + α₂ + α₃) / 2 - t₀) * U (((t₀ : ℂ) + α₂ + α₃) / 2 - α₂) *
      U (((t₀ : ℂ) + α₂ + α₃) / 2 - α₃) = U t₀ * U α₂ * U α₃ := by
    rw [hhalf, IsUpsilon.reflect hγ hγ2 hU, IsUpsilon.reflect hγ hγ2 hU,
      IsUpsilon.reflect hγ hγ2 hU]
  have hne : U t₀ * U α₂ * U α₃ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (zeroMode_ne_zero hU h₁ h₁') (zeroMode_ne_zero hU h₂ h₂'))
      (zeroMode_ne_zero hU h₃ h₃')
  have hlim := (hN.tendsto t₀).div (hD.tendsto t₀) (by rw [hDt₀]; exact hne)
  rw [hDt₀, div_self hne] at hlim
  exact hlim.mono_left nhdsWithin_le_nhds

/-- **The product on the punctured neighbourhood.** For `t ≠ t₀` (so `s = sExp ≠ 0`),
`μ^s Γ(s)⁻¹ D(t, α₂, α₃)` factors as `(μ^s B^(-s)) Γ(s + 1)⁻¹ (2/γ) (Υ'(0) / q) · bracket`,
where `q = Υ(w) / w` with `w = (t - t₀) / 2`. -/
theorem zeroMode_formula_eq {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) {α₂ α₃ t t₀ : ℝ}
    (ht₀ : t₀ + α₂ + α₃ = 2 * Q γ) (ht : t ≠ t₀) :
    ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) / Complex.Gamma (sExp γ t α₂ α₃)) *
        dozzFormula γ μ U t α₂ α₃ =
      ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) *
          ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ (-(sExp γ t α₂ α₃ : ℂ))) *
        (Complex.Gamma ((sExp γ t α₂ α₃ : ℂ) + 1))⁻¹ * (2 / (γ : ℂ)) *
        (deriv U 0 / (U (((t - t₀) / 2 : ℝ) : ℂ) / (((t - t₀) / 2 : ℝ) : ℂ))) *
        (U t * U α₂ * U α₃ / (U (((t : ℂ) + α₂ + α₃) / 2 - t) *
          U (((t : ℂ) + α₂ + α₃) / 2 - α₂) * U (((t : ℂ) + α₂ + α₃) / 2 - α₃))) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hQ : (2 * (Q γ : ℂ)) = (t₀ : ℂ) + α₂ + α₃ := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) ht₀
    push_cast at h
    exact h.symm
  have hs : sExp γ t α₂ α₃ = (t - t₀) / γ := by
    unfold sExp
    congr 1
    linarith
  have hsne : (sExp γ t α₂ α₃ : ℂ) ≠ 0 := by
    rw [hs]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr ht) hγ.ne')
  have hwne : (((t - t₀) / 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (div_ne_zero (sub_ne_zero.mpr ht) two_ne_zero)
  have hexp : (2 * (Q γ : ℂ) - ((t : ℂ) + α₂ + α₃)) / (γ : ℂ) = -(sExp γ t α₂ α₃ : ℂ) := by
    rw [hs]
    push_cast
    rw [hQ]
    ring
  have hv : U (((t : ℂ) + α₂ + α₃ - 2 * (Q γ : ℂ)) / 2) =
      (((t - t₀) / 2 : ℝ) : ℂ) *
        (U (((t - t₀) / 2 : ℝ) : ℂ) / (((t - t₀) / 2 : ℝ) : ℂ)) := by
    rw [mul_div_cancel₀ _ hwne]
    congr 1
    push_cast
    rw [hQ]
    ring
  have hw : (((t - t₀) / 2 : ℝ) : ℂ) = (γ : ℂ) * (sExp γ t α₂ α₃ : ℂ) / 2 := by
    rw [hs]
    push_cast
    field_simp
  have hG : Complex.Gamma ((sExp γ t α₂ α₃ : ℂ) + 1) =
      (sExp γ t α₂ α₃ : ℂ) * Complex.Gamma (sExp γ t α₂ α₃) := Complex.Gamma_add_one _ hsne
  unfold dozzFormula
  rw [hexp]
  exact zeroMode_algebra hG hv hw

/-- The zero-mode limit with the critical value presented as a free `t₀` satisfying
`t₀ + α₂ + α₃ = 2Q`. -/
theorem zeroMode_limit_aux {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hU : IsUpsilon γ U) {α₂ α₃ t₀ : ℝ} (ht₀ : t₀ + α₂ + α₃ = 2 * Q γ) (h₁ : 0 < t₀)
    (h₁' : t₀ < Q γ) (h₂ : 0 < α₂) (h₂' : α₂ < Q γ) (h₃ : 0 < α₃) (h₃' : α₃ < Q γ) :
    Tendsto (fun t : ℝ => ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) / Complex.Gamma (sExp γ t α₂ α₃)) *
        dozzFormula γ μ U t α₂ α₃) (𝓝[≠] t₀) (𝓝 (2 / γ)) := by
  have hμc : (μ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hμ.ne'
  have hBc : ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (mul_pos (dozzBase_pos hγ hγ2 hμ) (Real.rpow_pos_of_pos (by positivity) _)).ne'
  have hD := zeroMode_deriv_ne_zero hγ hγ2 hU
  have hs : Tendsto (fun t : ℝ => (sExp γ t α₂ α₃ : ℂ)) (𝓝[≠] t₀) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (sExp γ t α₂ α₃ : ℂ)) := by
      unfold sExp
      fun_prop
    have h0 : sExp γ t₀ α₂ α₃ = 0 := by
      unfold sExp
      rw [ht₀]
      simp
    have h := hc.tendsto t₀
    rw [h0, Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun t : ℝ => (μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) *
      ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ (-(sExp γ t α₂ α₃ : ℂ)))
      (𝓝[≠] t₀) (𝓝 1) := by
    have h1 := zeroMode_tendsto_cpow hμc hs
    have h2 := zeroMode_tendsto_cpow hBc (by simpa using hs.neg)
    simpa using h1.mul h2
  have hI := zeroMode_tendsto_inv_gamma hs
  have hR := zeroMode_tendsto_slope_comp hU.1 (zeroMode_zero hγ hγ2 hU) t₀
  have hBr := zeroMode_bracket_limit hγ hγ2 hU ht₀ h₁ h₁' h₂ h₂' h₃ h₃'
  have hmain := (((hP.mul hI).mul (tendsto_const_nhds (x := (2 / (γ : ℂ))))).mul
    ((tendsto_const_nhds (x := deriv U 0)).div hR hD)).mul hBr
  rw [div_self hD] at hmain
  simp only [one_mul, mul_one] at hmain
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (zeroMode_formula_eq hγ ht₀ ht).symm

/-- **The DOZZ companion at the zero mode.** As `α₁ → 2Q - α₂ - α₃` (so `s → 0`),
`μ^s Γ(s)⁻¹ D(α₁, α₂, α₃) → 2/γ`: the zero of `Υ` at `0` in the denominator cancels the pole of
`Γ(s)`, and `Υ(Q - x) = Υ(x)` cancels the remaining charge factors. -/
theorem dozzFormula_zeroMode_limit {γ μ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hU : IsUpsilon γ U) {α₂ α₃ : ℝ} (h₂ : 0 < α₂) (h₂' : α₂ < Q γ) (h₃ : 0 < α₃)
    (h₃' : α₃ < Q γ) (h₁ : 0 < 2 * Q γ - α₂ - α₃) (h₁' : 2 * Q γ - α₂ - α₃ < Q γ) :
    Tendsto (fun t : ℝ => ((μ : ℂ) ^ (sExp γ t α₂ α₃ : ℂ) / Complex.Gamma (sExp γ t α₂ α₃)) *
        dozzFormula γ μ U t α₂ α₃) (𝓝[≠] (2 * Q γ - α₂ - α₃)) (𝓝 (2 / γ)) :=
  zeroMode_limit_aux hγ hγ2 hμ hU (t₀ := 2 * Q γ - α₂ - α₃) (by ring) h₁ h₁' h₂ h₂' h₃ h₃'

end DOZZ.Proofs

end
