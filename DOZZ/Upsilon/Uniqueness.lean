/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import DOZZ.Upsilon.StripIdentities

/-!
# Uniqueness of the entire Upsilon continuation
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private theorem openStrip_mem_nhds (q : ℝ) (hq : 0 < q) :
    {z : ℂ | 0 < z.re ∧ z.re < q} ∈ 𝓝 ((q : ℂ) / 2) := by
  let S : Set ℂ := {z | 0 < z.re ∧ z.re < q}
  let c : ℂ := (q : ℂ) / 2
  have hc : c ∈ S := by
    dsimp [c, S]
    simp only [Complex.div_ofNat_re, Complex.ofReal_re]
    constructor <;> linarith
  have hOpen : IsOpen S := by
    change IsOpen (Complex.re ⁻¹' Set.Ioo 0 q)
    exact isOpen_Ioo.preimage Complex.continuous_re
  simpa [S] using hOpen.mem_nhds hc

/-- Uniqueness of `Υ_{γ/2}` (identity theorem on the strip). -/
theorem IsUpsilon.unique {U V : ℂ → ℂ} (hγ : 0 < γ) (hU : IsUpsilon γ U)
    (hV : IsUpsilon γ V) : U = V := by
  have hQ : 0 < Q γ := by
    unfold Q
    positivity
  let c : ℂ := (Q γ : ℂ) / 2
  let S : Set ℂ := {z | 0 < z.re ∧ z.re < Q γ}
  have hS : S ∈ 𝓝 c := by
    simpa [c] using openStrip_mem_nhds (Q γ) hQ
  have hEq : U =ᶠ[𝓝 c] V := by
    filter_upwards [hS] with z hz
    dsimp [S] at hz
    exact (hU.2 z hz.1 hz.2).trans (hV.2 z hz.1 hz.2).symm
  have hUA : AnalyticOnNhd ℂ U Set.univ := fun z _ => hU.1.analyticAt z
  have hVA : AnalyticOnNhd ℂ V Set.univ := fun z _ => hV.1.analyticAt z
  exact AnalyticOnNhd.eq_of_eventuallyEq hUA hVA hEq

/-- Reflection symmetry `Υ(Q - z) = Υ(z)`. -/
theorem IsUpsilon.reflect {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) :
    U (Q γ - z) = U z := by
  have hratio : γ / 2 < 2 / γ := by
    apply (div_lt_iff₀ (show (0 : ℝ) < 2 by norm_num)).2
    rw [show 2 / γ * 2 = 4 / γ by ring]
    apply (lt_div_iff₀ hγ).2
    have h1 : 0 < 2 - γ := by linarith
    have h2 : 0 < 2 + γ := by linarith
    have hprod := mul_pos h1 h2
    nlinarith
  have hγQ : γ < Q γ := by
    unfold Q
    linarith
  have hQ : 0 < Q γ := by linarith
  let S : Set ℂ := {w | 0 < w.re ∧ w.re < Q γ}
  have hS : S ∈ 𝓝 ((Q γ : ℂ) / 2) := by
    simpa [S] using openStrip_mem_nhds (Q γ) hQ
  have hEq : (fun w : ℂ => U ((Q γ : ℂ) - w)) =ᶠ[𝓝 ((Q γ : ℂ) / 2)] U := by
    filter_upwards [hS] with w hw
    dsimp [S] at hw
    have hw' : 0 < ((Q γ : ℂ) - w).re ∧ ((Q γ : ℂ) - w).re < Q γ := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      constructor <;> linarith
    calc
      U ((Q γ : ℂ) - w) = Complex.exp (upsilonLog γ ((Q γ : ℂ) - w)) :=
        hU.2 ((Q γ : ℂ) - w) hw'.1 hw'.2
      _ = Complex.exp (upsilonLog γ w) := by
        rw [upsilonLog_reflect γ w hw.1 hw.2]
      _ = U w := (hU.2 w hw.1 hw.2).symm
  have hUanalytic : AnalyticOnNhd ℂ U Set.univ := fun w _ => hU.1.analyticAt w
  have hVdiff : Differentiable ℂ (fun w : ℂ => U ((Q γ : ℂ) - w)) := by
    apply hU.1.comp
    fun_prop
  have hVanalytic : AnalyticOnNhd ℂ (fun w : ℂ => U ((Q γ : ℂ) - w)) Set.univ :=
    fun w _ => hVdiff.analyticAt w
  have hFunext := AnalyticOnNhd.eq_of_eventuallyEq hVanalytic hUanalytic hEq
  exact congrFun hFunext z

end DOZZ.Proofs
