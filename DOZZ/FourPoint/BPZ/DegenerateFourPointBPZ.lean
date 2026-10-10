/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.BPZAssemblyA
public import DOZZ.FourPoint.BPZ.WardCombL
public import DOZZ.FourPoint.BPZ.WardCombR
public import DOZZ.FourPoint.BPZ.WirtingerMoment
public import DOZZ.FourPoint.BPZ.GaussAlgebra
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC
public import DOZZ.Statements.FourPoint.FourPointT

/-! # The BPZ equation for the degenerate four-point function

For a degenerate insertion `χ ∈ {γ/2, 2/γ}` the reduced four-point function
`T(z) = 2 μ^{-s} Γ(s) γ⁻¹ E[I(z)^{-s}]` is `C²` off `0` and `1` and solves the Gauss equation with
the parameters `A`, `B`, `C` of [KRV, (defabcfirst)]. The proof combines

* the regularity of the negative moment and the Wirtinger forms of its derivatives
  (`∂T = -s K a E₁`, `∂²T = s(s+1) K a² D₂ - s K a(a-1) D₁`);
* the Ward identity for the test function `g(x) = x(x - 1)/(z - x)`, whose four real components
  combine into `c₀ J + c₁ E₁ + (1 - a) z(z-1) D₁ = (s+1)(γ²/4)(J - z(z-1) D₂)`;
* the coefficient algebra, which uses `χ² - χ Q + 1 = 0` and `(1 - a)(γ² - 4a) = 0`.

The GMC measure is first replaced by a measurable version, which has the same reduced function. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The BPZ equation, for a measurable GMC measure. -/
theorem bpz_gauss_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (hMm : Measurable M) :
    IsRealGaussSolution
      (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃)
      (gaussParameterC γ χ α₁)
      (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z) := by
  have hχpos : 0 < χ := by
    rcases hχ with rfl | rfl
    · positivity
    · positivity
  have ha1 : γ * χ / 2 ≤ 1 := by
    rcases hχ with rfl | rfl
    · have h4 : γ * γ ≤ 4 := by nlinarith
      linarith
    · rw [show γ * (2 / γ) / 2 = 1 by field_simp]
  have hspos : 0 < fourPointSExp γ (-χ) α₁ α₂ α₃ := by
    unfold fourPointSExp
    exact div_pos (by linarith) hγ
  obtain ⟨hC2, hW⟩ := bpz_fourPointT_contDiff_wirtinger P X hX hγ hγ₂ M hM hMm hχpos ha1 hα₁
    hα₂ hα₃ hspos μ
  refine ⟨hC2, fun z hz => ?_⟩
  obtain ⟨hW1, hW2⟩ := hW z hz
  obtain ⟨-, hE1⟩ := bpz_wirtL_momField1_zero P X hX hγ hγ₂ M hM hMm hχpos ha1 hα₁ hα₂ hα₃
    hspos.le hz.1 hz.2
  obtain ⟨-, hD⟩ := bpz_wirt2L_momField2_zero P X hX hγ hγ₂ M hM hMm hχpos ha1 hα₁ hα₂ hα₃
    hspos.le hz.1 hz.2
  have hL := bpz_wardLHS_combination P X hX hγ hγ₂ M hM hMm hχpos hα₁ hα₂ hα₃ hspos.le hz.1 hz.2
  have hR := bpz_wardRHS_combination P X hX hγ hγ₂ M hM hMm hχpos hα₁ hα₂ hα₃ hspos.le hz.1 hz.2
  have hw : ∀ (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ),
      bpzWardLHS P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z ℓ v =
        bpzWardRHS P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z ℓ v := fun ℓ v =>
    bpzWardLHS_eq_wardRHS P X hX hγ hγ₂ M hM hMm hχpos hα₁ hα₂ hα₃ hspos.le hz.1 hz.2 ℓ v
  simp only [hw] at hL
  have hward := hL.symm.trans hR
  have hT : fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
      2 * μ ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) / γ * Real.Gamma (fourPointSExp γ (-χ) α₁ α₂ α₃) *
        bpzMomJ P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z :=
    bpz_fourPointT_eq_moment P X hX hγ hγ₂ M hM hMm hχpos hα₁ hα₂ hα₃ μ hz.1 hz.2
  refine bpz_gauss_of_ward hγ hχ hz.1 hz.2
    (2 * μ ^ (-fourPointSExp γ (-χ) α₁ α₂ α₃) / γ * Real.Gamma (fourPointSExp γ (-χ) α₁ α₂ α₃))
    (bpzMomJ P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z)
    (fourPointT P M γ μ (-χ) α₁ α₂ α₃ z)
    (bpzMomE1 P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z)
    (bpzMomD1 P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z)
    (bpzMomD2 P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z)
    _ _ hT ?_ ?_ hward
  · rw [hW1, hE1]
    push_cast
    ring
  · rw [hW2, hD]
    push_cast
    ring

/-- **The BPZ equation** (proof of `DOZZ.degenerateFourPoint_BPZ`): for either degenerate
insertion, the reduced function `T` satisfies the Wirtinger form of the Gauss equation with the
parameters of [KRV, (defabcfirst)]. -/
theorem degenerateFourPoint_BPZ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsRealGaussSolution
      (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃)
      (gaussParameterC γ χ α₁)
      (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z) := by
  let _ := hμ
  obtain ⟨N, hNm, hNfin, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ₂ M hM
  have hN : IsGMCOf P X γ N := bpz_isGMCOf_congr hM hNfin hMN
  have hT : (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z) =
      fun z => fourPointT P N γ μ (-χ) α₁ α₂ α₃ z :=
    funext fun z => bpz_fourPointT_congr P hMN μ (-χ) z
  rw [hT]
  exact bpz_gauss_of_measurable P X N γ μ χ α₁ α₂ α₃ hγ hγ₂ hχ hα₁ hα₂ hα₃ hs hX hN hNm

end DOZZ.Proofs
