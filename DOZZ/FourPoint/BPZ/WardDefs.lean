/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardG

/-! # The moments entering the BPZ equation

With `k = bpzSoftWeight γ χ α₁ α₂ α₃ 0 z` the degenerate four-point weight and `I = ∫ k dM` the
four-point mass, we name the expectations

* `J = E[I^{-s}]`,
* `E₁ = E[I^{-s-1} ∫ k(x)/(z - x) dM(x)]`,
* `D₁ = E[I^{-s-1} ∫ k(x)/(z - x)² dM(x)]`,
* `D₂ = E[I^{-s-2} (∫ k(x)/(z - x) dM(x))²]`,

and the two sides of the real Ward identity for the test function `ℓ ∘ g`,
`g(x) = x (x - 1)/(z - x)`, in the direction `v`. -/

@[expose] public section

open MeasureTheory

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω] {γ χ α₁ α₂ α₃ : ℝ}

/-- The left side of the real Ward identity for `ℓ ∘ g` in the direction `v`. -/
noncomputable def bpzWardLHS (P : Measure Ω) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ s : ℝ) (z : ℂ)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : ℝ :=
  ∫ ω, (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-(s + 1)) *
    ∫ x, fderiv ℝ (fun x => ℓ (bpzG z x) * bpzTildeWeight γ χ α₁ α₂ z x) x v *
      normPlus x ^ (γ * (α₁ + α₂ + α₃ - χ)) ∂M ω ∂P

/-- The right side of the real Ward identity for `ℓ ∘ g` in the direction `v`. -/
noncomputable def bpzWardRHS (P : Measure Ω) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ s : ℝ) (z : ℂ)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) : ℝ :=
  ∫ ω, (s + 1) * ((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-(s + 1) - 1) *
    (γ ^ 2 * ∫ x, ∫ y, (ℓ (bpzG z x) - ℓ (bpzG z y)) * (bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x *
      bpzSoftWeight γ χ α₁ α₂ α₃ 0 z y) * bpzKern v (x - y) / 2 ∂M ω ∂M ω)) ∂P

/-- The real Ward identity for `ℓ ∘ g`. -/
theorem bpzWardLHS_eq_wardRHS (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMm : Measurable M)
    (hχ : 0 < χ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 0 ≤ fourPointSExp γ (-χ) α₁ α₂ α₃) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (ℓ : ℂ →L[ℝ] ℝ) (v : ℂ) :
    bpzWardLHS P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z ℓ v =
      bpzWardRHS P M γ χ α₁ α₂ α₃ (fourPointSExp γ (-χ) α₁ α₂ α₃) z ℓ v :=
  bpz_fourPoint_ward_g P X hX hγ hγ2 M hM hMm hχ hα₁ hα₂ hα₃ hs hz0 hz1 ℓ v

/-- `J = E[I^{-s}]`. -/
noncomputable def bpzMomJ (P : Measure Ω) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ s : ℝ) (z : ℂ) :
    ℝ :=
  ∫ ω, (∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s) ∂P

/-- `E₁ = E[I^{-s-1} ∫ k(x)/(z - x) dM(x)]`. -/
noncomputable def bpzMomE1 (P : Measure Ω) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ s : ℝ) (z : ℂ) :
    ℂ :=
  ∫ ω, (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
    ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂M ω ∂P

/-- `D₁ = E[I^{-s-1} ∫ k(x)/(z - x)² dM(x)]`. -/
noncomputable def bpzMomD1 (P : Measure Ω) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ s : ℝ) (z : ℂ) :
    ℂ :=
  ∫ ω, (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 1) : ℝ) : ℂ) *
    ∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ^ 2 ∂M ω ∂P

/-- `D₂ = E[I^{-s-2} (∫ k(x)/(z - x) dM(x))²]`. -/
noncomputable def bpzMomD2 (P : Measure Ω) (M : Ω → Measure ℂ) (γ χ α₁ α₂ α₃ s : ℝ) (z : ℂ) :
    ℂ :=
  ∫ ω, (((∫ x, bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x ∂M ω) ^ (-s - 2) : ℝ) : ℂ) *
    (∫ x, ((bpzSoftWeight γ χ α₁ α₂ α₃ 0 z x : ℝ) : ℂ) / (z - x) ∂M ω) ^ 2 ∂P

end DOZZ.Proofs
