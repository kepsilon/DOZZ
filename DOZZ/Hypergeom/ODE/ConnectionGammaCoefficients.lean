/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionMidpointCramer
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Parameter regularity of the four Gamma coefficients in the connection formulas. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The first Gamma coefficient in the zero-to-one connection formula. -/
noncomputable def gaussConnectionMinusGammaCoefficient₁ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma p.2.2 * Complex.Gamma (p.2.2 - p.1 - p.2.1) *
    (Complex.Gamma (p.2.2 - p.1))⁻¹ * (Complex.Gamma (p.2.2 - p.2.1))⁻¹

/-- The second Gamma coefficient in the zero-to-one connection formula. -/
noncomputable def gaussConnectionMinusGammaCoefficient₂ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma p.2.2 * Complex.Gamma (p.1 + p.2.1 - p.2.2) *
    (Complex.Gamma p.1)⁻¹ * (Complex.Gamma p.2.1)⁻¹

/-- The first Gamma coefficient in the powered zero-to-one connection formula. -/
noncomputable def gaussConnectionPlusGammaCoefficient₁ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma (2 - p.2.2) * Complex.Gamma (p.2.2 - p.1 - p.2.1) *
    (Complex.Gamma (1 - p.1))⁻¹ * (Complex.Gamma (1 - p.2.1))⁻¹

/-- The second Gamma coefficient in the powered zero-to-one connection formula. -/
noncomputable def gaussConnectionPlusGammaCoefficient₂ (p : ℂ × ℂ × ℂ) : ℂ :=
  Complex.Gamma (2 - p.2.2) * Complex.Gamma (p.1 + p.2.1 - p.2.2) *
    (Complex.Gamma (p.1 - p.2.2 + 1))⁻¹ *
      (Complex.Gamma (p.2.1 - p.2.2 + 1))⁻¹

private theorem connection_c_polefree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ n : ℕ, p.2.2 ≠ -(n : ℂ) := by
  intro n he
  exact hp.1 (-(n : ℤ)) (by simpa using he)

private theorem connection_delta_polefree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ n : ℕ, p.2.2 - p.1 - p.2.1 ≠ -(n : ℂ) := by
  intro n he
  exact hp.2 (-(n : ℤ)) (by simpa using he)

private theorem connection_neg_delta_polefree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ n : ℕ, p.1 + p.2.1 - p.2.2 ≠ -(n : ℂ) := by
  intro n he
  apply hp.2 n
  have he' := congrArg (fun z : ℂ => -z) he
  linear_combination he'

private theorem connection_two_sub_c_polefree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ n : ℕ, 2 - p.2.2 ≠ -(n : ℂ) := by
  intro n he
  apply hp.1 ((n : ℤ) + 2)
  have hcast : p.2.2 = (((n : ℤ) + 2 : ℤ) : ℂ) := by
    push_cast at he ⊢
    linear_combination -he
  exact hcast

private theorem gamma_comp_differentiableAt
    {p : ℂ × ℂ × ℂ} (f : ℂ × ℂ × ℂ → ℂ)
    (hf : DifferentiableAt ℂ f p)
    (hfree : ∀ n : ℕ, f p ≠ -(n : ℂ)) :
    DifferentiableAt ℂ (fun q => Complex.Gamma (f q)) p := by
  have hGamma := Complex.differentiableAt_Gamma (f p) hfree
  change DifferentiableAt ℂ (Complex.Gamma ∘ f) p
  exact hGamma.comp p hf

private theorem invGamma_comp_differentiableAt
    {p : ℂ × ℂ × ℂ} (f : ℂ × ℂ × ℂ → ℂ)
    (hf : DifferentiableAt ℂ f p) :
    DifferentiableAt ℂ (fun q => (Complex.Gamma (f q))⁻¹) p := by
  have hGammaInv : Differentiable ℂ (fun z : ℂ => (Complex.Gamma z)⁻¹) :=
    Complex.differentiable_one_div_Gamma
  have hAt := hGammaInv (f p)
  change DifferentiableAt ℂ ((fun z : ℂ => (Complex.Gamma z)⁻¹) ∘ f) p
  exact hAt.comp p hf

/-- The first unpowered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionMinusGammaCoefficient₁_differentiableAt
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ gaussConnectionMinusGammaCoefficient₁ p := by
  have hc : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p := by fun_prop
  have hδ : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) p := by fun_prop
  have hca : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1) p := by fun_prop
  have hcb : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.2.2 - q.2.1) p := by fun_prop
  have hGammaC := gamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => q.2.2) hc
    (connection_c_polefree hp)
  have hGammaDelta := gamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) hδ (connection_delta_polefree hp)
  have hRecipCA := invGamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1) hca
  have hRecipCB := invGamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.2.2 - q.2.1) hcb
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    Complex.Gamma q.2.2 * Complex.Gamma (q.2.2 - q.1 - q.2.1) *
      (Complex.Gamma (q.2.2 - q.1))⁻¹ * (Complex.Gamma (q.2.2 - q.2.1))⁻¹) p
  exact ((hGammaC.mul hGammaDelta).mul hRecipCA).mul hRecipCB

/-- The second unpowered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionMinusGammaCoefficient₂_differentiableAt
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ gaussConnectionMinusGammaCoefficient₂ p := by
  have hc : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.2) p := by fun_prop
  have hNegDelta : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.1 + q.2.1 - q.2.2) p := by fun_prop
  have ha : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.1) p := by fun_prop
  have hb : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1) p := by fun_prop
  have hGammaC := gamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => q.2.2) hc
    (connection_c_polefree hp)
  have hGammaNegDelta := gamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.1 + q.2.1 - q.2.2) hNegDelta
    (connection_neg_delta_polefree hp)
  have hRecipA := invGamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => q.1) ha
  have hRecipB := invGamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => q.2.1) hb
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    Complex.Gamma q.2.2 * Complex.Gamma (q.1 + q.2.1 - q.2.2) *
      (Complex.Gamma q.1)⁻¹ * (Complex.Gamma q.2.1)⁻¹) p
  exact ((hGammaC.mul hGammaNegDelta).mul hRecipA).mul hRecipB

/-- The first powered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionPlusGammaCoefficient₁_differentiableAt
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ gaussConnectionPlusGammaCoefficient₁ p := by
  have hC : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 2 - q.2.2) p := by fun_prop
  have hDelta : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) p := by fun_prop
  have hOneA : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.1) p := by fun_prop
  have hOneB : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.1) p := by fun_prop
  have hGammaC := gamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => 2 - q.2.2) hC
    (connection_two_sub_c_polefree hp)
  have hGammaDelta := gamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) hDelta
    (connection_delta_polefree hp)
  have hRecipA := invGamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => 1 - q.1) hOneA
  have hRecipB := invGamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => 1 - q.2.1) hOneB
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    Complex.Gamma (2 - q.2.2) * Complex.Gamma (q.2.2 - q.1 - q.2.1) *
      (Complex.Gamma (1 - q.1))⁻¹ * (Complex.Gamma (1 - q.2.1))⁻¹) p
  exact ((hGammaC.mul hGammaDelta).mul hRecipA).mul hRecipB

/-- The second powered Gamma coefficient is differentiable throughout the connection domain. -/
theorem gaussConnectionPlusGammaCoefficient₂_differentiableAt
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ gaussConnectionPlusGammaCoefficient₂ p := by
  have hC : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 2 - q.2.2) p := by fun_prop
  have hNegDelta : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.1 + q.2.1 - q.2.2) p := by fun_prop
  have hAC : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.1 - q.2.2 + 1) p := by fun_prop
  have hBC : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q.2.1 - q.2.2 + 1) p := by fun_prop
  have hGammaC := gamma_comp_differentiableAt (fun q : ℂ × ℂ × ℂ => 2 - q.2.2) hC
    (connection_two_sub_c_polefree hp)
  have hGammaNegDelta := gamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.1 + q.2.1 - q.2.2) hNegDelta
    (connection_neg_delta_polefree hp)
  have hRecipAC := invGamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.1 - q.2.2 + 1) hAC
  have hRecipBC := invGamma_comp_differentiableAt
    (fun q : ℂ × ℂ × ℂ => q.2.1 - q.2.2 + 1) hBC
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    Complex.Gamma (2 - q.2.2) * Complex.Gamma (q.1 + q.2.1 - q.2.2) *
      (Complex.Gamma (q.1 - q.2.2 + 1))⁻¹ *
        (Complex.Gamma (q.2.1 - q.2.2 + 1))⁻¹) p
  exact ((hGammaC.mul hGammaNegDelta).mul hRecipAC).mul hRecipBC

end DOZZ.Proofs
