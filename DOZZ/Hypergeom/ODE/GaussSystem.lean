/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! The Gauss scalar equation as a first-order holomorphic system on its regular domain. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The first coefficient in the first-order Gauss system for the state `(f, f')`. -/
noncomputable def gaussSystemCoeff₁ (a b : ℂ) (z : ℂ) : ℂ :=
  (z * (1 - z))⁻¹ * (a * b)

/-- The second coefficient in the first-order Gauss system for the state `(f, f')`. -/
noncomputable def gaussSystemCoeff₂ (a b c : ℂ) (z : ℂ) : ℂ :=
  (z * (1 - z))⁻¹ * ((a + b + 1) * z - c)

/-- Coefficient operator for the Gauss first-order system on `ℂ × ℂ`. -/
noncomputable def gaussSystemOperator (a b c z : ℂ) :
    ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  let firstOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (1, 0)
  let secondOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (0, 1)
  (firstOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)) +
    ((gaussSystemCoeff₁ a b z) • (secondOutput.comp (ContinuousLinearMap.fst ℂ ℂ ℂ)) +
      (gaussSystemCoeff₂ a b c z) • (secondOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)))

@[simp] theorem gaussSystemOperator_apply (a b c z : ℂ) (y : ℂ × ℂ) :
    gaussSystemOperator a b c z y =
      (y.2, gaussSystemCoeff₁ a b z * y.1 + gaussSystemCoeff₂ a b c z * y.2) := by
  simp [gaussSystemOperator, gaussSystemCoeff₁, gaussSystemCoeff₂,
    ContinuousLinearMap.smulRight_apply]

theorem gaussRegularPlane_isOpen : IsOpen gaussRegularPlane := by
  change IsOpen ({z : ℂ | z ≠ 0} ∩ {z : ℂ | z ≠ 1})
  exact isOpen_ne.inter isOpen_ne

theorem gaussSystemCoeff₁_differentiableOn (a b : ℂ) :
    DifferentiableOn ℂ (gaussSystemCoeff₁ a b) gaussRegularPlane := by
  have hden : DifferentiableOn ℂ (fun z : ℂ => z * (1 - z)) gaussRegularPlane := by
    exact differentiableOn_id.mul ((differentiableOn_const 1).sub differentiableOn_id)
  have hden_ne : ∀ z ∈ gaussRegularPlane, z * (1 - z) ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := hz.1
    have hz1 : z ≠ 1 := hz.2
    apply mul_ne_zero hz0
    intro hz'
    apply hz1
    linear_combination -hz'
  have hinv : DifferentiableOn ℂ (fun z : ℂ => (z * (1 - z))⁻¹) gaussRegularPlane :=
    hden.inv hden_ne
  change DifferentiableOn ℂ (fun z : ℂ => (z * (1 - z))⁻¹ * (a * b)) gaussRegularPlane
  exact hinv.mul_const (a * b)

theorem gaussSystemCoeff₂_differentiableOn (a b c : ℂ) :
    DifferentiableOn ℂ (gaussSystemCoeff₂ a b c) gaussRegularPlane := by
  have hden : DifferentiableOn ℂ (fun z : ℂ => z * (1 - z)) gaussRegularPlane := by
    exact differentiableOn_id.mul ((differentiableOn_const 1).sub differentiableOn_id)
  have hden_ne : ∀ z ∈ gaussRegularPlane, z * (1 - z) ≠ 0 := by
    intro z hz
    have hz0 : z ≠ 0 := hz.1
    have hz1 : z ≠ 1 := hz.2
    apply mul_ne_zero hz0
    intro hz'
    apply hz1
    linear_combination -hz'
  have hinv : DifferentiableOn ℂ (fun z : ℂ => (z * (1 - z))⁻¹) gaussRegularPlane :=
    hden.inv hden_ne
  have hlin : DifferentiableOn ℂ (fun z : ℂ => (a + b + 1) * z - c) gaussRegularPlane := by
    exact (differentiableOn_const (a + b + 1)).mul differentiableOn_id |>.sub
      (differentiableOn_const c)
  change DifferentiableOn ℂ
    (fun z : ℂ => (z * (1 - z))⁻¹ * ((a + b + 1) * z - c)) gaussRegularPlane
  exact hinv.mul hlin

theorem gaussSystemOperator_differentiableOn (a b c : ℂ) :
    DifferentiableOn ℂ (gaussSystemOperator a b c) gaussRegularPlane := by
  let firstOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (1, 0)
  let secondOutput : ℂ →L[ℂ] ℂ × ℂ :=
    (ContinuousLinearMap.id ℂ ℂ).smulRight (0, 1)
  let firstComponent : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    firstOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  let secondFromFirst : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    secondOutput.comp (ContinuousLinearMap.fst ℂ ℂ ℂ)
  let secondFromSecond : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
    secondOutput.comp (ContinuousLinearMap.snd ℂ ℂ ℂ)
  have hfirstComponent : DifferentiableOn ℂ (fun _ : ℂ => firstComponent) gaussRegularPlane :=
    differentiableOn_const _
  have hsecondFromFirst : DifferentiableOn ℂ
      (fun _ : ℂ => secondFromFirst) gaussRegularPlane :=
    differentiableOn_const _
  have hsecondFromSecond : DifferentiableOn ℂ
      (fun _ : ℂ => secondFromSecond) gaussRegularPlane :=
    differentiableOn_const _
  have hrow₁ : DifferentiableOn ℂ
      (fun z : ℂ => gaussSystemCoeff₁ a b z • secondFromFirst)
      gaussRegularPlane :=
    gaussSystemCoeff₁_differentiableOn a b |>.smul hsecondFromFirst
  have hrow₂ : DifferentiableOn ℂ
      (fun z : ℂ => gaussSystemCoeff₂ a b c z • secondFromSecond)
      gaussRegularPlane :=
    gaussSystemCoeff₂_differentiableOn a b c |>.smul hsecondFromSecond
  change DifferentiableOn ℂ
    (fun z : ℂ => firstComponent + (gaussSystemCoeff₁ a b z • secondFromFirst +
      gaussSystemCoeff₂ a b c z • secondFromSecond)) gaussRegularPlane
  exact hfirstComponent.add (hrow₁.add hrow₂)

theorem gaussHolomorphicOperator_eq_mul_system_residual
    (a b c : ℂ) (f : ℂ → ℂ) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    gaussHolomorphicOperator a b c f z =
      z * (1 - z) * (deriv (deriv f) z -
        (gaussSystemCoeff₁ a b z * f z + gaussSystemCoeff₂ a b c z * deriv f z)) := by
  have hden : z * (1 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))
  simp only [gaussHolomorphicOperator, gaussSystemCoeff₁, gaussSystemCoeff₂]
  field_simp
  ring

theorem gaussHolomorphicOperator_eq_zero_iff_system_residual_eq_zero
    (a b c : ℂ) (f : ℂ → ℂ) {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    gaussHolomorphicOperator a b c f z = 0 ↔
      deriv (deriv f) z =
        gaussSystemCoeff₁ a b z * f z + gaussSystemCoeff₂ a b c z * deriv f z := by
  rw [gaussHolomorphicOperator_eq_mul_system_residual a b c f hz0 hz1]
  have hden : z * (1 - z) ≠ 0 := mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz1))
  constructor
  · intro h
    have hres := (mul_eq_zero.mp h).resolve_left hden
    exact sub_eq_zero.mp hres
  · intro h
    simp [h]

end DOZZ.Proofs
