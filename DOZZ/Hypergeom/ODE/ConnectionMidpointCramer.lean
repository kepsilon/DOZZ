/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionMidpointDerivatives
public import DOZZ.Hypergeom.BasisWronskians
public import DOZZ.Hypergeom.BasisSpanning

/-! Holomorphic midpoint Cramer coefficients for the connection expansions. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The Wronskian of the one-end local basis, evaluated at the common midpoint. -/
noncomputable def connectionMidpointOneWronskian
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)

private theorem connectionMidpointOneWronskian_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ (fun q => connectionMidpointOneWronskian H q) p := by
  have hGm := gaussGMinus_midpoint_differentiableAt_params hH hp
  have hGm' := gaussGMinus_midpoint_deriv_differentiableAt_params hH hp
  have hGp := gaussGPlus_midpoint_differentiableAt_params hH hp
  have hGp' := gaussGPlus_midpoint_deriv_differentiableAt_params hH hp
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
      deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
        gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p
  exact (hGm.mul hGp').sub (hGm'.mul hGp)

private theorem connectionMidpointOneWronskian_ne_zero
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    connectionMidpointOneWronskian H p ≠ 0 := by
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hw := gaussGPlus_wronskian_identity hH p.1 p.2.1 p.2.2 hp.2 (1 / 2 : ℂ) hmid
  have hδ : p.2.2 - p.1 - p.2.1 ≠ 0 := by
    have := hp.2 0
    simpa using this
  have hformula : connectionMidpointOneWronskian H p =
      -(p.2.2 - p.1 - p.2.1) * (1 / 2 : ℂ) ^ (-p.2.2) *
        (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) := by
    have hw' := hw
    norm_num at hw'
    simpa [connectionMidpointOneWronskian] using hw'
  have hfactor : -(p.2.2 - p.1 - p.2.1) ≠ 0 := neg_ne_zero.mpr hδ
  have hpow₁ : (1 / 2 : ℂ) ^ (-p.2.2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hpow₂ : (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [hformula]
  exact mul_ne_zero (mul_ne_zero hfactor hpow₁) hpow₂

/-- The first midpoint Cramer quotient for expanding `FMinus` in the one-end basis. -/
noncomputable def connectionMinusFirstCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussFMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹

/-- The second midpoint Cramer quotient for expanding `FMinus` in the one-end basis. -/
noncomputable def connectionMinusSecondCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussFMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹

/-- The first Cramer coefficient in the expansion of the zero-basis solution in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionMinusFirstCramerCoefficient_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ (fun q => connectionMinusFirstCramerCoefficient H q) p := by
  have hFm := gaussFMinus_midpoint_differentiableAt_params hH hp
  have hFm' := gaussFMinus_midpoint_deriv_differentiableAt_params hH hp
  have hGp := gaussGPlus_midpoint_differentiableAt_params hH hp
  have hGp' := gaussGPlus_midpoint_deriv_differentiableAt_params hH hp
  have hnum : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      gaussFMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
          deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
        deriv (gaussFMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
          gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p :=
    (hFm.mul hGp').sub (hFm'.mul hGp)
  have hden := connectionMidpointOneWronskian_differentiableAt hH hp
  have hinv := hden.inv (connectionMidpointOneWronskian_ne_zero hH hp)
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    (gaussFMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
      deriv (gaussFMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
        gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul hinv

/-- The second Cramer coefficient in the expansion of the zero-basis solution in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionMinusSecondCramerCoefficient_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ (fun q => connectionMinusSecondCramerCoefficient H q) p := by
  have hGm := gaussGMinus_midpoint_differentiableAt_params hH hp
  have hGm' := gaussGMinus_midpoint_deriv_differentiableAt_params hH hp
  have hFm := gaussFMinus_midpoint_differentiableAt_params hH hp
  have hFm' := gaussFMinus_midpoint_deriv_differentiableAt_params hH hp
  have hnum : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
          deriv (gaussFMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
        deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
          gaussFMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p :=
    (hGm.mul hFm').sub (hGm'.mul hFm)
  have hden := connectionMidpointOneWronskian_differentiableAt hH hp
  have hinv := hden.inv (connectionMidpointOneWronskian_ne_zero hH hp)
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    (gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
        deriv (gaussFMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
      deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
        gaussFMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul hinv

/-- The first midpoint Cramer quotient for expanding `FPlus` in the one-end basis. -/
noncomputable def connectionPlusFirstCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussFPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹

/-- The second midpoint Cramer quotient for expanding `FPlus` in the one-end basis. -/
noncomputable def connectionPlusSecondCramerCoefficient
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (p : ℂ × ℂ × ℂ) : ℂ :=
  (gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
      deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
      gaussFPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ)) *
    (connectionMidpointOneWronskian H p)⁻¹

/-- The first Cramer coefficient for expanding the second zero-basis function in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionPlusFirstCramerCoefficient_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ (fun q => connectionPlusFirstCramerCoefficient H q) p := by
  have hFp := gaussFPlus_midpoint_differentiableAt_params hH hp
  have hFp' := gaussFPlus_midpoint_deriv_differentiableAt_params hH hp
  have hGp := gaussGPlus_midpoint_differentiableAt_params hH hp
  have hGp' := gaussGPlus_midpoint_deriv_differentiableAt_params hH hp
  have hnum : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      gaussFPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
          deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
        deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
          gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p :=
    (hFp.mul hGp').sub (hFp'.mul hGp)
  have hinv := (connectionMidpointOneWronskian_differentiableAt hH hp).inv
    (connectionMidpointOneWronskian_ne_zero hH hp)
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    (gaussFPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
      deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
        gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul hinv

/-- The second Cramer coefficient for expanding the second zero-basis function in the one-basis
varies holomorphically on the nonresonant connection domain. -/
theorem connectionPlusSecondCramerCoefficient_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ (fun q => connectionPlusSecondCramerCoefficient H q) p := by
  have hGm := gaussGMinus_midpoint_differentiableAt_params hH hp
  have hGm' := gaussGMinus_midpoint_deriv_differentiableAt_params hH hp
  have hFp := gaussFPlus_midpoint_differentiableAt_params hH hp
  have hFp' := gaussFPlus_midpoint_deriv_differentiableAt_params hH hp
  have hnum : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
          deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
        deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
          gaussFPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p :=
    (hGm.mul hFp').sub (hGm'.mul hFp)
  have hinv := (connectionMidpointOneWronskian_differentiableAt hH hp).inv
    (connectionMidpointOneWronskian_ne_zero hH hp)
  change DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
    (gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ) *
        deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) -
      deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ) *
        gaussFPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) *
      (connectionMidpointOneWronskian H q)⁻¹) p
  exact hnum.mul hinv

/-- On the cut plane, the zero-basis solution has its midpoint Cramer expansion in the one-basis.
This separates the ODE spanning argument from the later Gamma evaluation of the coefficients. -/
theorem gaussFMinus_eq_connectionMidpointCramer
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H p.1 p.2.1 p.2.2 z =
        connectionMinusFirstCramerCoefficient H p * gaussGMinus H p.1 p.2.1 p.2.2 z +
          connectionMinusSecondCramerCoefficient H p * gaussGPlus H p.1 p.2.1 p.2.2 z := by
  have hZero := gauss_local_basis_zero hH p.1 p.2.1 p.2.2 hp.1
  have hOne := gauss_local_basis_one hH p.1 p.2.1 p.2.2 hp.2
  have hspan := hOne.2.2.2 (gaussFMinus H p.1 p.2.1 p.2.2) hZero.1
    (fun z hz => (hZero.2.2.1 z hz).1)
  obtain ⟨v, hv, hvuniq⟩ := hspan
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hFmid : gaussFMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) =
      v.1 * gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) +
        v.2 * gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) := hv _ hmid
  have hGmAt : DifferentiableAt ℂ (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) :=
    (hOne.1 (1 / 2 : ℂ) hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hGpAt : DifferentiableAt ℂ (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) :=
    (hOne.2.1 (1 / 2 : ℂ) hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hsum := (hGmAt.hasDerivAt.const_mul v.1).add (hGpAt.hasDerivAt.const_mul v.2)
  have hFmid' : deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
      v.1 * deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) +
        v.2 * deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) := by
    have hEqOn : gaussCutPlane.EqOn (gaussFMinus H p.1 p.2.1 p.2.2)
        (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
          v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) := hv
    calc
      deriv (gaussFMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
          deriv (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
            v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) (1 / 2 : ℂ) :=
        hEqOn.deriv gaussCutPlane_isOpen hmid
      _ = v.1 * deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) +
          v.2 * deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) := hsum.deriv
  have hwne : connectionMidpointOneWronskian H p ≠ 0 :=
    connectionMidpointOneWronskian_ne_zero hH hp
  have hW : connectionMidpointOneWronskian H p =
      gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
          deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
        deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) := rfl
  have hWne : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
      deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) ≠ 0 := by
    rw [← hW]
    exact hwne
  have hWneComm : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
        deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) ≠ 0 := by
    convert hWne using 1; ring
  have hcoeff₁ : connectionMinusFirstCramerCoefficient H p = v.1 := by
    unfold connectionMinusFirstCramerCoefficient
    rw [hFmid, hFmid']
    rw [hW]
    field_simp [hWneComm]
    ring_nf
  have hcoeff₂ : connectionMinusSecondCramerCoefficient H p = v.2 := by
    unfold connectionMinusSecondCramerCoefficient
    rw [hFmid, hFmid']
    rw [hW]
    field_simp [hWneComm]
    ring_nf
  intro z hz
  rw [hcoeff₁, hcoeff₂]
  exact hv z hz

/-- On the cut plane, the second zero-basis solution has its midpoint Cramer expansion in the
one-basis. Gamma evaluation of these parameter-dependent coefficients is a separate step. -/
theorem gaussFPlus_eq_connectionMidpointCramer
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    ∀ z ∈ gaussCutPlane,
      gaussFPlus H p.1 p.2.1 p.2.2 z =
        connectionPlusFirstCramerCoefficient H p * gaussGMinus H p.1 p.2.1 p.2.2 z +
          connectionPlusSecondCramerCoefficient H p * gaussGPlus H p.1 p.2.1 p.2.2 z := by
  have hZero := gauss_local_basis_zero hH p.1 p.2.1 p.2.2 hp.1
  have hOne := gauss_local_basis_one hH p.1 p.2.1 p.2.2 hp.2
  have hspan := hOne.2.2.2 (gaussFPlus H p.1 p.2.1 p.2.2) hZero.2.1
    (fun z hz => (hZero.2.2.1 z hz).2.1)
  obtain ⟨v, hv, hvuniq⟩ := hspan
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hFmid : gaussFPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) =
      v.1 * gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) +
        v.2 * gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) := hv _ hmid
  have hGmAt : DifferentiableAt ℂ (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) :=
    (hOne.1 (1 / 2 : ℂ) hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hGpAt : DifferentiableAt ℂ (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) :=
    (hOne.2.1 (1 / 2 : ℂ) hmid).differentiableAt
      (gaussCutPlane_isOpen.mem_nhds hmid)
  have hsum := (hGmAt.hasDerivAt.const_mul v.1).add (hGpAt.hasDerivAt.const_mul v.2)
  have hFmid' : deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
      v.1 * deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) +
        v.2 * deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) := by
    have hEqOn : gaussCutPlane.EqOn (gaussFPlus H p.1 p.2.1 p.2.2)
        (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
          v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) := hv
    calc
      deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
          deriv (fun z => v.1 * gaussGMinus H p.1 p.2.1 p.2.2 z +
            v.2 * gaussGPlus H p.1 p.2.1 p.2.2 z) (1 / 2 : ℂ) :=
        hEqOn.deriv gaussCutPlane_isOpen hmid
      _ = v.1 * deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) +
          v.2 * deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) := hsum.deriv
  have hwne : connectionMidpointOneWronskian H p ≠ 0 :=
    connectionMidpointOneWronskian_ne_zero hH hp
  have hW : connectionMidpointOneWronskian H p =
      gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
          deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
        deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) := rfl
  have hWne : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
      deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) ≠ 0 := by
    rw [← hW]
    exact hwne
  have hWneComm : gaussGMinus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
        deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) -
      gaussGPlus H p.1 p.2.1 p.2.2 (1 / 2 : ℂ) *
        deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) ≠ 0 := by
    convert hWne using 1; ring
  have hcoeff₁ : connectionPlusFirstCramerCoefficient H p = v.1 := by
    unfold connectionPlusFirstCramerCoefficient
    rw [hFmid, hFmid', hW]
    field_simp [hWneComm]
    ring_nf
  have hcoeff₂ : connectionPlusSecondCramerCoefficient H p = v.2 := by
    unfold connectionPlusSecondCramerCoefficient
    rw [hFmid, hFmid', hW]
    field_simp [hWneComm]
    ring_nf
  intro z hz
  rw [hcoeff₁, hcoeff₂]
  exact hv z hz

end DOZZ.Proofs
