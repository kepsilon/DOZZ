/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesFamily
public import DOZZ.Hypergeom.ODE.ConnectionParameterDomain

/-! Parameter regularity of the four connection-basis values at the common midpoint. -/

@[expose] public section

namespace DOZZ.Proofs

private theorem connectionDomain_subset_poleFree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) : p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have h := hp.1 (-(n : ℤ))
  apply h
  simpa using hn

private def connectionFPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1 - p.2.2 + 1, p.2.1 - p.2.2 + 1, 2 - p.2.2)

private def connectionGMinusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1, p.2.1, 1 + p.1 + p.2.1 - p.2.2)

private def connectionGPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.2.2 - p.2.1, p.2.2 - p.1, 1 + p.2.2 - p.1 - p.2.1)

private theorem connectionFPlusParameters_mem
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    connectionFPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 = (n : ℂ) + 2 := by
    dsimp [connectionFPlusParameters] at hn
    linear_combination -hn
  have hcast : p.2.2 = (((n : ℤ) + 2 : ℤ) : ℂ) := by
    calc
      p.2.2 = (n : ℂ) + 2 := hcastNat
      _ = (((n : ℤ) + 2 : ℤ) : ℂ) := by push_cast; ring
  exact (hp.1 ((n : ℤ) + 2)) hcast

private theorem connectionGMinusParameters_mem
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    connectionGMinusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := by
    dsimp [connectionGMinusParameters] at hn
    linear_combination -hn
  have hcast : p.2.2 - p.1 - p.2.1 = (((n : ℤ) + 1 : ℤ) : ℂ) := by
    calc
      p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := hcastNat
      _ = (((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
  exact (hp.2 ((n : ℤ) + 1)) hcast

private theorem connectionGPlusParameters_mem
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    connectionGPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := by
    dsimp [connectionGPlusParameters] at hn
    linear_combination hn
  let m : ℤ := -((n : ℤ) + 1)
  have hcast : p.2.2 - p.1 - p.2.1 = (m : ℂ) := by
    calc
      p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := hcastNat
      _ = -(((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
      _ = (m : ℂ) := by dsimp [m]; rw [Int.cast_neg]
  exact (hp.2 m) hcast

private theorem familyParameterValue_comp_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : ℂ × ℂ × ℂ)
    (S : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ)
    (hS : S p ∈ gaussParameterPoleFreeDomain)
    (hSDiff : DifferentiableAt ℂ S p) (z : ℂ) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => H (S q).1 (S q).2.1 (S q).2.2 z) p := by
  have hOn := IsGaussHypergeometricFamily.differentiableOn_params_unitDisk hH hz
  have hAt : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) (S p) :=
    (hOn (S p) hS).differentiableAt
      (gaussParameterPoleFreeDomain_isOpen.mem_nhds hS)
  change DifferentiableAt ℂ
    ((fun q : ℂ × ℂ × ℂ => H q.1 q.2.1 q.2.2 z) ∘ S) p
  exact hAt.comp p hSDiff

/-- The first zero-basis value at `1/2` varies holomorphically with the parameters on the
nonresonant connection domain. -/
theorem gaussFMinus_midpoint_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussFMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have hp0 := connectionDomain_subset_poleFree hp
  have hmap : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q) p := by fun_prop
  have h := familyParameterValue_comp_differentiableAt hH p id hp0 hmap
    (1 / 2 : ℂ) (by norm_num)
  simpa [gaussFMinus] using h

/-- The second zero-basis value at `1/2` varies holomorphically with the parameters. -/
theorem gaussFPlus_midpoint_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussFPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have hSDiff : DifferentiableAt ℂ connectionFPlusParameters p := by
    fun_prop [connectionFPlusParameters]
  have hvalue := familyParameterValue_comp_differentiableAt hH p connectionFPlusParameters
    (connectionFPlusParameters_mem hp) hSDiff (1 / 2 : ℂ) (by norm_num)
  have hpower : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (1 - q.2.2)) p := by
    have hExponent : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p := by
      fun_prop
    exact hExponent.const_cpow (Or.inl (by norm_num))
  change DifferentiableAt ℂ
    (fun q => (1 / 2 : ℂ) ^ (1 - q.2.2) *
      H (q.1 - q.2.2 + 1) (q.2.1 - q.2.2 + 1) (2 - q.2.2) (1 / 2 : ℂ)) p
  exact hpower.mul hvalue

/-- The first one-basis value at `1/2` varies holomorphically with the parameters. -/
theorem gaussGMinus_midpoint_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussGMinus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have hSDiff : DifferentiableAt ℂ connectionGMinusParameters p := by
    fun_prop [connectionGMinusParameters]
  have hvalue := familyParameterValue_comp_differentiableAt hH p connectionGMinusParameters
    (connectionGMinusParameters_mem hp) hSDiff (1 / 2 : ℂ) (by norm_num)
  norm_num [gaussGMinus, connectionGMinusParameters] at ⊢
  exact hvalue

/-- The second one-basis value at `1/2` varies holomorphically with the parameters. -/
theorem gaussGPlus_midpoint_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => gaussGPlus H q.1 q.2.1 q.2.2 (1 / 2 : ℂ)) p := by
  have hSDiff : DifferentiableAt ℂ connectionGPlusParameters p := by
    fun_prop [connectionGPlusParameters]
  have hvalue := familyParameterValue_comp_differentiableAt hH p connectionGPlusParameters
    (connectionGPlusParameters_mem hp) hSDiff (1 / 2 : ℂ) (by norm_num)
  have hpower : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1)) p := by
    have hExponent : DifferentiableAt ℂ
        (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) p := by fun_prop
    exact hExponent.const_cpow (Or.inl (by norm_num))
  have hvalue' : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ =>
        H (q.2.2 - q.2.1) (q.2.2 - q.1) (1 + q.2.2 - q.1 - q.2.1) (1 / 2 : ℂ)) p := by
    simpa [connectionGPlusParameters] using hvalue
  have hprod := hpower.mul hvalue'
  norm_num [gaussGPlus] at ⊢
  exact hprod

end DOZZ.Proofs
