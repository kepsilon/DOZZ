/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ConnectionMidpointValues
public import DOZZ.Hypergeom.ODE.ParameterSpatialDerivative
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! Parameter regularity of the spatial derivatives in the midpoint connection matrix. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

private def midpointFPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1 - p.2.2 + 1, p.2.1 - p.2.2 + 1, 2 - p.2.2)

private def midpointGMinusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1, p.2.1, 1 + p.1 + p.2.1 - p.2.2)

private def midpointGPlusParameters (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.2.2 - p.2.1, p.2.2 - p.1, 1 + p.2.2 - p.1 - p.2.1)

private theorem midpointFPlusParameters_mem
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    midpointFPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 = (n : ℂ) + 2 := by
    dsimp [midpointFPlusParameters] at hn
    linear_combination -hn
  have hcast : p.2.2 = (((n : ℤ) + 2 : ℤ) : ℂ) := by
    calc
      p.2.2 = (n : ℂ) + 2 := hcastNat
      _ = (((n : ℤ) + 2 : ℤ) : ℂ) := by push_cast; ring
  exact (hp.1 ((n : ℤ) + 2)) hcast

private theorem midpointGMinusParameters_mem
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    midpointGMinusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := by
    dsimp [midpointGMinusParameters] at hn
    linear_combination -hn
  have hcast : p.2.2 - p.1 - p.2.1 = (((n : ℤ) + 1 : ℤ) : ℂ) := by
    calc
      p.2.2 - p.1 - p.2.1 = (n : ℂ) + 1 := hcastNat
      _ = (((n : ℤ) + 1 : ℤ) : ℂ) := by push_cast; ring
  exact (hp.2 ((n : ℤ) + 1)) hcast

private theorem midpointGPlusParameters_mem
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    midpointGPlusParameters p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have hcastNat : p.2.2 - p.1 - p.2.1 = -((n : ℂ) + 1) := by
    dsimp [midpointGPlusParameters] at hn
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

private theorem familyParameterDeriv_comp_differentiableAt
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (p : ℂ × ℂ × ℂ)
    (S : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ)
    (hS : S p ∈ gaussParameterPoleFreeDomain)
    (hSDiff : DifferentiableAt ℂ S p) (z : ℂ) (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => deriv (fun w => H (S q).1 (S q).2.1 (S q).2.2 w) z) p := by
  have hOn := IsGaussHypergeometricFamily.differentiableAt_params_deriv_unitDisk hH hS hz
  have hAt : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => deriv (fun w => H q.1 q.2.1 q.2.2 w) z) (S p) := hOn
  change DifferentiableAt ℂ
    ((fun q : ℂ × ℂ × ℂ => deriv (fun w => H q.1 q.2.1 q.2.2 w) z) ∘ S) p
  exact hAt.comp p hSDiff

private theorem gaussSlitPlane_isOpen_for_connection : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private theorem gaussFPlus_deriv_midpoint_formula
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (p : ℂ × ℂ × ℂ) (hp : p ∈ gaussConnectionParameterDomain) :
    deriv (gaussFPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
      (1 - p.2.2) * (1 / 2 : ℂ) ^ (-p.2.2) *
          H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2) (1 / 2 : ℂ) +
        (1 / 2 : ℂ) ^ (1 - p.2.2) *
          deriv (H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2)) (1 / 2 : ℂ) := by
  have hC := midpointFPlusParameters_mem hp
  have hCfree : ∀ n : ℕ, (2 - p.2.2) ≠ -(n : ℂ) := by
    intro n
    exact hC n
  have hchar := hH (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2)
    hCfree
  have hmid : (1 / 2 : ℂ) ∈ gaussSlitPlane := by norm_num [gaussSlitPlane]
  have hHAt : DifferentiableAt ℂ
      (H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2)) (1 / 2 : ℂ) :=
    hchar.1 (1 / 2 : ℂ) hmid |>.differentiableAt
      (gaussSlitPlane_isOpen_for_connection.mem_nhds hmid)
  have hpowAt : DifferentiableAt ℂ (fun z : ℂ => z ^ (1 - p.2.2)) (1 / 2 : ℂ) :=
    differentiableAt_id.cpow_const (Or.inl (by norm_num))
  have hmul := hpowAt.hasDerivAt.mul hHAt.hasDerivAt
  have hpowDeriv : deriv (fun z : ℂ => z ^ (1 - p.2.2)) (1 / 2 : ℂ) =
      (1 - p.2.2) * (1 / 2 : ℂ) ^ (-p.2.2) := by
    have hmidCut : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
    have h := Complex.deriv_cpow_const (c := 1 - p.2.2)
      (gaussCutPlane_subset_Complex_slitPlane hmidCut)
    simpa only [show (1 - p.2.2) - 1 = -p.2.2 by ring] using h
  change deriv ((fun z : ℂ => z ^ (1 - p.2.2)) *
    H (p.1 - p.2.2 + 1) (p.2.1 - p.2.2 + 1) (2 - p.2.2)) (1 / 2 : ℂ) = _
  rw [hmul.deriv, hpowDeriv]

private theorem connectionDomain_subset_poleFree {p : ℂ × ℂ × ℂ}
    (hp : p ∈ gaussConnectionParameterDomain) : p ∈ gaussParameterPoleFreeDomain := by
  intro n hn
  have h := hp.1 (-(n : ℤ))
  apply h
  simpa using hn

/-- The derivative of the first zero-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussFMinus_midpoint_deriv_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussFMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have hp0 := connectionDomain_subset_poleFree hp
  have hmap : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => q) p := by fun_prop
  have h := familyParameterDeriv_comp_differentiableAt hH p id hp0 hmap
    (1 / 2 : ℂ) (by norm_num)
  change DifferentiableAt ℂ
    (fun q : ℂ × ℂ × ℂ => deriv (fun z => H q.1 q.2.1 q.2.2 z) (1 / 2 : ℂ)) p
  exact h

/-- The derivative of the second zero-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussFPlus_midpoint_deriv_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have hSdiff : DifferentiableAt ℂ midpointFPlusParameters p := by
    fun_prop [midpointFPlusParameters]
  have hval := familyParameterValue_comp_differentiableAt hH p midpointFPlusParameters
    (midpointFPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hder := familyParameterDeriv_comp_differentiableAt hH p midpointFPlusParameters
    (midpointFPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hexp : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p := by fun_prop
  have hpow : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (1 - q.2.2)) p :=
    hexp.const_cpow (Or.inl (by norm_num))
  have hcoeff : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => 1 - q.2.2) p := by fun_prop
  have hpowNeg : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (-q.2.2)) p := by
    have hneg : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ => -q.2.2) p := by fun_prop
    exact hneg.const_cpow (Or.inl (by norm_num))
  have hcoefPow := hcoeff.mul hpowNeg
  have hfirst := hcoefPow.mul hval
  have hsecond := hpow.mul hder
  have hsum : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      (1 - q.2.2) * (1 / 2 : ℂ) ^ (-q.2.2) *
          H (q.1 - q.2.2 + 1) (q.2.1 - q.2.2 + 1) (2 - q.2.2) (1 / 2 : ℂ) +
        (1 / 2 : ℂ) ^ (1 - q.2.2) *
          deriv (H (q.1 - q.2.2 + 1) (q.2.1 - q.2.2 + 1) (2 - q.2.2)) (1 / 2 : ℂ)) p := by
    exact hfirst.add hsecond
  have hlocal : (fun q : ℂ × ℂ × ℂ =>
      deriv (gaussFPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) =ᶠ[𝓝 p]
      (fun q => (1 - q.2.2) * (1 / 2 : ℂ) ^ (-q.2.2) *
          H (q.1 - q.2.2 + 1) (q.2.1 - q.2.2 + 1) (2 - q.2.2) (1 / 2 : ℂ) +
        (1 / 2 : ℂ) ^ (1 - q.2.2) *
          deriv (H (q.1 - q.2.2 + 1) (q.2.1 - q.2.2 + 1) (2 - q.2.2)) (1 / 2 : ℂ)) := by
    filter_upwards [gaussConnectionParameterDomain_isOpen.mem_nhds hp] with q hq
    exact gaussFPlus_deriv_midpoint_formula hH q hq
  exact hsum.congr_of_eventuallyEq hlocal

private theorem gaussGMinus_deriv_midpoint_formula
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (p : ℂ × ℂ × ℂ) (hp : p ∈ gaussConnectionParameterDomain) :
    deriv (gaussGMinus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
      -deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 / 2 : ℂ) := by
  have hC := midpointGMinusParameters_mem hp
  have hCfree : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n
    exact hC n
  have hchar := hH p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) hCfree
  have hmid : (1 / 2 : ℂ) ∈ gaussSlitPlane := by norm_num [gaussSlitPlane]
  have hHAt : DifferentiableAt ℂ
      (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 / 2 : ℂ) :=
    hchar.1 (1 / 2 : ℂ) hmid |>.differentiableAt
      (gaussSlitPlane_isOpen_for_connection.mem_nhds hmid)
  have hHAt' : DifferentiableAt ℂ
      (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 - (1 / 2 : ℂ)) := by
    convert hHAt using 1; norm_num
  have hmap : HasDerivAt (fun z : ℂ => 1 - z) (-1) (1 / 2 : ℂ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub (1 : ℂ)
  have hcomp := hHAt'.hasDerivAt.comp (1 / 2 : ℂ) hmap
  have hcomp' : HasDerivAt
      (fun z : ℂ => H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (1 - z))
      (deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 - (1 / 2 : ℂ)) * -1)
      (1 / 2 : ℂ) := by
    simpa [Function.comp_def] using hcomp
  change deriv (fun z : ℂ => H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (1 - z))
    (1 / 2 : ℂ) = _
  calc
    deriv (fun z : ℂ => H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2) (1 - z))
        (1 / 2 : ℂ) =
      deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2))
        (1 - (1 / 2 : ℂ)) * -1 := hcomp'.deriv
    _ = -deriv (H p.1 p.2.1 (1 + p.1 + p.2.1 - p.2.2)) (1 / 2 : ℂ) := by norm_num

/-- The derivative of the first one-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussGMinus_midpoint_deriv_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have hSdiff : DifferentiableAt ℂ midpointGMinusParameters p := by
    fun_prop [midpointGMinusParameters]
  have hder := familyParameterDeriv_comp_differentiableAt hH p midpointGMinusParameters
    (midpointGMinusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hlocal : (fun q : ℂ × ℂ × ℂ =>
      deriv (gaussGMinus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) =ᶠ[𝓝 p]
      (fun q => -deriv (H q.1 q.2.1 (1 + q.1 + q.2.1 - q.2.2)) (1 / 2 : ℂ)) := by
    filter_upwards [gaussConnectionParameterDomain_isOpen.mem_nhds hp] with q hq
    exact gaussGMinus_deriv_midpoint_formula hH q hq
  have hright : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ =>
        -deriv (H q.1 q.2.1 (1 + q.1 + q.2.1 - q.2.2)) (1 / 2 : ℂ)) p := by
    have hmap : DifferentiableAt ℂ midpointGMinusParameters p := hSdiff
    have hcomp := familyParameterDeriv_comp_differentiableAt hH p midpointGMinusParameters
      (midpointGMinusParameters_mem hp) hmap (1 / 2 : ℂ) (by norm_num)
    simpa [midpointGMinusParameters] using hcomp.neg
  exact hright.congr_of_eventuallyEq hlocal

private theorem gaussGPlus_deriv_midpoint_formula
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (p : ℂ × ℂ × ℂ) (hp : p ∈ gaussConnectionParameterDomain) :
    deriv (gaussGPlus H p.1 p.2.1 p.2.2) (1 / 2 : ℂ) =
      -(p.2.2 - p.1 - p.2.1) * (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) *
          H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) (1 / 2 : ℂ) -
        (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1) *
          deriv (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1))
            (1 / 2 : ℂ) := by
  have hC := midpointGPlusParameters_mem hp
  have hCfree : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n
    exact hC n
  have hchar := hH (p.2.2 - p.2.1) (p.2.2 - p.1)
    (1 + p.2.2 - p.1 - p.2.1) hCfree
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hmidSlit := gaussCutPlane_subset_gaussSlitPlane hmid
  have hargSlit := gaussCutPlane_subset_Complex_slitPlane hmid
  have hHAt : DifferentiableAt ℂ
      (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1))
      (1 / 2 : ℂ) := hchar.1 (1 / 2 : ℂ) hmidSlit |>.differentiableAt
        (gaussSlitPlane_isOpen_for_connection.mem_nhds hmidSlit)
  have hHAt' : DifferentiableAt ℂ
      (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1))
      (1 - (1 / 2 : ℂ)) := by
    convert hHAt using 1; norm_num
  have hargAt : DifferentiableAt ℂ (fun z : ℂ => 1 - z) (1 / 2 : ℂ) := by fun_prop
  have hpowAt : DifferentiableAt ℂ
      (fun z : ℂ => (1 - z) ^ (p.2.2 - p.1 - p.2.1)) (1 / 2 : ℂ) :=
    hargAt.cpow_const (Or.inl (by norm_num))
  have hmap : HasDerivAt (fun z : ℂ => 1 - z) (-1) (1 / 2 : ℂ) := by
    simpa using (hasDerivAt_id (1 / 2 : ℂ)).const_sub (1 : ℂ)
  have hpowOneAt := differentiableAt_id.cpow_const
    (c := p.2.2 - p.1 - p.2.1) hargSlit
  have hpowOneAt' : DifferentiableAt ℂ
      (fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1)) (1 - (1 / 2 : ℂ)) := by
    convert hpowOneAt using 1 <;> norm_num
  have hpowComp := hpowOneAt'.hasDerivAt.comp (1 / 2 : ℂ) hmap
  have hpowDeriv : deriv (fun z : ℂ => (1 - z) ^ (p.2.2 - p.1 - p.2.1))
      (1 / 2 : ℂ) = -(p.2.2 - p.1 - p.2.1) *
        (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) := by
    have hargSlit' : (1 - (1 / 2 : ℂ)) ∈ Complex.slitPlane := by
      convert hargSlit using 1; norm_num
    have hpow' := Complex.deriv_cpow_const
      (c := p.2.2 - p.1 - p.2.1) hargSlit'
    have hpow'' : deriv (fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1))
        (1 - (1 / 2 : ℂ)) = (p.2.2 - p.1 - p.2.1) *
          (1 / 2 : ℂ) ^ (p.2.2 - p.1 - p.2.1 - 1) := by
      convert hpow' using 1; norm_num
    have hpowComp' : deriv ((fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1)) ∘
        (fun z : ℂ => 1 - z)) (1 / 2 : ℂ) =
        deriv (fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1))
          (1 - (1 / 2 : ℂ)) * -1 := by
      simpa using hpowComp.deriv
    change deriv ((fun w : ℂ => w ^ (p.2.2 - p.1 - p.2.1)) ∘
      (fun z : ℂ => 1 - z)) (1 / 2 : ℂ) = _
    rw [hpowComp', hpow'']
    ring
  have hcomp := hHAt'.hasDerivAt.comp (1 / 2 : ℂ) hmap
  have hmul := hpowAt.hasDerivAt.mul hcomp
  change deriv ((fun z : ℂ => (1 - z) ^ (p.2.2 - p.1 - p.2.1)) *
      (H (p.2.2 - p.2.1) (p.2.2 - p.1) (1 + p.2.2 - p.1 - p.2.1) ∘
        fun z : ℂ => 1 - z)) (1 / 2 : ℂ) = _
  rw [hmul.deriv, hpowDeriv]
  norm_num [Function.comp_def]
  ring

/-- The derivative of the second one-basis function at the midpoint varies holomorphically in
the connection parameters. -/
theorem gaussGPlus_midpoint_deriv_differentiableAt_params
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain) :
    DifferentiableAt ℂ
      (fun q => deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) p := by
  have hSdiff : DifferentiableAt ℂ midpointGPlusParameters p := by
    fun_prop [midpointGPlusParameters]
  have hval := familyParameterValue_comp_differentiableAt hH p midpointGPlusParameters
    (midpointGPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hder := familyParameterDeriv_comp_differentiableAt hH p midpointGPlusParameters
    (midpointGPlusParameters_mem hp) hSdiff (1 / 2 : ℂ) (by norm_num)
  have hdelta : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1) p := by fun_prop
  have hpow : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1)) p :=
    hdelta.const_cpow (Or.inl (by norm_num))
  have hdeltaSub : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => q.2.2 - q.1 - q.2.1 - 1) p := by fun_prop
  have hpowSub : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1 - 1)) p :=
    hdeltaSub.const_cpow (Or.inl (by norm_num))
  have hcoeff : DifferentiableAt ℂ
      (fun q : ℂ × ℂ × ℂ => -(q.2.2 - q.1 - q.2.1)) p := by fun_prop
  have hfirst : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      -(q.2.2 - q.1 - q.2.1) * (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1 - 1) *
        H (q.2.2 - q.2.1) (q.2.2 - q.1) (1 + q.2.2 - q.1 - q.2.1) (1 / 2 : ℂ)) p :=
    (hcoeff.mul hpowSub).mul hval
  have hsecond : DifferentiableAt ℂ (fun q : ℂ × ℂ × ℂ =>
      (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1) *
        deriv (H (q.2.2 - q.2.1) (q.2.2 - q.1)
          (1 + q.2.2 - q.1 - q.2.1)) (1 / 2 : ℂ)) p := hpow.mul hder
  have hsum := hfirst.sub hsecond
  have hlocal : (fun q : ℂ × ℂ × ℂ =>
      deriv (gaussGPlus H q.1 q.2.1 q.2.2) (1 / 2 : ℂ)) =ᶠ[𝓝 p]
      (fun q => -(q.2.2 - q.1 - q.2.1) *
          (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1 - 1) *
          H (q.2.2 - q.2.1) (q.2.2 - q.1) (1 + q.2.2 - q.1 - q.2.1) (1 / 2 : ℂ) -
        (1 / 2 : ℂ) ^ (q.2.2 - q.1 - q.2.1) *
          deriv (H (q.2.2 - q.2.1) (q.2.2 - q.1)
            (1 + q.2.2 - q.1 - q.2.1)) (1 / 2 : ℂ)) := by
    filter_upwards [gaussConnectionParameterDomain_isOpen.mem_nhds hp] with q hq
    exact gaussGPlus_deriv_midpoint_formula hH q hq
  exact hsum.congr_of_eventuallyEq hlocal

end DOZZ.Proofs
