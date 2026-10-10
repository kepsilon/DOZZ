/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationDiagonalConnection
public import DOZZ.Hypergeom.ClassificationDiagonalExtensionForward
public import DOZZ.Hypergeom.ClassificationPositiveHalfPlaneBases
public import DOZZ.Hypergeom.ClassificationLocalDiagonalTensor
public import DOZZ.Hypergeom.BasisSpanning
public import DOZZ.Hypergeom.ODE.FamilySystem

/-! Piecewise single-valued extension of the classified diagonal norm square. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter
open scoped Topology

noncomputable def gaussDiagonalOneCoefficient₁ (a b c α δ : ℝ) : ℝ :=
  α * (Real.Gamma c * Real.Gamma (c - a - b) *
      (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹) ^ 2 +
    δ * (Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
      (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹) ^ 2

noncomputable def gaussDiagonalOneCoefficient₂ (a b c α δ : ℝ) : ℝ :=
  α * (Real.Gamma c * Real.Gamma (a + b - c) *
      (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹) ^ 2 +
    δ * (Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
      (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹) ^ 2

/-- The classified diagonal expression continued by the alternate basis on each branch cut. -/
noncomputable def gaussDiagonalExtensionCandidate
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c α δ : ℝ) (z : ℂ) : ℝ :=
  if z.re < 0 then
    α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
      δ * Complex.normSq (gaussNegativeCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ) z)
  else if 1 < z.re then
    gaussDiagonalOneCoefficient₁ a b c α δ *
        Complex.normSq (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
      gaussDiagonalOneCoefficient₂ a b c α δ *
        Complex.normSq (gaussPositiveCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ) z)
  else
    α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
      δ * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z)

private theorem gauss_real_parameter_nonint_to_complex
    (x : ℝ) (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    ∀ n : ℤ, (x : ℂ) ≠ (n : ℂ) := by
  intro n hn
  apply hx n
  exact_mod_cast hn

private theorem gauss_real_excess_nonint_to_complex
    (a b c : ℝ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ)) :
    ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
  intro n hn
  apply hδ n
  have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
  apply Complex.ofReal_injective
  push_cast at hn ⊢
  linear_combination hn

/-- On the principal cut plane the piecewise continuation is the original diagonal formula. -/
theorem gaussDiagonalExtensionCandidate_eq_cut_formula
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c α δ : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    ∀ z ∈ gaussCutPlane,
      gaussDiagonalExtensionCandidate H a b c α δ z =
        α * ‖gaussFMinus H a b c z‖ ^ 2 + δ * ‖gaussFPlus H a b c z‖ ^ 2 := by
  have hcC := gauss_real_parameter_nonint_to_complex c hc
  have hδC := gauss_real_excess_nonint_to_complex a b c hδ
  have hphaseZero : Complex.normSq (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      (1 - (c : ℂ)))) = 1 := gaussNegativeCrossingPhase_normSq_eq_one c
  have hphaseOne : Complex.normSq (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
      (1 - (1 + (a : ℂ) + (b : ℂ) - (c : ℂ))))) = 1 := by
    have hcast : ((1 + a + b - c : ℝ) : ℂ) =
        1 + (a : ℂ) + (b : ℂ) - (c : ℂ) := by push_cast; ring
    rw [← hcast]
    exact gaussNegativeCrossingPhase_normSq_eq_one (1 + a + b - c)
  have htransfer := gauss_diagonal_one_basis_of_constraint hH a b c α δ hc hδ hconstraint
  intro z hz
  by_cases hleft : z.re < 0
  · have him : z.im ≠ 0 := by
      change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
      rcases hz with him | ⟨hz0, _⟩
      · exact him
      · linarith
    have hsecondNorm :
        Complex.normSq (gaussNegativeCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ) z) =
          Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      by_cases himPos : 0 < z.im
      · rw [gaussNegativeCrossingSecond_eq_gaussFPlus_of_im_pos
          (a : ℂ) (b : ℂ) (c : ℂ) z himPos]
      · have himNeg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt himPos) him
        rw [gaussNegativeCrossingSecond_eq_phase_mul_gaussFPlus_of_im_neg
          (a : ℂ) (b : ℂ) (c : ℂ) z himNeg,
          Complex.normSq_mul, hphaseZero]
        ring
    simp [gaussDiagonalExtensionCandidate, hleft]
    rw [hsecondNorm]
    simp only [Complex.normSq_eq_norm_sq]
  · by_cases hright : 1 < z.re
    · have him : z.im ≠ 0 := by
        change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
        rcases hz with him | ⟨_, hz1⟩
        · exact him
        · linarith
      have hsecondNorm :
          Complex.normSq (gaussPositiveCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ) z) =
            Complex.normSq (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
        by_cases himNeg : z.im < 0
        · rw [gaussPositiveCrossingSecond_eq_gaussGPlus_of_im_neg
            (a : ℂ) (b : ℂ) (c : ℂ) z himNeg]
        · have himPos : 0 < z.im := lt_of_le_of_ne (le_of_not_gt himNeg) (Ne.symm him)
          rw [gaussPositiveCrossingSecond_eq_phase_mul_gaussGPlus_of_im_pos
            (a : ℂ) (b : ℂ) (c : ℂ) z himPos,
            Complex.normSq_mul, hphaseOne]
          ring
      have hT := htransfer z hz
      simp [gaussDiagonalExtensionCandidate, hleft, hright]
      rw [hsecondNorm]
      simpa [gaussDiagonalOneCoefficient₁, gaussDiagonalOneCoefficient₂,
        Complex.normSq_eq_norm_sq] using hT.symm
    · simp [gaussDiagonalExtensionCandidate, hleft, hright]
      simp only [Complex.normSq_eq_norm_sq]

private theorem gaussDiagonalPDE_eq_of_eqOn
    (a b c : ℝ) {U : Set ℂ} (hU : IsOpen U)
    {T S : ℂ → ℝ} (hT : ContDiffOn ℝ 2 T U) (hS : ContDiffOn ℝ 2 S U)
    (hEq : Set.EqOn T S U) {z : ℂ} (hz : z ∈ U) :
    (wirtingerZ (wirtingerZ (fun w => (T w : ℂ))) z +
        ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
          wirtingerZ (fun w => (T w : ℂ)) z -
        (a : ℂ) * b / (z * (1 - z)) * (T z : ℂ)) =
      (wirtingerZ (wirtingerZ (fun w => (S w : ℂ))) z +
        ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
          wirtingerZ (fun w => (S w : ℂ)) z -
        (a : ℂ) * b / (z * (1 - z)) * (S z : ℂ)) := by
  let FT : ℂ → ℂ := fun w => (T w : ℂ)
  let FS : ℂ → ℂ := fun w => (S w : ℂ)
  have hTAt : ContDiffAt ℝ 2 T z :=
    (hT z hz).contDiffAt (hU.mem_nhds hz)
  have hSAt : ContDiffAt ℝ 2 S z :=
    (hS z hz).contDiffAt (hU.mem_nhds hz)
  have hFTAt : ContDiffAt ℝ 2 FT z := by
    change ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ T) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hTAt
  have hFSAt : ContDiffAt ℝ 2 FS z := by
    change ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ S) z
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp z hSAt
  have hnear : FT =ᶠ[𝓝 z] FS := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrArg Complex.ofReal (hEq hw)
  have hfirst := wirtingerZ_congr_of_eventuallyEq
    (hFTAt.differentiableAt (by norm_num))
    (hFSAt.differentiableAt (by norm_num)) hnear
  have hFTfirstAt := differentiableAt_wirtingerZ_of_contDiffAt_two hFTAt
  have hFSfirstAt := differentiableAt_wirtingerZ_of_contDiffAt_two hFSAt
  have hfirstNear : (fun w => wirtingerZ FT w) =ᶠ[𝓝 z]
      (fun w => wirtingerZ FS w) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    have hFTAtW : ContDiffAt ℝ 2 FT w := by
      change ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ T) w
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp w
        ((hT w hw).contDiffAt (hU.mem_nhds hw))
    have hFSAtW : ContDiffAt ℝ 2 FS w := by
      change ContDiffAt ℝ 2 (Complex.ofRealCLM ∘ S) w
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp w
        ((hS w hw).contDiffAt (hU.mem_nhds hw))
    have hnearW : FT =ᶠ[𝓝 w] FS := by
      filter_upwards [hU.mem_nhds hw] with v hv
      exact congrArg Complex.ofReal (hEq hv)
    exact wirtingerZ_congr_of_eventuallyEq
      (hFTAtW.differentiableAt (by norm_num))
      (hFSAtW.differentiableAt (by norm_num)) hnearW
  have hsecond := wirtingerZ_congr_of_eventuallyEq hFTfirstAt hFSfirstAt hfirstNear
  change wirtingerZ (fun w => wirtingerZ FT w) z +
      ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
        wirtingerZ FT z - (a : ℂ) * b / (z * (1 - z)) * FT z =
    wirtingerZ (fun w => wirtingerZ FS w) z +
      ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
        wirtingerZ FS z - (a : ℂ) * b / (z * (1 - z)) * FS z
  rw [hsecond, hfirst, show FT z = FS z from congrArg Complex.ofReal (hEq hz)]

private theorem gaussNegativeHalfPlane_isOpen_extension :
    IsOpen gaussNegativeHalfPlane := by
  exact isOpen_Iio.preimage Complex.continuous_re

private theorem gaussPositiveHalfPlane_isOpen_extension :
    IsOpen gaussPositiveHalfPlane := by
  exact isOpen_Ioi.preimage Complex.continuous_re

private theorem gaussNegativeHalfPlane_subset_regularPlane :
    gaussNegativeHalfPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  constructor
  · intro h
    have hre : z.re = 0 := by simpa using congrArg Complex.re h
    change z.re < 0 at hz
    linarith
  · intro h
    have hre : z.re = 1 := by simpa using congrArg Complex.re h
    change z.re < 0 at hz
    linarith

private theorem gaussPositiveHalfPlane_subset_regularPlane :
    gaussPositiveHalfPlane ⊆ gaussRegularPlane := by
  intro z hz
  change z ≠ 0 ∧ z ≠ 1
  constructor
  · intro h
    have hre : z.re = 0 := by simpa using congrArg Complex.re h
    change 1 < z.re at hz
    linarith
  · intro h
    have hre : z.re = 1 := by simpa using congrArg Complex.re h
    change 1 < z.re at hz
    linarith

private theorem gaussFMinus_analyticOnNhd_left
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (gaussFMinus H a b c) gaussNegativeHalfPlane := by
  have hchar := hH a b c hc
  have hsource : AnalyticOnNhd ℂ (H a b c) gaussSlitPlane :=
    hchar.1.analyticOnNhd gaussSlitPlane_isOpen
  have hsub : gaussNegativeHalfPlane ⊆ gaussSlitPlane := by
    intro z hz
    change z.im ≠ 0 ∨ z.re < 1
    right
    change z.re < 0 at hz
    linarith
  change AnalyticOnNhd ℂ (H a b c) gaussNegativeHalfPlane
  exact hsource.mono hsub

private theorem gaussFMinus_holomorphicOperator_eq_zero_left
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    ∀ z ∈ gaussNegativeHalfPlane,
      gaussHolomorphicOperator a b c (gaussFMinus H a b c) z = 0 := by
  intro z hz
  have hsource := gauss_family_holomorphicOperator_eq_zero_on_slit hH a b c hc
  have hzslit : z ∈ gaussSlitPlane := by
    change z.im ≠ 0 ∨ z.re < 1
    right
    change z.re < 0 at hz
    linarith
  change gaussHolomorphicOperator a b c (H a b c) z = 0
  exact hsource z hzslit

private noncomputable def gaussNegativeExtensionTensor
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c α δ : ℝ) (z : ℂ) : ℝ :=
  α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
    δ * Complex.normSq (gaussNegativeCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ) z)

private noncomputable def gaussPositiveExtensionTensor
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c α δ : ℝ) (z : ℂ) : ℝ :=
  gaussDiagonalOneCoefficient₁ a b c α δ *
      Complex.normSq (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
    gaussDiagonalOneCoefficient₂ a b c α δ *
      Complex.normSq (gaussPositiveCrossingSecond H (a : ℂ) (b : ℂ) (c : ℂ) z)

private noncomputable def gaussZeroExtensionTensor
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c α δ : ℝ) (z : ℂ) : ℝ :=
  α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
    δ * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z)

private theorem gaussRegularPlane_point_in_cut_or_branch
    {z : ℂ} (hz : z ∈ gaussRegularPlane) (hleft : ¬ z.re < 0)
    (hright : ¬ 1 < z.re) : z ∈ gaussCutPlane := by
  change z ≠ 0 ∧ z ≠ 1 at hz
  change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1)
  by_cases him : z.im ≠ 0
  · exact Or.inl him
  · right
    have him0 : z.im = 0 := not_ne_iff.mp him
    have hre0 : z.re ≠ 0 := by
      intro hre
      apply hz.1
      apply Complex.ext <;> simp [hre, him0]
    have hre1 : z.re ≠ 1 := by
      intro hre
      apply hz.2
      apply Complex.ext <;> simp [hre, him0]
    constructor
    · exact lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hre0)
    · exact lt_of_le_of_ne (le_of_not_gt hright) hre1

/-- The piecewise continuation is C² on the entire regular plane. -/
theorem gaussDiagonalExtensionCandidate_contDiffOn
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c α δ : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    ContDiffOn ℝ 2 (gaussDiagonalExtensionCandidate H a b c α δ) gaussRegularPlane := by
  have hcC := gauss_real_parameter_nonint_to_complex c hc
  have hδC := gauss_real_excess_nonint_to_complex a b c hδ
  have hcNat : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n
    simpa using hcC (-(n : ℤ))
  have hNegF := gaussFMinus_analyticOnNhd_left hH (a : ℂ) (b : ℂ) (c : ℂ) hcNat
  have hNegS := gaussNegativeCrossingSecond_analyticOnNhd_left hH
    (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hNegFODE := gaussFMinus_holomorphicOperator_eq_zero_left hH
    (a : ℂ) (b : ℂ) (c : ℂ) hcNat
  have hNegSODE := gaussNegativeCrossingSecond_holomorphicOperator_eq_zero_left hH
    (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hNegTensor := realGaussDiagonalTensor_solutionOn a b c α δ
    gaussNegativeHalfPlane_isOpen_extension hNegF hNegS hNegFODE hNegSODE
  have hPosF := gaussGMinus_analyticOnNhd_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosS := gaussPositiveCrossingSecond_analyticOnNhd_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosFODE := gaussGMinus_holomorphicOperator_eq_zero_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosSODE := gaussPositiveCrossingSecond_holomorphicOperator_eq_zero_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosTensor := realGaussDiagonalTensor_solutionOn a b c
    (gaussDiagonalOneCoefficient₁ a b c α δ)
    (gaussDiagonalOneCoefficient₂ a b c α δ)
    gaussPositiveHalfPlane_isOpen_extension hPosF hPosS hPosFODE hPosSODE
  have hzero := gauss_local_basis_zero hH (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hZeroF := hzero.1.analyticOnNhd gaussCutPlane_isOpen
  have hZeroS := hzero.2.1.analyticOnNhd gaussCutPlane_isOpen
  have hZeroFODE : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) z = 0 :=
    fun z hz => (hzero.2.2.1 z hz).1
  have hZeroSODE : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) z = 0 :=
    fun z hz => (hzero.2.2.1 z hz).2.1
  have hZeroTensor := realGaussDiagonalTensor_solutionOn a b c α δ
    gaussCutPlane_isOpen hZeroF hZeroS hZeroFODE hZeroSODE
  intro z hz
  by_cases hleft : z.re < 0
  · have hEqOn : Set.EqOn (gaussDiagonalExtensionCandidate H a b c α δ)
      (gaussNegativeExtensionTensor H a b c α δ) gaussNegativeHalfPlane := by
      intro w hw
      change w.re < 0 at hw
      simp [gaussDiagonalExtensionCandidate, gaussNegativeExtensionTensor, hw]
    have hAt := (hNegTensor.1 z hleft).contDiffAt
      (gaussNegativeHalfPlane_isOpen_extension.mem_nhds hleft)
    have hNear : gaussDiagonalExtensionCandidate H a b c α δ =ᶠ[𝓝 z]
        gaussNegativeExtensionTensor H a b c α δ := by
      filter_upwards [gaussNegativeHalfPlane_isOpen_extension.mem_nhds hleft] with w hw
      exact hEqOn hw
    exact (hAt.congr_of_eventuallyEq hNear).contDiffWithinAt
  · by_cases hright : 1 < z.re
    · have hEqOn : Set.EqOn (gaussDiagonalExtensionCandidate H a b c α δ)
        (gaussPositiveExtensionTensor H a b c α δ) gaussPositiveHalfPlane := by
        intro w hw
        change 1 < w.re at hw
        have hnotleft : ¬ w.re < 0 := by linarith
        simp [gaussDiagonalExtensionCandidate, gaussPositiveExtensionTensor, hnotleft, hw]
      have hAt := (hPosTensor.1 z hright).contDiffAt
        (gaussPositiveHalfPlane_isOpen_extension.mem_nhds hright)
      have hNear : gaussDiagonalExtensionCandidate H a b c α δ =ᶠ[𝓝 z]
          gaussPositiveExtensionTensor H a b c α δ := by
        filter_upwards [gaussPositiveHalfPlane_isOpen_extension.mem_nhds hright] with w hw
        exact hEqOn hw
      exact (hAt.congr_of_eventuallyEq hNear).contDiffWithinAt
    · have hzCut := gaussRegularPlane_point_in_cut_or_branch hz hleft hright
      have hEqOn : Set.EqOn (gaussDiagonalExtensionCandidate H a b c α δ)
        (gaussZeroExtensionTensor H a b c α δ) gaussCutPlane := by
        intro w hw
        have heq := gaussDiagonalExtensionCandidate_eq_cut_formula
          hH a b c α δ hc hδ hconstraint w hw
        simpa [gaussZeroExtensionTensor, Complex.normSq_eq_norm_sq] using heq
      have hAt := (hZeroTensor.1 z hzCut).contDiffAt
        (gaussCutPlane_isOpen.mem_nhds hzCut)
      have hNear : gaussDiagonalExtensionCandidate H a b c α δ =ᶠ[𝓝 z]
          gaussZeroExtensionTensor H a b c α δ := by
        filter_upwards [gaussCutPlane_isOpen.mem_nhds hzCut] with w hw
        exact hEqOn hw
      exact (hAt.congr_of_eventuallyEq hNear).contDiffWithinAt

/-- The piecewise continuation is a single-valued real C² solution of the Gauss PDE. -/
theorem gaussDiagonalExtensionCandidate_isRealGaussSolution
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c α δ : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    IsRealGaussSolution a b c (gaussDiagonalExtensionCandidate H a b c α δ) := by
  have hC2 := gaussDiagonalExtensionCandidate_contDiffOn hH a b c α δ hc hδ hconstraint
  have hcC := gauss_real_parameter_nonint_to_complex c hc
  have hδC := gauss_real_excess_nonint_to_complex a b c hδ
  have hcNat : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n
    simpa using hcC (-(n : ℤ))
  have hNegF := gaussFMinus_analyticOnNhd_left hH (a : ℂ) (b : ℂ) (c : ℂ) hcNat
  have hNegS := gaussNegativeCrossingSecond_analyticOnNhd_left hH
    (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hNegFODE := gaussFMinus_holomorphicOperator_eq_zero_left hH
    (a : ℂ) (b : ℂ) (c : ℂ) hcNat
  have hNegSODE := gaussNegativeCrossingSecond_holomorphicOperator_eq_zero_left hH
    (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hNegTensor := realGaussDiagonalTensor_solutionOn a b c α δ
    gaussNegativeHalfPlane_isOpen_extension hNegF hNegS hNegFODE hNegSODE
  have hPosF := gaussGMinus_analyticOnNhd_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosS := gaussPositiveCrossingSecond_analyticOnNhd_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosFODE := gaussGMinus_holomorphicOperator_eq_zero_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosSODE := gaussPositiveCrossingSecond_holomorphicOperator_eq_zero_right hH
    (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hPosTensor := realGaussDiagonalTensor_solutionOn a b c
    (gaussDiagonalOneCoefficient₁ a b c α δ)
    (gaussDiagonalOneCoefficient₂ a b c α δ)
    gaussPositiveHalfPlane_isOpen_extension hPosF hPosS hPosFODE hPosSODE
  have hzero := gauss_local_basis_zero hH (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hZeroF := hzero.1.analyticOnNhd gaussCutPlane_isOpen
  have hZeroS := hzero.2.1.analyticOnNhd gaussCutPlane_isOpen
  have hZeroFODE : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) z = 0 :=
    fun z hz => (hzero.2.2.1 z hz).1
  have hZeroSODE : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator (a : ℂ) (b : ℂ) (c : ℂ)
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) z = 0 :=
    fun z hz => (hzero.2.2.1 z hz).2.1
  have hZeroTensor := realGaussDiagonalTensor_solutionOn a b c α δ
    gaussCutPlane_isOpen hZeroF hZeroS hZeroFODE hZeroSODE
  refine ⟨hC2, ?_⟩
  intro z hz
  by_cases hleft : z.re < 0
  · have hEqOn : Set.EqOn (gaussDiagonalExtensionCandidate H a b c α δ)
      (gaussNegativeExtensionTensor H a b c α δ) gaussNegativeHalfPlane := by
      intro w hw
      change w.re < 0 at hw
      simp [gaussDiagonalExtensionCandidate, gaussNegativeExtensionTensor, hw]
    have hCandOn : ContDiffOn ℝ 2
        (gaussDiagonalExtensionCandidate H a b c α δ) gaussNegativeHalfPlane :=
      hC2.mono gaussNegativeHalfPlane_subset_regularPlane
    have hRes := gaussDiagonalPDE_eq_of_eqOn a b c
      gaussNegativeHalfPlane_isOpen_extension hCandOn hNegTensor.1 hEqOn hleft
    calc
      _ = (wirtingerZ (wirtingerZ (fun w =>
          (gaussNegativeExtensionTensor H a b c α δ w : ℂ))) z +
          ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
            wirtingerZ (fun w =>
              (gaussNegativeExtensionTensor H a b c α δ w : ℂ)) z -
          (a : ℂ) * b / (z * (1 - z)) *
            (gaussNegativeExtensionTensor H a b c α δ z : ℂ)) := hRes
      _ = 0 := hNegTensor.2 z hleft (gaussNegativeHalfPlane_subset_regularPlane hleft)
  · by_cases hright : 1 < z.re
    · have hEqOn : Set.EqOn (gaussDiagonalExtensionCandidate H a b c α δ)
        (gaussPositiveExtensionTensor H a b c α δ) gaussPositiveHalfPlane := by
        intro w hw
        change 1 < w.re at hw
        have hnotleft : ¬ w.re < 0 := by linarith
        simp [gaussDiagonalExtensionCandidate, gaussPositiveExtensionTensor, hnotleft, hw]
      have hCandOn : ContDiffOn ℝ 2
          (gaussDiagonalExtensionCandidate H a b c α δ) gaussPositiveHalfPlane :=
        hC2.mono gaussPositiveHalfPlane_subset_regularPlane
      have hRes := gaussDiagonalPDE_eq_of_eqOn a b c
        gaussPositiveHalfPlane_isOpen_extension hCandOn hPosTensor.1 hEqOn hright
      calc
        _ = (wirtingerZ (wirtingerZ (fun w =>
            (gaussPositiveExtensionTensor H a b c α δ w : ℂ))) z +
            ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
              wirtingerZ (fun w =>
                (gaussPositiveExtensionTensor H a b c α δ w : ℂ)) z -
            (a : ℂ) * b / (z * (1 - z)) *
              (gaussPositiveExtensionTensor H a b c α δ z : ℂ)) := hRes
        _ = 0 := hPosTensor.2 z hright (gaussPositiveHalfPlane_subset_regularPlane hright)
    · have hzCut := gaussRegularPlane_point_in_cut_or_branch hz hleft hright
      have hEqOn : Set.EqOn (gaussDiagonalExtensionCandidate H a b c α δ)
        (gaussZeroExtensionTensor H a b c α δ) gaussCutPlane := by
        intro w hw
        have heq := gaussDiagonalExtensionCandidate_eq_cut_formula
          hH a b c α δ hc hδ hconstraint w hw
        simpa [gaussZeroExtensionTensor, Complex.normSq_eq_norm_sq] using heq
      have hCandOn : ContDiffOn ℝ 2
          (gaussDiagonalExtensionCandidate H a b c α δ) gaussCutPlane :=
        hC2.mono gaussCutPlane_subset_regularPlane
      have hRes := gaussDiagonalPDE_eq_of_eqOn a b c
        gaussCutPlane_isOpen hCandOn hZeroTensor.1 hEqOn hzCut
      calc
        _ = (wirtingerZ (wirtingerZ (fun w =>
            (gaussZeroExtensionTensor H a b c α δ w : ℂ))) z +
            ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
              wirtingerZ (fun w =>
                (gaussZeroExtensionTensor H a b c α δ w : ℂ)) z -
            (a : ℂ) * b / (z * (1 - z)) *
              (gaussZeroExtensionTensor H a b c α δ z : ℂ)) := hRes
        _ = 0 := hZeroTensor.2 z hzCut
          (gaussCutPlane_subset_regularPlane hzCut)

/-- Every pair on the undivided coefficient line has a global real C² PDE extension, and any
such extension must lie on that line. -/
theorem gauss_diagonal_extension_iff
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ)) (coeff₁ coeff₂ : ℝ) :
    (∃ T : ℂ → ℝ, IsRealGaussSolution a b c T ∧
      ∀ z ∈ gaussCutPlane,
        T z = coeff₁ * ‖gaussFMinus H a b c z‖ ^ 2 +
          coeff₂ * ‖gaussFPlus H a b c z‖ ^ 2) ↔
      gaussK₁ a b c * coeff₁ + gaussK₂ a b c * coeff₂ = 0 := by
  constructor
  · exact gauss_diagonal_extension_iff_forward hH a b c hc hδ coeff₁ coeff₂
  · intro hconstraint
    refine ⟨gaussDiagonalExtensionCandidate H a b c coeff₁ coeff₂,
      gaussDiagonalExtensionCandidate_isRealGaussSolution
        hH a b c coeff₁ coeff₂ hc hδ hconstraint, ?_⟩
    exact gaussDiagonalExtensionCandidate_eq_cut_formula
      hH a b c coeff₁ coeff₂ hc hδ hconstraint

end DOZZ.Proofs
