/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Observable
public import DOZZ.FourPoint.Dual.PhysicalFusionCoefficient
public import DOZZ.Statements.FourPoint.FourPointTZeroEqStructureConstant
import DOZZ.FourPoint.Reflected.Normalization
import Mathlib.Tactic

/-! # Dual fusion normalization and classification assembly

The actual normalized inverse-moment limit is the explicit stochastic input. The exact
zero-mode and reflection normalizations give the full complex asymptotic with the same
witness, and its positive-ray specialization is fed to the diagonal classification.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

-- The literal interface retains source premises used by the stochastic proof of its normalized
-- limit. Several are redundant once that limit is given.
set_option linter.unusedVariables false in
/-- From the literal full inverse-moment limit to both dual fusion conclusions. -/
theorem dual_full_fusion_of_normalized_inverse_limit {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ η ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η) (hη₂ : η < γ / 2) (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hαlo : Q γ - η < α₁) (hαhi : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hslack₁ : (4 / γ) * (Q γ - α₁) < ξ)
    (hslack₂ : (4 / γ) * (Q γ - α₁) <
      (1 - ξ) * (4 - γ * α₁ - 2 * γ * η))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ (B α₁) Z)
    (hLimit :
      let ν := Q γ-α₁
      let a := 2*ν/γ
      let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
      Tendsto (fun z : ℂ =>
        ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-p) ∂P).toReal-
          (∫⁻ ω, coulombMass γ (M ω) ![-2/γ,α₁,α₂] ![0,0,1] α₃^(-p) ∂P).toReal)/
            ‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
        (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
          (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃^(-(p+a)) ∂P).toReal*
          (∫⁻ ω, twoSidedReflectionMass γ (B α₁) Z ω^a ∂P).toReal))) :
let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
let c := gaussParameterC γ (2 / γ) α₁
let κ := (4 / γ) * (Q γ - α₁)
(∃ r : ℂ → ℝ,
  (∀ z, fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
    structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ +
      reflectionR P γ μ α₁ (B α₁) Z *
        structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
          (‖z‖ ^ κ : ℝ) + r z) ∧
    Tendsto (fun z => r z / ‖z‖ ^ κ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0)) ∧
  (∀ z ∈ gaussCutPlane,
    fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
          ‖gaussFMinus H a b c z‖ ^ 2 +
        reflectionR P γ μ α₁ (B α₁) Z *
          structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ *
            ‖gaussFPlus H a b c z‖ ^ 2) := by
  let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
  let a := 2*(Q γ-α₁)/γ
  let κ := (4/γ)*(Q γ-α₁)
  let N := 2*μ^(-p)/γ*Real.Gamma p
  let C₀ := structureConstant P M γ μ (α₁-2/γ) α₂ α₃
  let D := reflectionR P γ μ α₁ (B α₁) Z *
    structureConstant P M γ μ (2*Q γ-α₁-2/γ) α₂ α₃
  let E := fun z : ℂ => (∫⁻ ω,
    (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-p) ∂P).toReal
  let E₀ := (∫⁻ ω, coulombMass γ (M ω) ![-2/γ,α₁,α₂] ![0,0,1] α₃^(-p) ∂P).toReal
  let L := (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
    (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃^(-(p+a)) ∂P).toReal*
    (∫⁻ ω, twoSidedReflectionMass γ (B α₁) Z ω^a ∂P).toReal
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hcoeff : N*L = D := by
    have hi := dual_inner_coefficient_eq P M (B α₁) Z γ μ α₁ α₂ α₃ hγ hμ hs
    have he : L = 1/2*μ^p*γ*(Real.Gamma p)⁻¹ *
        reflectionR P γ μ α₁ (B α₁) Z *
          structureConstant P M γ μ (2*Q γ-α₁-2/γ) α₂ α₃ := by
      dsimp only at hi
      simp only [reflectionBarR, reflectionExponent, ENNReal.rpow_eq_pow] at hi
      dsimp only [L, a, p]
      rw [← hi]
      ring
    rw [he]
    exact reflected_prefactor_cancel γ μ p _ _ hγ hμ hp
  have hT (z : ℂ) : fourPointT P M γ μ (-2/γ) α₁ α₂ α₃ z = N*E z :=
    fourPointT_eq_dualKernelMoment P X hX γ hγ hγ₂ M hM μ α₁ α₂ α₃ z
  have hzero : N*E₀ = C₀ := by
    have h2 : 0 < 2/γ := by positivity
    have hz := DOZZ.fourPointT_zero_eq_structureConstant P X M γ μ (2/γ) α₁ α₂ α₃
      hγ hγ₂ hμ (by linarith only [hαhi,h2])
      hα₂ hα₃ (by linarith only [hs]) hX hM
    change N*E₀ = structureConstant P M γ μ (α₁-2/γ) α₂ α₃
    rw [← hz]
    unfold fourPointT
    rw [show fourPointSExp γ (-(2/γ)) α₁ α₂ α₃ = p from
      by simpa only [neg_div] using fourPointSExp_dual γ α₁ α₂ α₃]
    simp only [N, E₀, ENNReal.rpow_eq_pow, neg_div]
  have hfull : Tendsto (fun z : ℂ =>
      (fourPointT P M γ μ (-2/γ) α₁ α₂ α₃ z-C₀)/‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 D) := by
    change Tendsto (fun z : ℂ => (E z-E₀)/‖z‖^κ) _ (𝓝 L) at hLimit
    have ht := hLimit.const_mul N
    rw [hcoeff] at ht
    apply ht.congr'
    filter_upwards [] with z
    rw [hT, ← hzero]
    ring
  let r : ℂ → ℝ := fun z => fourPointT P M γ μ (-2/γ) α₁ α₂ α₃ z-C₀-D*‖z‖^κ
  dsimp only
  constructor
  · refine ⟨r, ?_, ?_⟩
    · intro z
      dsimp only [r,C₀,D,κ]
      ring
    · have ht := hfull.sub_const D
      simp only [sub_self] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hn : ‖z‖^κ ≠ 0 := (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _).ne'
      change (fourPointT P M γ μ (-2/γ) α₁ α₂ α₃ z-C₀)/‖z‖^κ-D =
        ((fourPointT P M γ μ (-2/γ) α₁ α₂ α₃ z-C₀)-D*‖z‖^κ)/‖z‖^κ
      simp only [sub_div, mul_div_cancel_right₀ _ hn]
  · have hcast : Tendsto (fun t : ℝ => (t : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_ne_zero] using ne_of_gt ht
    have hray : Tendsto (fun t : ℝ =>
        (fourPointT P M γ μ (-(2/γ)) α₁ α₂ α₃ (t : ℂ)-C₀)/t^κ)
        (𝓝[>] (0 : ℝ)) (𝓝 D) := by
      apply (hfull.comp hcast).congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, neg_div]
    have hclass := dual_physical_fusion_coefficient hH P X M γ μ α₁ α₂ α₃ D
      hγ hγ₂ hμ hαhi hα₂ hα₃ hs (hslack₁.trans hξ₂) hX hM hray
    simpa only [neg_div] using hclass.2

end DOZZ.Proofs
