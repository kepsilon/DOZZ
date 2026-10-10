/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceInnerAsymptotic
public import DOZZ.FourPoint.Reflected.SourceLateralWitness
public import DOZZ.FourPoint.Reflected.Normalization
/-! The reflected inner limit `DOZZ.gammaHalf_reflected_inner_limit` follows from the actual source
Williams squeeze. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

theorem gammaHalf_reflected_inner_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hreflect : Q γ - α₁ < γ / 2)
    (hnear : γ * (Q γ - α₁) < min 1 ξ)
    (hfreeze : γ * (Q γ - α₁) <
      (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
        let κ := γ * (Q γ - α₁)
        ∃ r : ℂ → ℂ,
          (∀ z,
            (((gammaHalfMoment P M γ α₁ α₂ α₃ p z -
                gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ) : ℝ) : ℂ) =
              ((((1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ *
                  reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ : ℝ) : ℂ) *
                ((‖z‖ ^ κ : ℝ) : ℂ)) + r z)) ∧
            IsComplexLittleOAtZero κ r := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨Xc,B,hc,hm,hcont,hSource,hL,hB⟩ := reflected_regular_source_reflection_family
    P X hX γ hγ hγ₂ M hM
  let Z := fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)
  have hData : IsReflectionData P γ α₁ (B α₁) Z := hB α₁ hα₁
  obtain ⟨N,hN,hi,hfin,heq,hNa,hwhole⟩ := reflected_copied_radial_plane_observable
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  let B₀ := P.map (fun ω => radialPositiveHalf (originRadialPath Xc ω))
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hB₀ : IsBrownianReal (fun t p => p t) B₀ := radialPositiveHalf_map_isBrownian
    P (originRadialPath Xc) hA (originRadialPath_isBrownian P X Xc hX hc hcont).1
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  let κ := γ*(Q γ-α₁)
  let a := 2*(Q γ-α₁)/γ
  let C := 1/2*μ^p*γ*(Real.Gamma p)⁻¹*reflectionR P γ μ α₁ (B α₁) Z*
    structureConstant P M γ μ (2*Q γ-α₁-γ/2) α₂ α₃
  have ht := reflected_source_inner_increment_tendsto P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    N hN hi heq hfin hwhole hNa α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ hreflect hs hξ hξ₂
    (hnear.trans_le (min_le_right 1 ξ)) hfreeze (B α₁) hL hData B₀ hB₀
  have hcoef : (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
      (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃^(-(p+a)) ∂P).toReal*
        reflectionBarR P γ α₁ (B α₁) Z = C := by
    calc
      _ = (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        reflectionBarR P γ α₁ (B α₁) Z*
          (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃^(-(p+a)) ∂P).toReal := by ring
      _ = C := reflected_inner_coefficient_eq P M (B α₁) Z γ μ α₁ α₂ α₃ hγ hμ hs
  have hLimit : Tendsto (fun z : ℂ =>
      (gammaHalfMoment P M γ α₁ α₂ α₃ p z-gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ)/‖z‖^κ)
      (𝓝[≠] 0) (𝓝 C) := by
    rw [← hcoef]
    exact ht
  let rReal := fun z : ℂ => gammaHalfMoment P M γ α₁ α₂ α₃ p z-
    gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ-C*‖z‖^κ
  have hrem : Tendsto (fun z : ℂ => rReal z/‖z‖^κ) (𝓝[≠] 0) (𝓝 0) := by
    have hs := hLimit.sub (tendsto_const_nhds (x := C))
    have hs0 : Tendsto (fun z : ℂ =>
        (gammaHalfMoment P M γ α₁ α₂ α₃ p z-gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ)/‖z‖^κ-C)
        (𝓝[≠] 0) (𝓝 0) := by simpa only [sub_self] using hs
    apply hs0.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hn : ‖z‖^κ ≠ 0 := (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) κ).ne'
    dsimp only [rReal]
    simp only [sub_div,mul_div_cancel_right₀ C hn]
  refine ⟨B,Z,hSource,hData,fun z => (rReal z : ℂ),?_,?_⟩
  · intro z
    dsimp only [rReal,C]
    simp only [Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  · exact (isComplexLittleOAtZero_ofReal_iff κ rReal).mpr hrem

end DOZZ.Proofs
