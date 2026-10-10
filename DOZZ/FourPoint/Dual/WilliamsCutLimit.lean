/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.FullMaximumLimit
public import DOZZ.FourPoint.Dual.FixedCutMaximumLimit
public import DOZZ.FourPoint.Dual.SourceWilliamsSandwich
public import DOZZ.FourPoint.Dual.CutSqueezeLimit
public import DOZZ.FourPoint.Dual.SourceParetoLimit
public import DOZZ.FourPoint.Dual.SourceParetoIncrement
public import DOZZ.FourPoint.Dual.SourceMaximumPareto
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.FourPoint.Reflected.RestartedWilliams
public import DOZZ.FourPoint.Dual.RadialFirstOrder
import Mathlib.Tactic
/-! The actual Williams random last cut has the full same-witness leading coefficient. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual independent Pareto maximum, full reflection mass, retained source mass and
radial restart scale give the required leading coefficient for each fixed radial buffer. -/
theorem dual_source_williams_cut_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+2/γ < α₁+α₂+α₃)
    (hshifted : 2*Q γ-α₁-2/γ < Q γ)
    (hslack : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
    let D := fun z : ℂ => ∫ v : Ω × (ℝ × Ω),
      (((dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        dual_radial_scale γ ν h Xc z v.1*(Real.exp (γ*v.2.1)*(twoSidedReflectionCutMass γ v.2.1 B Z v.2.2).toReal))^(-p)-
        (dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal ^(-p))
        ∂P.prod ((brownianMaximumReferenceLaw ν).prod P)
    Tendsto (fun z => D z/‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^a ∂P).toReal)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
  let κ := (4/γ)*ν
  let R := (brownianMaximumReferenceLaw ν).prod P
  let A := fun (z : ℂ) ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := dual_radial_scale γ ν h Xc
  let E := fun (J : ℝ × Ω → ℝ) (z : ℂ) => ∫ v : Ω × (ℝ × Ω),
    ((A z v.1+b z v.1*(Real.exp (γ*v.2.1)*J v.2))^(-p)-(A z v.1)^(-p)) ∂P.prod R
  let D := E (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal)
  let Dfull := E (fun q => (twoSidedReflectionMass γ B Z q.2).toReal)
  let Dc := fun c => E (fun q => (twoSidedReflectionCutMass γ c B Z q.2).toReal)
  let C := (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
    (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal
  let L := C*(∫⁻ ω, twoSidedReflectionMass γ B Z ω^a ∂P).toReal
  let Cc := fun c => C*(∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω^a ∂P).toReal
  let F := fun z : ℂ => ∫ ω, b z ω*(A z ω)^(-p-1) ∂P
  let J₁ := ∫ ω, (twoSidedReflectionMass γ B Z ω).toReal ∂P
  let Err := fun c z => p*Real.exp (γ*c)*F z*J₁
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have ha : 0 < a := div_pos (mul_pos (by norm_num) (sub_pos.mpr hα₁)) hγ
  have ha1 : a < 1 := by
    dsimp only [a, ν]
    rw [div_lt_one hγ]
    linarith only [hreflect]
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ, hγ₂]
  have hfull : Tendsto (fun z => Dfull z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 L) :=
    dual_source_full_maximum_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ h hα₁ hreflect hα₂ hα₃ hh hs hshifted hslack hξ hξ1 B Z hData
  have hcut (c : ℝ) : Tendsto (fun z => Dc c z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 (Cc c)) :=
    dual_source_cut_maximum_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ h c hα₁ hreflect hα₂ hα₃ hh hs hshifted hslack hξ hξ1 B Z hData
  have hCoeff : Tendsto Cc atTop (𝓝 L) :=
    (dual_reflection_cut_moment_tendsto P γ α₁ a hγ hγ₂ B Z hα₁ hData ha (ha1.trans h4)).const_mul C
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖(0 : ℂ)‖) :=
    (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun z => F z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht := dual_radial_first_order_littleO P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ (p+1) h κ hh hξ hξ1 (by linarith only [hp]) hslack
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))]
      with z hz0 hz
    have he := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
      ν h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1 (by linarith only [hp]) z hz0 hz.le).2
    simp only [Real.rpow_one, show -(p+1) = -p-1 by ring] at he
    change _ = F z/‖z‖^κ
    dsimp only [F, A, b]
    rw [he]
    simp_rw [dual_radial_scale_eq_restart γ ν h Xc z hz0]
    simp only [ν, show -(p+1) = -p-1 by ring]
  have hErr (c : ℝ) : Tendsto (fun z => Err c z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht := hF.const_mul (p*Real.exp (γ*c)*J₁)
    simp only [mul_zero] at ht
    apply ht.congr
    intro z
    dsimp only [Err]
    ring
  change Tendsto (fun z => D z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 L)
  apply dual_cut_squeeze_tendsto _ _ (fun z => Dfull z/‖z‖^κ)
    (fun c z => Dc c z/‖z‖^κ) (fun c z => Err c z/‖z‖^κ) Cc L hfull
    (fun c => by simpa only [add_zero] using (hcut c).add (hErr c)) hCoeff
  intro c
  filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))]
    with z hz0 hz
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hb := dual_source_williams_expectation_sandwich P X hX γ hγ hγ₂ M hM Xc hc
    α₁ α₂ α₃ ξ h p c hα₁ hα₂ hα₃ hh hp hξ hξ1 B Z hData z hz0 hz1 hz.le
  have hden : 0 ≤ ‖z‖^κ := Real.rpow_nonneg (norm_nonneg z) _
  refine ⟨div_le_div_of_nonneg_right hb.1 hden, ?_⟩
  have hu := div_le_div_of_nonneg_right hb.2 hden
  simpa only [add_div] using hu

end DOZZ.Proofs
