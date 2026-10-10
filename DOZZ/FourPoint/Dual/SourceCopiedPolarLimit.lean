/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.SourcePolarLimit
public import DOZZ.FourPoint.Dual.SourceCopiedPolarExpectation
public import DOZZ.FourPoint.Dual.FullPathCarrier
import Mathlib.Tactic

/-! # The copied exterior/path polar increment limit

The full-path joint law transports the exact source polar expectation to the copied carrier.
Its leading coefficient retains the supplied reflection witness and the fixed radial buffer.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Exact copied-carrier transport of the proved source polar increment limit. -/
theorem dual_source_copied_polar_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (hlaw : ∀ β₁ β₂ β₃ ξ' : ℝ, ∀ z : ℂ, ‖z‖ < ‖z‖^(1-ξ') →
      P.map (fun ω => (originRadialPath Xc ω,dualOuterMass γ β₁ β₂ β₃ (M ω) z ξ')) =
        (P.prod P).map (fun ω : Ω × Ω => (originRadialPath Xc ω.1,
          ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ')),
            ENNReal.ofReal (dualFusionKernel γ β₁ β₂ β₃ z x)*
              ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2)))
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+2/γ < α₁+α₂+α₃)
    (hshifted : 2*Q γ-α₁-2/γ < Q γ)
    (hslack : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (hiZ : IndepFun (originRadialPath Xc) Z P) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
    let T := fun z : ℂ => Real.toNNReal (-Real.log ‖z‖+h)
    let A := originRadialPath Xc
    let O := fun z (v : Ω × Ω) => ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ (A v.1) x) ∂N v.2
    let D := fun z : ℂ => ∫ v : (Ω × Ω) × Ω,
      (((O z v.1).toReal+dualPathRadialScale γ ν h z (A v.1.1)*
        (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
          (brownianShiftPath (T z) (radialPositiveHalf (A v.1.1)) (Real.toNNReal t)-ν*t))) else 0)
            ∂(Z v.2).map (fun s => s-(T z : ℝ))).toReal)^(-p)-(O z v.1).toReal^(-p))
          ∂(P.prod P).prod P
    Tendsto (fun z => D z/‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^a ∂P).toReal)) := by
  have ht := dual_source_restarted_polar_increment_tendsto P X hX γ hγ hγ₂ M hM
    Xc hc hm hcont α₁ α₂ α₃ ξ h hα₁ hreflect hα₂ hα₃ hh hs hshifted hslack
    hξ hξ1 B Z hData hiZ
  apply ht.congr'
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 ‖(0 : ℂ)‖) :=
    (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
    hn.eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))] with z hz0 hz
  have hstrict : ‖z‖ < ‖z‖^(1-ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt
      (norm_pos_iff.mpr hz0) hz (by linarith only [hξ] : 1-ξ < 1)
  have he := dual_source_copied_polar_increment_eq P X Xc hX hc hcont γ hγ hγ₂ M hM
    N hNm hfin Z hData.2.1 α₁ α₂ α₃ ξ h
    ((α₁+α₂+α₃-2/γ-2*Q γ)/γ) z (Real.toNNReal (-Real.log ‖z‖+h))
    (hlaw α₁ α₂ α₃ ξ z hstrict)
  exact congrArg (fun t : ℝ => t/‖z‖^((4/γ)*(Q γ-α₁))) he

end DOZZ.Proofs
