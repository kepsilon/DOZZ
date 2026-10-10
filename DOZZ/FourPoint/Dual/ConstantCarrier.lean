/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.FullCopiedLimit
import Mathlib.Tactic
/-! Actual lateral decoupling is negligible at the prescribed dual fusion exponent. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Almost-sure equality of the lateral plane carriers preserves the full copied observable. -/
theorem dual_copied_inverse_moment_congr
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Xc : Ω → ℂ → ℝ → ℝ) (hAr : AEMeasurable (originRadialPath Xc) P)
    (N₁ N₂ : Ω → Measure ℂ) (he : N₁ =ᵐ[P] N₂)
    (γ α₁ α₂ α₃ q : ℝ) (z : ℂ) (s r : ℝ) :
    dualCopiedSeparatedInverseMoment P Xc N₁ γ α₁ α₂ α₃ q z s r =
      dualCopiedSeparatedInverseMoment P Xc N₂ γ α₁ α₂ α₃ q z s r := by
  let _ : IsProbabilityMeasure (P.map (originRadialPath Xc)) :=
    (Measure.isProbabilityMeasure_map_iff hAr).mpr inferInstance
  have hpair : ∀ᵐ v : Ω × Ω ∂P.prod P, N₁ v.1 = N₂ v.1 ∧ N₁ v.2 = N₂ v.2 := by
    filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae he,
      measurePreserving_snd.quasiMeasurePreserving.ae he] with v h₁ h₂
    exact ⟨h₁,h₂⟩
  have hwhole := (measurePreserving_snd (μ := P.map (originRadialPath Xc))
    (ν := P.prod P)).quasiMeasurePreserving.ae hpair
  unfold dualCopiedSeparatedInverseMoment
  apply lintegral_congr_ae
  filter_upwards [hwhole] with v hv
  rw [hv.1,hv.2]

/-- The supplied chaos admits independent lateral copies whose actual signed separated-mass
error is little-o at every exponent below `ξ`. Their radial removal and independence are
proved on the same eventual family of source carriers. -/
theorem dual_full_copied_constant_carrier
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun v : Ω × (ℂ × ℝ) => Xc v.1 v.2.1 v.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun v : ℂ × ℝ => Xc ω v.1 v.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q h ξ κ : ℝ) (hq : 0 < q)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ*α₁ < 4) (hslack : κ < (1-ξ)*(4-γ*α₁)) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hκ : κ < ξ) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      Tendsto (fun z : ℂ =>
        ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P).toReal-
         (dualCopiedSeparatedInverseMoment P Xc N γ α₁ α₂ α₃ q z
          (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal)/‖z‖^κ)
        (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hNm, hi, hfin, heq, _, _⟩ := reflected_copied_radial_plane_observable
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  obtain ⟨Nz, hNz, ht⟩ := dual_full_copied_inverse_littleO P X Xc hX hc hm hcont
    γ hγ hγ₂ M hM α₁ α₂ α₃ q h ξ κ hq hα₁ hα₂ hα₃ hβ hslack hξ hξ1 hκ
  refine ⟨N, hNm, hi, hfin, heq, ?_⟩
  have hAr := originRadialPath_aemeasurable P X Xc hc hcont
  apply ht.congr'
  filter_upwards [hNz] with z hz
  have he := dual_copied_inverse_moment_congr P Xc hAr (Nz z) N
    (hz.2.2.2.trans heq.symm) γ α₁ α₂ α₃ q z (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))
  rw [he]

end DOZZ.Proofs
