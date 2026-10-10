/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceCopiedError
public import DOZZ.FourPoint.Reflected.SourceWilliamsKernelSqueeze
public import DOZZ.FourPoint.Reflected.SourceWilliamsLimit
public import DOZZ.FourPoint.Reflected.OrderedKernelSqueeze
public import DOZZ.FourPoint.Reflected.KernelCoefficientLimits
/-! The literal source reflected increment follows by the ordered Williams/kernel squeeze. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_inner_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (hwhole : ∀ (f : ℂ → ℝ≥0∞), Measurable f →
      ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
      (∫⁻ ω, G (originRadialPath Xc ω, ∫⁻ x in ({0} : Set ℂ)ᶜ, f x ∂M ω) ∂P) =
      ∫⁻ ω, G (originRadialPath Xc ω.1, ∫⁻ x in ({0} : Set ℂ)ᶜ,
        f x*ENNReal.ofReal (reflected_global_reinsertionWeight γ
          (originRadialPath Xc ω.1) x) ∂N ω.2) ∂P.prod P)
    (hNa : ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
      (fun ω => (N ω).restrict (originLateralChart ρ)))
    (α₁ α₂ α₃ ξ : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hreflect : Q γ-α₁ < γ/2) (hs : 2*Q γ+γ/2 < α₁+α₂+α₃)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hnear : γ*(Q γ-α₁) < ξ)
    (hfreeze : γ*(Q γ-α₁) < (1-ξ)*(γ*(Q γ-α₁)+(α₁+γ/2-Q γ)^2/2))
    (B : Ω → BrownianPath × BrownianPath)
    (hL : IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (hData : IsReflectionData P γ α₁ B (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (B₀ : Measure BrownianPath) [SFinite B₀] (hB₀ : IsBrownianReal (fun t p => p t) B₀) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
    Tendsto (fun z : ℂ =>
      (gammaHalfMoment P M γ α₁ α₂ α₃ p z-gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ)/‖z‖^(γ*ν))
      (𝓝[≠] 0) (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃^(-(p+a)) ∂P).toReal*
          reflectionBarR P γ α₁ B (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))) := by
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let κ := γ*ν
  let Z := fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)
  let L := (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
    (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃^(-(p+a)) ∂P).toReal*reflectionBarR P γ α₁ B Z
  let W := fun (h : ℝ) (z : ℂ) => ∫ v : Ω × (ℝ × Ω),
    ((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
      reflected_radial_scale γ ν h Xc z v.1*Real.exp (γ*v.2.1)*
        (twoSidedReflectionCutMass γ v.2.1 B Z v.2.2).toReal)^(-p)-
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)
        ∂P.prod ((brownianMaximumReferenceLaw ν).prod P)
  let E := fun (h : ℝ) (z : ℂ) => gammaHalfMoment P M γ α₁ α₂ α₃ p z-
    (reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z
      (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ)) p).toReal
  let Chi := fun (h : ℝ) (z : ℂ) => max 1 ((1+Real.exp (-h))^(γ^2/2)*
    (1-Real.exp (-h)*‖z‖)⁻¹^|γ*α₂|)
  let Clo := fun (h : ℝ) (z : ℂ) => min 1 ((1-Real.exp (-h))^(γ^2/2)*
    (1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α₂|))
  let f := fun z : ℂ => (gammaHalfMoment P M γ α₁ α₂ α₃ p z-
    gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ)/‖z‖^κ
  let g := fun h z => Chi h z*(W h z/‖z‖^κ)+E h z/‖z‖^κ
  let k := fun h z => Clo h z*(W h z/‖z‖^κ)+E h z/‖z‖^κ
  let Llo := fun h : ℝ => max 1 ((1+Real.exp (-h))^(γ^2/2))*L
  let Lhi := fun h : ℝ => min 1 ((1-Real.exp (-h))^(γ^2/2))*L
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hW (h : ℝ) (hh : 0 < h) : Tendsto (fun z => W h z/‖z‖^κ) (𝓝[≠] 0) (𝓝 L) :=
    reflected_source_williams_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ h hα₁ hreflect hα₂ hα₃ hh.le hs hξ hξ1 B Z hData B₀ hB₀
  have hE (h : ℝ) (hh : 0 < h) : Tendsto (fun z => E h z/‖z‖^κ) (𝓝[≠] 0) (𝓝 0) :=
    (isComplexLittleOAtZero_ofReal_iff κ (E h)).mp
      (reflected_source_full_copied_littleO P X Xc hX hc hm hcont γ hγ hγ₂ M hM
        N hN hfin hwhole hNa α₁ α₂ α₃ ξ h hα₁ hα₂ hα₃ hreflect hs hξ hξ1 hnear hfreeze hh.le)
  have hg (h : ℝ) (hh : 0 < h) : Tendsto (g h) (𝓝[≠] 0) (𝓝 (Llo h)) := by
    have hc := (reflected_kernel_coefficient_spatial_limits γ α₂ h).1.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
    simpa only [g,Llo,add_zero] using (hc.mul (hW h hh)).add (hE h hh)
  have hk (h : ℝ) (hh : 0 < h) : Tendsto (k h) (𝓝[≠] 0) (𝓝 (Lhi h)) := by
    have hc := (reflected_kernel_coefficient_spatial_limits γ α₂ h).2.mono_left (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
    simpa only [k,Lhi,add_zero] using (hc.mul (hW h hh)).add (hE h hh)
  have hdepth := reflected_kernel_coefficient_depth_limit γ
  have hLlo : Tendsto Llo atTop (𝓝 L) := by
    simpa only [Llo,one_mul] using hdepth.fst_nhds.mul_const L
  have hLhi : Tendsto Lhi atTop (𝓝 L) := by
    simpa only [Lhi,one_mul] using hdepth.snd_nhds.mul_const L
  have hbound (h : ℝ) (hh : 0 < h) : ∀ᶠ z : ℂ in 𝓝[≠] 0, g h z ≤ f z ∧ f z ≤ k h z := by
    have hQν := hData.1.1.2
    have hb := reflected_source_williams_kernel_squeeze P X hX Xc hc hm hcont γ hγ hγ₂ M hM
      N hN hi heq hfin α₁ α₂ α₃ ξ h hα₁ B hL hData _ hQν p hp hα₂ hα₃ hξ hξ1 hh
    filter_upwards [hb] with z hz
    have hlo := div_le_div_of_nonneg_right hz.1 (Real.rpow_nonneg (norm_nonneg z) κ)
    have hhi := div_le_div_of_nonneg_right hz.2 (Real.rpow_nonneg (norm_nonneg z) κ)
    exact ⟨by simpa only [g,Chi,E,f,W,ν,add_div,mul_div_assoc] using hlo,
      by simpa only [k,Clo,E,f,W,ν,add_div,mul_div_assoc] using hhi⟩
  exact reflected_ordered_two_sided_squeeze (𝓝[≠] (0 : ℂ)) f g k L Llo Lhi hg hk hLlo hLhi hbound

end DOZZ.Proofs
