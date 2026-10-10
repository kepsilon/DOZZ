/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceRadialJointLaw
public import DOZZ.FourPoint.Reflected.CopiedRegionRegroup
public import DOZZ.FourPoint.Reflected.WilliamsRealCutData
public import DOZZ.FourPoint.Reflected.VariableCutMeasurable
/-! Exact inverse-moment transport of the actual copied radial inner mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_copied_radial_inverse_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N) (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ)
    (B : Ω → BrownianPath × BrownianPath)
    (hL : IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (hData : IsReflectionData P γ α₁ B (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw (Q γ-α₁) Qν)
    (z : ℂ) (hz0 : z ≠ 0) (T : ℝ≥0) (hcoord : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) (p : ℝ) :
    (∫⁻ ω : Ω × Ω, (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ+
      ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
        ENNReal.ofReal (‖x‖^(-(γ*α₁)))*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))^(-p) ∂P.prod P) =
    ∫⁻ v : Ω × (ℝ × Ω), (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ+
      ENNReal.ofReal (reflected_radial_scale γ (Q γ-α₁) h Xc z v.1)*
        (ENNReal.ofReal (Real.exp (γ*v.2.1))*twoSidedReflectionCutMass γ v.2.1 B
          (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) v.2.2))^(-p)
      ∂P.prod ((brownianMaximumReferenceLaw (Q γ-α₁)).prod P) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let μ := (brownianMaximumReferenceLaw ν).prod P
  let _ : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
    isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let Y := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,
    reflected_radial_scale γ ν h Xc z ω)
  let Z := fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)
  let J := fun v : ℝ × Ω => ENNReal.ofReal (Real.exp (γ*v.1))*twoSidedReflectionCutMass γ v.1 B Z v.2
  let F := fun q : (ℝ≥0∞ × ℝ) × ℝ≥0∞ => (q.1.1,ENNReal.ofReal q.1.2*q.2)
  have hF : Measurable F := (measurable_fst.comp measurable_fst).prodMk
    (((measurable_snd.comp measurable_fst).ennreal_ofReal).mul measurable_snd)
  have ho : AEMeasurable (fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ) P :=
    (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have ht := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hb : AEMeasurable (reflected_radial_scale γ ν h Xc z) P :=
    ((ht.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hY : AEMeasurable Y P := ho.prodMk hb
  have hBm := conditionedPair_aemeasurable P B ν hData.1
  have hcut := reflected_williams_variable_cut_aemeasurable P (brownianMaximumReferenceLaw ν)
    γ B Z hBm hL.2.2.2.1 hL.2.2.2.2.1
  have hJ : AEMeasurable J μ :=
    (((measurable_fst.const_mul γ).exp.ennreal_ofReal).aemeasurable).mul hcut
  have hpack : AEMeasurable (fun v : Ω × (ℝ × Ω) => (Y v.1,J v.2)) (P.prod μ) :=
    (hY.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
      (hJ.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)
  have hlaw := reflected_source_copied_radial_joint_law P X hX Xc hc hm hcont γ hγ hγ₂ M hM
    N hN hi heq hfin α₁ α₂ α₃ ξ h hα₁ B hL hData Qν hQν z hz0 T hcoord hr hz hT
  have hmap := reflected_map_two_measures_prod_ae P μ Y J hY hJ
  change _ = ((P.map Y).prod (μ.map J)).map F at hlaw
  rw [← hmap,AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hpack] at hlaw
  let U := {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))}
  have hU : MeasurableSet U := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    simpa only [mem_compl_iff,mem_singleton_iff] using norm_pos_iff.mp hx.1
  have hK : Measurable (fun x : ℂ => ENNReal.ofReal (‖x‖^(-(γ*α₁)))) := by fun_prop
  have hI := reflected_copied_region_mass_aemeasurable P (originRadialPath Xc) N
    (originRadialPath_aemeasurable P X Xc hc hcont) hN hfin γ U hU hU0 _ hK
  have hactual := (ho.comp_quasiMeasurePreserving
    (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving).prodMk
    ((measurable_const : Measurable (fun _ : Ω × Ω => ENNReal.ofReal (‖z‖^(γ^2/2)))).aemeasurable.mul hI)
  dsimp only [Function.comp_apply,Pi.mul_apply,U] at hactual
  let G := fun v : ℝ≥0∞ × ℝ≥0∞ => (v.1+v.2)^(-p)
  have hG : Measurable G := by fun_prop
  have hiLeft := lintegral_map' hG.aemeasurable hactual
  have hiRight := lintegral_map' hG.aemeasurable (hF.comp_aemeasurable hpack)
  rw [hlaw] at hiLeft
  exact hiLeft.symm.trans hiRight

end DOZZ.Proofs
