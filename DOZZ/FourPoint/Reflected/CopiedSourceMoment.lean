/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedRegionRegroup
public import DOZZ.FourPoint.Reflected.DecorrelationError
public import DOZZ.FourPoint.Reflected.SpatialBoundary
import Mathlib.Tactic
/-! The copied separated moment retains the literal source outer mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_copied_separatedMoment_source
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N) (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (α₁ α₂ α₃ ξ s q : ℝ) (z : ℂ)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ)) :
    reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z s (‖z‖^(1-ξ)) q =
      ∫⁻ ω : Ω × Ω, ((∫⁻ x in reflected_innerRegion s,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2)+
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ)^(-q) ∂P.prod P := by
  let _ : IsProbabilityMeasure P := hX.1
  let U := reflected_innerRegion s
  let V := reflected_outerRegion (‖z‖^(1-ξ))
  let K := fun x : ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)
  have hU : MeasurableSet U := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hV : MeasurableSet V := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_insert.mpr (measurableSet_singleton (1 : ℂ)) : MeasurableSet ({0,1} : Set ℂ)).compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    simpa only [mem_compl_iff,mem_singleton_iff] using norm_pos_iff.mp hx.1
  have hV0 : V ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    simpa only [mem_compl_iff,mem_singleton_iff] using norm_pos_iff.mp (hr.trans hx.1)
  have hK : Measurable K := (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hF : Measurable (fun p : ℝ≥0∞ × ℝ≥0∞ => (p.1+p.2)^(-q)) := by fun_prop
  have he := reflected_copied_reinserted_regions_regroup P (originRadialPath Xc) N
    (originRadialPath_aemeasurable P X Xc hc hcont) hN hi hfin γ U V hU hV hU0 hV0 K hK _ hF
  change reflected_copied_separatedMoment P Xc N γ α₁ α₂ α₃ z s (‖z‖^(1-ξ)) q = _ at he
  rw [he]
  apply lintegral_congr_ae
  filter_upwards [measurePreserving_fst.quasiMeasurePreserving.ae heq,
    measurePreserving_fst.quasiMeasurePreserving.ae
      (reflected_source_outerMass_eq_comparison_region P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ ξ z hz)] with ω hn ho
  rw [hn,reflected_reinserted_region_eq γ (originRadialPath Xc ω.1) (M ω.1) V hV hV0 K hK,ho]
  rfl

end DOZZ.Proofs
