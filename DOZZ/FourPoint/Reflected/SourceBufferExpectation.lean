/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ThreeMassInverseError
public import DOZZ.FourPoint.Reflected.SourceRegionPartition
public import DOZZ.FourPoint.Reflected.SourceOuterMoments
public import DOZZ.Statements.FourPoint.GammaHalfMoment
/-! The literal source buffer error is bounded by its first-order retained-mass expectation. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_source_buffer_inverse_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ ξ s p : ℝ)
    (hp : 0 < p) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hzn : ‖z‖ ≤ 1)
    (hr1 : ‖z‖^(1-ξ) ≤ 1) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (hs : 0 < s) (hsr : s ≤ ‖z‖^(1-ξ))
    (hBuffer : (∫⁻ ω, (∫⁻ x in {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-(p+1)) ∂P) < ⊤) :
    |gammaHalfMoment P M γ α₁ α₂ α₃ p z-
      (reflected_source_separatedMoment P M γ α₁ α₂ α₃ z s (‖z‖^(1-ξ)) p).toReal| ≤
    p*(∫⁻ ω, (∫⁻ x in {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)},
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)*
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-(p+1)) ∂P).toReal := by
  let K := fun x : ℂ => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)
  let F := fun ω => coulombMass γ (M ω) ![-γ/2,α₁,α₂] ![z,0,1] α₃
  let I := fun ω => ∫⁻ x in reflected_innerRegion s, K x ∂M ω
  let B := fun ω => ∫⁻ x in {x : ℂ | s ≤ ‖x‖ ∧ ‖x‖ < ‖z‖^(1-ξ)}, K x ∂M ω
  let O := fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  have hK : Measurable K := (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hU : MeasurableSet (reflected_innerRegion s) :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hI : AEMeasurable I P := by
    simpa only [lintegral_indicator hU] using gmc_lintegral_aemeasurable
      P X hX γ hγ hγ₂ M hM _ (hK.indicator hU)
  have hF : AEMeasurable F P := gmc_coulombMass_aemeasurable P X hX γ hγ hγ₂ M hM
    ![-γ/2,α₁,α₂] ![z,0,1] α₃
  have hO : AEMeasurable O P :=
    (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have houter := reflected_source_outerMass_eq_comparison_region P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ ξ z hz
  change (∀ᵐ ω ∂P, O ω = ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)), K x ∂M ω) at houter
  have heq : ∀ᵐ ω ∂P, F ω = (I ω+O ω)+B ω := by
    filter_upwards [reflected_source_three_region_partition P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ s z hs hsr,houter] with ω he ho
    change F ω = I ω+B ω+(∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)), K x ∂M ω) at he
    rw [← ho] at he
    exact he.trans (by ac_rfl)
  have hOp : ∀ᵐ ω ∂P, 0 < O ω :=
    (reflected_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hzn hr1).mono fun _ hω => hω.1
  have hinj : Function.Injective (![z,0,1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hcharges : ∀ i : Fin 3, (![-γ/2,α₁,α₂] : Fin 3 → ℝ) i < Q γ := by
    intro i
    fin_cases i
    · change -γ/2 < Q γ
      have hQ : 0 < Q γ := by unfold Q; positivity
      linarith only [hγ,hQ]
    · exact hα₁
    · exact hα₂
  have hFf : ∀ᵐ ω ∂P, F ω ≠ ⊤ :=
    (reflected_coulombMass_ae_finite P X hX γ hγ hγ₂ M hM ![z,0,1] hinj
      ![-γ/2,α₁,α₂] α₃ hcharges hα₃).mono fun _ hω => hω.ne
  obtain ⟨C,_,hC⟩ := reflected_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ p hp.le
  have hInv : (∫⁻ ω, O ω^(-p) ∂P) < ⊤ :=
    lt_of_le_of_lt (hC z ξ hzn hr1) ENNReal.ofReal_lt_top
  have he := reflected_three_mass_inverse_error P F I B O hF hI hO p hp heq hOp hFf hInv hBuffer
  have hsep : reflected_source_separatedMoment P M γ α₁ α₂ α₃ z s (‖z‖^(1-ξ)) p =
      ∫⁻ ω, (I ω+O ω)^(-p) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [houter] with ω hω
    change (I ω+(∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)), K x ∂M ω))^(-p) = (I ω+O ω)^(-p)
    rw [← hω]
  rw [hsep]
  exact he

end DOZZ.Proofs
