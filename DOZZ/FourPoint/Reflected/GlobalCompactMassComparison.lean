/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.WeightedSpatialLimit
/-! Both compact comparison directions for literal extended-real global masses. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_global_compact_mass_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
      (originLateralCircleRegularization Xc ρ) γ (fun ω => (N ω).restrict (originLateralChart ρ)))
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ)
    (hfin : ∀ ω, N ω K < ⊤) (A : Set ℂ) (hA : MeasurableSet A)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hinner : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R*r)
    (houter : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖)
    (f₀ f₁ : BoundedContinuousFunction ℂ ℝ) (hf₀ : ∀ x, 0 ≤ f₀ x) (hf₁ : ∀ x, 0 ≤ f₁ x)
    (hf₀K : tsupport (f₀ : ℂ → ℝ) ⊆ K) (hf₁K : tsupport (f₁ : ℂ → ℝ) ⊆ K)
    (hf₀A : tsupport (f₀ : ℂ → ℝ) ⊆ A) (hf₁A : tsupport (f₁ : ℂ → ℝ) ⊆ Aᶜ)
    (q : ℝ) (hq : 0 < q) (a : TwoSidedPath) :
    let J := fun (f : BoundedContinuousFunction ℂ ℝ) (ω : Ω) =>
      ∫⁻ x in K, ENNReal.ofReal (f x)*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω
    let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
    (∫⁻ ω, (J f₀ ω+J f₁ ω)^(-q) ∂P) ≤
      m*(∫⁻ ω : Ω × Ω, (J f₀ ω.1+J f₁ ω.2)^(-q) ∂P.prod P) ∧
    (∫⁻ ω : Ω × Ω, (J f₀ ω.1+J f₁ ω.2)^(-q) ∂P.prod P) ≤
      m*(∫⁻ ω, (J f₀ ω+J f₁ ω)^(-q) ∂P) := by
  have hK0 : K ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx
    have hh : 2*ρ < ‖x‖ := hKU hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith : 0 < ‖x‖))
    simpa using hx0
  have hW : Measurable (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hsum (ω : Ω) :
      ENNReal.ofReal (∫ x, (f₀ x+f₁ x)*reflected_global_reinsertionWeight γ a x ∂N ω) =
      (∫⁻ x in K, ENNReal.ofReal (f₀ x)*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω) +
      (∫⁻ x in K, ENNReal.ofReal (f₁ x)*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω) := by
    have ht := reflected_global_compact_test_ofReal γ a (N ω) K hK hK0 (hfin ω)
      (f₀+f₁) (fun x => add_nonneg (hf₀ x) (hf₁ x))
      ((tsupport_add f₀ f₁).trans (union_subset hf₀K hf₁K))
    simp only [BoundedContinuousFunction.add_apply] at ht
    rw [ht]
    simp_rw [ENNReal.ofReal_add (hf₀ _) (hf₁ _), add_mul]
    exact lintegral_add_left (f₀.continuous.measurable.ennreal_ofReal.mul hW) _
  have hcopy (ω : Ω × Ω) :
      ENNReal.ofReal ((∫ x, f₀ x*reflected_global_reinsertionWeight γ a x ∂N ω.1)+
        (∫ x, f₁ x*reflected_global_reinsertionWeight γ a x ∂N ω.2)) =
      (∫⁻ x in K, ENNReal.ofReal (f₀ x)*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω.1)+
      (∫⁻ x in K, ENNReal.ofReal (f₁ x)*ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω.2) := by
    rw [ENNReal.ofReal_add
      (integral_nonneg fun x => mul_nonneg (hf₀ x) (reflected_global_reinsertionWeight_nonneg γ a x))
      (integral_nonneg fun x => mul_nonneg (hf₁ x) (reflected_global_reinsertionWeight_nonneg γ a x)),
      reflected_global_compact_test_ofReal γ a (N ω.1) K hK hK0 (hfin ω.1) f₀ hf₀ hf₀K,
      reflected_global_compact_test_ofReal γ a (N ω.2) K hK hK0 (hfin ω.2) f₁ hf₁ hf₁K]
  simpa only [hsum, hcopy] using reflected_global_compact_chaos_comparison
    P X Xc hX hc hm ρ γ hρ N hN K hK hKU A hA R r η hR0 hR hr hη
      hinner houter f₀ f₁ hf₀ hf₁ hf₀K hf₁K hf₀A hf₁A q hq a

end DOZZ.Proofs
