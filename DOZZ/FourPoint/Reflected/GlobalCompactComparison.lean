/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.CopiedRadialPlane
/-! Limiting compact comparisons expressed on the single global lateral carrier. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- A compact chart test uses the true unclamped radial factor against the global measure. -/
theorem reflected_global_radial_test_integral (ρ γ : ℝ) (hρ : 0 < ρ)
    (a : TwoSidedPath) (f : BoundedContinuousFunction ℂ ℝ)
    (hfU : tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ) (μ : Measure ℂ) :
    (∫ x, f x*originRadialReinsertionWeight ρ γ a x ∂μ.restrict (originLateralChart ρ)) =
      ∫ x, f x*reflected_global_reinsertionWeight γ a x ∂μ := by
  have hz (x : ℂ) (hx : x ∉ originLateralChart ρ) : f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hs => hx (hfU hs))
  have he : (∫ x, f x*originRadialReinsertionWeight ρ γ a x
      ∂μ.restrict (originLateralChart ρ)) =
      ∫ x, f x*originRadialReinsertionWeight ρ γ a x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [hz x hx, zero_mul]
  rw [he]
  apply integral_congr_ae
  exact ae_of_all μ fun x => by
    dsimp only
    by_cases hx : x ∈ originLateralChart ρ
    · rw [reflected_global_reinsertionWeight_chart ρ γ hρ a x hx]
    · rw [hz x hx, zero_mul, zero_mul]

/-- Both limiting compact comparisons apply to the global carrier, with the unclamped
radial path weights and the exact common-Gaussian factor. -/
theorem reflected_global_compact_chaos_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
      (originLateralCircleRegularization Xc ρ) γ (fun ω => (N ω).restrict (originLateralChart ρ)))
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ)
    (A : Set ℂ) (hA : MeasurableSet A)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hinner : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R*r)
    (houter : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖)
    (f₀ f₁ : BoundedContinuousFunction ℂ ℝ) (hf₀ : ∀ x, 0 ≤ f₀ x) (hf₁ : ∀ x, 0 ≤ f₁ x)
    (hf₀K : tsupport (f₀ : ℂ → ℝ) ⊆ K) (hf₁K : tsupport (f₁ : ℂ → ℝ) ⊆ K)
    (hf₀A : tsupport (f₀ : ℂ → ℝ) ⊆ A) (hf₁A : tsupport (f₁ : ℂ → ℝ) ⊆ Aᶜ)
    (q : ℝ) (hq : 0 < q) :
    let W := reflected_global_reinsertionWeight γ
    let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
    ∀ a : TwoSidedPath,
      (∫⁻ ω, ENNReal.ofReal (∫ x, (f₀ x+f₁ x)*W a x ∂N ω)^(-q) ∂P) ≤
        m*(∫⁻ ω : Ω × Ω, ENNReal.ofReal
          ((∫ x, f₀ x*W a x ∂N ω.1)+(∫ x, f₁ x*W a x ∂N ω.2))^(-q) ∂P.prod P) ∧
      (∫⁻ ω : Ω × Ω, ENNReal.ofReal
          ((∫ x, f₀ x*W a x ∂N ω.1)+(∫ x, f₁ x*W a x ∂N ω.2))^(-q) ∂P.prod P) ≤
        m*(∫⁻ ω, ENNReal.ofReal (∫ x, (f₀ x+f₁ x)*W a x ∂N ω)^(-q) ∂P) := by
  have hfc₀ : HasCompactSupport (f₀ : ℂ → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hf₀K
  have hfc₁ : HasCompactSupport (f₁ : ℂ → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hf₁K
  dsimp only
  intro a
  have hb := reflected_lateral_compact_chaos_comparison P X Xc hX hc hm ρ hρ γ
    (fun ω => (N ω).restrict (originLateralChart ρ)) hN K hK hKU A hA
    R r η hR0 hR hr hη hinner houter
    (originRadialWeightedTest ρ γ hρ a f₀ hfc₀)
    (originRadialWeightedTest ρ γ hρ a f₁ hfc₁)
    (fun x => mul_nonneg (hf₀ x) (Real.exp_pos _).le)
    (fun x => mul_nonneg (hf₁ x) (Real.exp_pos _).le)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₀ hfc₀).trans hf₀K)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₁ hfc₁).trans hf₁K)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₀ hfc₀).trans hf₀A)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₁ hfc₁).trans hf₁A) q hq
  simp only [originRadialWeightedTest_apply, BoundedContinuousFunction.add_apply, ← add_mul] at hb
  have hfU : tsupport ((f₀+f₁ : BoundedContinuousFunction ℂ ℝ) : ℂ → ℝ) ⊆ originLateralChart ρ :=
    (tsupport_add (f := (f₀ : ℂ → ℝ)) (g := (f₁ : ℂ → ℝ))).trans
      ((union_subset hf₀K hf₁K).trans hKU)
  have hsum (μ : Measure ℂ) :
      (∫ x, (f₀ x+f₁ x)*originRadialReinsertionWeight ρ γ a x
        ∂μ.restrict (originLateralChart ρ)) =
        ∫ x, (f₀ x+f₁ x)*reflected_global_reinsertionWeight γ a x ∂μ := by
    simpa only [BoundedContinuousFunction.add_apply] using
      reflected_global_radial_test_integral ρ γ hρ a (f₀+f₁) hfU μ
  simpa only [hsum,
    reflected_global_radial_test_integral ρ γ hρ a f₀ (hf₀K.trans hKU),
    reflected_global_radial_test_integral ρ γ hρ a f₁ (hf₁K.trans hKU),
    BoundedContinuousFunction.add_apply] using hb

end DOZZ.Proofs
