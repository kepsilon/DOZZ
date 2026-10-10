/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.LateralCompactLimit
public import DOZZ.FourPoint.Reflected.CopiedRadialChart
public import DOZZ.FourPoint.Reflected.CompactTestIntegral
/-! The limiting lateral comparison with the actual radial reinsertion weights. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Conditioning on the actual source radial path preserves both limiting compact comparison
bounds. The lateral version and its independence are obtained from the supplied ordinary GMC. -/
theorem reflected_conditional_compact_chaos_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
 :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ N ∧
      IndepFun (originRadialPath Xc) N P ∧
      (∀ (f : ℂ → ℝ≥0∞), Measurable f →
        ∀ G : TwoSidedPath × ℝ≥0∞ → ℝ≥0∞, Measurable G →
        (∫⁻ ω, G (originRadialPath Xc ω, ∫⁻ x in originLateralChart ρ, f x ∂M ω) ∂P) =
        ∫⁻ ω, G (originRadialPath Xc ω.1, ∫⁻ x in originLateralChart ρ,
          f x*ENNReal.ofReal (originRadialReinsertionWeight ρ γ
            (originRadialPath Xc ω.1) x) ∂N ω.2) ∂P.prod P) ∧
      ∀ (K : Set ℂ) (_hK : IsCompact K) (_hKU : K ⊆ originLateralChart ρ)
      (A : Set ℂ) (_hA : MeasurableSet A)
      (R r η : ℝ) (_hR0 : 0 ≤ R) (_hR : R ≤ 1 / 2) (_hr : 0 < r) (_hη : 0 < η)
      (_hinner : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R*r)
      (_houter : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖)
      (f₀ f₁ : BoundedContinuousFunction ℂ ℝ) (_hf₀ : ∀ x, 0 ≤ f₀ x) (_hf₁ : ∀ x, 0 ≤ f₁ x)
      (_hf₀K : tsupport (f₀ : ℂ → ℝ) ⊆ K) (_hf₁K : tsupport (f₁ : ℂ → ℝ) ⊆ K)
      (_hf₀A : tsupport (f₀ : ℂ → ℝ) ⊆ A) (_hf₁A : tsupport (f₁ : ℂ → ℝ) ⊆ Aᶜ)
      (q : ℝ) (_hq : 0 < q) ,
      let W := originRadialReinsertionWeight ρ γ
      let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
      let original := ∫⁻ a, ∫⁻ ω, ENNReal.ofReal
        (∫ x, (f₀ x+f₁ x)*W a x ∂N ω) ^ (-q) ∂P ∂P.map (originRadialPath Xc)
      let copied := ∫⁻ a, ∫⁻ ω : Ω × Ω, ENNReal.ofReal
        ((∫ x, f₀ x*W a x ∂N ω.1) + ∫ x, f₁ x*W a x ∂N ω.2) ^ (-q)
          ∂P.prod P ∂P.map (originRadialPath Xc)
      original ≤ m*copied ∧ copied ≤ m*original ∧
        (∫⁻ ω, ENNReal.ofReal (∫ x, (f₀ x+f₁ x) ∂M ω) ^ (-q) ∂P) = original := by
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨N, hN, hi, hwhole⟩ := reflected_copied_radial_chart_observable
    P X Xc hX hc hm hcont ρ γ hρ hγ hγ₂ M hM
  have hmass (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ)
      (f : ℂ → ℝ≥0∞) (hf : Measurable f) (q : ℝ) :
      (∫⁻ ω, (∫⁻ x in K, f x ∂M ω)^q ∂P) =
      ∫⁻ ω, (∫⁻ x in K, f x*ENNReal.ofReal (originRadialReinsertionWeight ρ γ
        (originRadialPath Xc ω.1) x) ∂N ω.2)^q ∂P.prod P := by
    have hl := hwhole (K.indicator f) (hf.indicator hK.measurableSet)
      (fun p => p.2^q) (measurable_snd.pow_const q)
    have he (a : TwoSidedPath) (μ : Measure ℂ) :
        (∫⁻ x in originLateralChart ρ, K.indicator f x*ENNReal.ofReal
          (originRadialReinsertionWeight ρ γ a x) ∂μ) =
        ∫⁻ x in K, f x*ENNReal.ofReal (originRadialReinsertionWeight ρ γ a x) ∂μ := by
      have hp : (fun x => K.indicator f x*ENNReal.ofReal
          (originRadialReinsertionWeight ρ γ a x)) = K.indicator
          (fun x => f x*ENNReal.ofReal (originRadialReinsertionWeight ρ γ a x)) := by
        funext x
        by_cases hx : x ∈ K <;> simp [hx]
      rw [hp, setLIntegral_indicator hK.measurableSet, inter_eq_left.mpr hKU]
    simpa only [setLIntegral_indicator hK.measurableSet, inter_eq_left.mpr hKU, he] using hl
  refine ⟨N, hN, hi, hwhole, ?_⟩
  intro K hK hKU A hA R r η hR0 hR hr hη hinner houter
    f₀ f₁ hf₀ hf₁ hf₀K hf₁K hf₀A hf₁A q hq
  have hfc₀ : HasCompactSupport (f₀ : ℂ → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hf₀K
  have hfc₁ : HasCompactSupport (f₁ : ℂ → ℝ) :=
    hK.of_isClosed_subset (isClosed_tsupport _) hf₁K
  have hb (a : TwoSidedPath) := reflected_lateral_compact_chaos_comparison P X Xc hX hc hm
    ρ hρ γ N hN K hK hKU A hA R r η hR0 hR hr hη hinner houter
    (originRadialWeightedTest ρ γ hρ a f₀ hfc₀)
    (originRadialWeightedTest ρ γ hρ a f₁ hfc₁)
    (fun x => mul_nonneg (hf₀ x) (Real.exp_pos _).le)
    (fun x => mul_nonneg (hf₁ x) (Real.exp_pos _).le)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₀ hfc₀).trans hf₀K)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₁ hfc₁).trans hf₁K)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₀ hfc₀).trans hf₀A)
    ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f₁ hfc₁).trans hf₁A) q hq
  simp only [originRadialWeightedTest_apply, BoundedContinuousFunction.add_apply, ← add_mul] at hb
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q))) *
          (∫⁻ ω : Ω × Ω, ENNReal.ofReal
            ((∫ x, f₀ x*originRadialReinsertionWeight ρ γ a x ∂N ω.1) +
              ∫ x, f₁ x*originRadialReinsertionWeight ρ γ a x ∂N ω.2) ^ (-q) ∂P.prod P)
                ∂P.map (originRadialPath Xc) := lintegral_mono fun a => (hb a).1
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · calc
      _ ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q))) *
          (∫⁻ ω, ENNReal.ofReal
            (∫ x, (f₀ x+f₁ x)*originRadialReinsertionWeight ρ γ a x ∂N ω) ^ (-q) ∂P)
              ∂P.map (originRadialPath Xc) := lintegral_mono fun a => (hb a).2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · let f := f₀+f₁
    have hf : ∀ x, 0 ≤ f x := fun x => add_nonneg (hf₀ x) (hf₁ x)
    have hfK : tsupport (f : ℂ → ℝ) ⊆ K :=
      (tsupport_add f₀ f₁).trans (union_subset hf₀K hf₁K)
    have hfc : HasCompactSupport (f : ℂ → ℝ) :=
      hK.of_isClosed_subset (isClosed_tsupport _) hfK
    have hMfin (ω : Ω) : M ω K < ⊤ := by
      let _ := hM.1 ω
      exact measure_lt_top _ _
    have hmtest (ω : Ω) := reflected_compact_test_integral_ofReal (M ω) K hK
      (hMfin ω) f hf hfK
    have hntest (a : TwoSidedPath) (ω : Ω) :
        ENNReal.ofReal (∫ x, f x*originRadialReinsertionWeight ρ γ a x ∂N ω) =
          ∫⁻ x in K, ENNReal.ofReal (f x)*ENNReal.ofReal
            (originRadialReinsertionWeight ρ γ a x) ∂N ω := by
      have he := reflected_compact_test_integral_ofReal (N ω) K hK
        (hN.2.2.1 ω K hK hKU) (originRadialWeightedTest ρ γ hρ a f hfc)
        (fun x => mul_nonneg (hf x) (Real.exp_pos _).le)
        ((tsupport_originRadialWeightedTest_subset ρ γ hρ a f hfc).trans hfK)
      simp only [originRadialWeightedTest_apply] at he
      exact he.trans (lintegral_congr fun x => ENNReal.ofReal_mul (hf x))
    have hlaw := hmass K hK hKU (fun x => ENNReal.ofReal (f x))
      f.continuous.measurable.ennreal_ofReal (-q)
    simp_rw [← hmtest, ← hntest] at hlaw
    have hF : Measurable (fun a : TwoSidedPath × Ω =>
        ENNReal.ofReal (∫ x, f x*originRadialReinsertionWeight ρ γ a.1 x ∂N a.2) ^ (-q)) := by
      exact (originRadialWeightedTest_integral_measurable ρ γ hρ f hfc N hN.1
        (fun ω => (measure_mono hfK).trans_lt (hN.2.2.1 ω K hK hKU))).ennreal_ofReal.pow_const (-q)
    have hAr := originRadialPath_aemeasurable P X Xc hc hcont
    have hpair : AEMeasurable (fun ω : Ω × Ω => (originRadialPath Xc ω.1, ω.2)) (P.prod P) :=
      (hAr.comp_quasiMeasurePreserving measurePreserving_fst.quasiMeasurePreserving).prodMk
        measurable_snd.aemeasurable
    have hp := lintegral_prod _ (hF.comp_aemeasurable hpair)
    have ho := lintegral_map' (hF.lintegral_prod_right' (ν := P)).aemeasurable hAr
    exact hlaw.trans (hp.trans ho.symm)

end DOZZ.Proofs
