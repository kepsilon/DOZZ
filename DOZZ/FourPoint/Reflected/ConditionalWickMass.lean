/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.ConditionalLateralLaw
public import DOZZ.GMC.FieldChaosNegativePower
import Mathlib.Tactic
/-! # Conditioning the actual lateral Wick mass with a random radial weight -/
public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The finite circle Wick expectation with its actual source radial weight is exactly the
iterated expectation with that radial path held fixed. The statement retains the finite Wick
variance and permits every jointly measurable radial weight. -/
theorem reflected_lateral_random_weight_factorization
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hKU : K ⊆ originLateralChart ρ)
    (ν : Measure K) [IsFiniteMeasure ν] (τ : ℝ≥0) (γ q : ℝ)
    (W : TwoSidedPath → K → ℝ≥0) (hW : Measurable (Function.uncurry W)) :
    let ε := Real.exp (-(originLateralCutoffBaseTime ρ + (τ : ℝ)))
    let Φ := fun ω (x : K) => originLateralCircleRegularization Xc ρ ω ε x
    (∫⁻ ω, fieldChaosMass P Φ ν (W (originRadialPath Xc ω)) γ ω ^ (-q) ∂P) =
      ∫⁻ a, ∫⁻ ω, fieldChaosMass P Φ ν (W a) γ ω ^ (-q) ∂P
        ∂P.map (originRadialPath Xc) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ε := Real.exp (-(originLateralCutoffBaseTime ρ + (τ : ℝ)))
  let Φ := fun ω (x : K) => originLateralCircleRegularization Xc ρ ω ε x
  let e : K → OriginLateralCutoffDomain ρ := fun x => (⟨x.val, hKU x.property⟩, τ)
  have he : Continuous e := by fun_prop
  have hΦ : IsCenteredGaussianField P Φ := by
    constructor
    · exact (originLateralCircleRegularization_measurableAtScale Xc hm ρ hρ ε).comp
        (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
    · intro n x
      exact originLateralCircleRegularization_gaussian P X Xc hX hc hm ρ hρ n
        (fun i => (ε, (x i).val))
  have hv : Measurable (fun x : K => ∫ ω, Φ ω x ^ 2 ∂P) := by
    simpa only [gaussianVariance, gaussianCovariance, pow_two] using
      centeredGaussianField_variance_measurable P Φ hΦ
  let F : TwoSidedPath × C(OriginLateralCutoffDomain ρ, ℝ) → ℝ≥0∞ := fun p =>
    (∫⁻ x, (W p.1 x : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (γ * p.2 (e x) - γ ^ 2 / 2 * ∫ ω, Φ ω x ^ 2 ∂P)) ∂ν) ^ (-q)
  have hF : Measurable F := by
    have hwe : Measurable (fun p : (TwoSidedPath × C(OriginLateralCutoffDomain ρ, ℝ)) × K =>
        (W p.1.1 p.2 : ℝ≥0∞)) := measurable_coe_nnreal_ennreal.comp
      (hW.comp (measurable_fst.fst.prodMk measurable_snd))
    have hev : Measurable (fun p : (TwoSidedPath × C(OriginLateralCutoffDomain ρ, ℝ)) × K =>
        p.1.2 (e p.2)) :=
      (continuous_eval.comp (continuous_fst.snd.prodMk (he.comp continuous_snd))).measurable
    have hv' := hv.comp (measurable_snd : Measurable
      (fun p : (TwoSidedPath × C(OriginLateralCutoffDomain ρ, ℝ)) × K => p.2))
    have hh : Measurable (fun p : (TwoSidedPath × C(OriginLateralCutoffDomain ρ, ℝ)) × K =>
        (W p.1.1 p.2 : ℝ≥0∞) * ENNReal.ofReal
          (Real.exp (γ * p.1.2 (e p.2) - γ ^ 2 / 2 * ∫ ω, Φ ω p.2 ^ 2 ∂P))) :=
      hwe.mul (((hev.const_mul γ).sub (hv'.const_mul (γ ^ 2 / 2))).exp.ennreal_ofReal)
    exact hh.lintegral_prod_right'.pow_const (-q)
  have hid : ∀ᵐ ω ∂P, ∀ a : TwoSidedPath,
      F (a, originLateralCutoffPath Xc ρ ω) = fieldChaosMass P Φ ν (W a) γ ω ^ (-q) := by
    filter_upwards [originLateralCutoffPath_eval_ae P Xc hcont ρ hρ] with ω hω a
    apply congrArg (fun y : ℝ≥0∞ => y ^ (-q))
    apply lintegral_congr
    intro x
    rw [hω (e x)]
    have ht : Real.log (1 / ε) = originLateralCutoffBaseTime ρ + (τ : ℝ) := by
      dsimp only [ε]
      rw [one_div, Real.log_inv, Real.log_exp, neg_neg]
    simp only [Φ, originLateralCircleRegularization, ht, e]
  calc
    (∫⁻ ω, fieldChaosMass P Φ ν (W (originRadialPath Xc ω)) γ ω ^ (-q) ∂P) =
        ∫⁻ ω, F (originRadialPath Xc ω, originLateralCutoffPath Xc ρ ω) ∂P :=
      lintegral_congr_ae (hid.mono fun ω hω => (hω _).symm)
    _ = ∫⁻ a, ∫⁻ y, F (a, y) ∂P.map (originLateralCutoffPath Xc ρ)
        ∂P.map (originRadialPath Xc) :=
      reflected_lateral_cutoff_radial_factorization P X Xc hX hc hm hcont ρ hρ F hF
    _ = ∫⁻ a, ∫⁻ ω, F (a, originLateralCutoffPath Xc ρ ω) ∂P
        ∂P.map (originRadialPath Xc) := by
      apply lintegral_congr
      intro a
      exact lintegral_map' ((hF.comp (measurable_const.prodMk measurable_id)).aemeasurable)
        (originLateralCutoffPath_aemeasurable P Xc hm hcont ρ hρ)
    _ = _ := by
      apply lintegral_congr
      intro a
      exact lintegral_congr_ae (hid.mono fun ω hω => hω a)

/-- Actual random radial weights satisfy the integrated two-sided compact lateral comparison. -/
theorem reflected_lateral_conditional_compact_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) (A : Set ℂ) (hA : MeasurableSet A)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1 / 2) (hr : 0 < r) (hη : 0 < η)
    (hinner : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R * r)
    (houter : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ (ν : Measure K) [IsFiniteMeasure ν] (τ : ℝ≥0),
      Real.exp (-(originLateralCutoffBaseTime ρ + (τ : ℝ))) ≤ min d ρ →
      ∀ (γ q : ℝ), 0 ≤ q → ∀ (W : TwoSidedPath → K → ℝ≥0),
      Measurable (Function.uncurry W) → (∀ a, ∃ b : ℝ≥0, ∀ x, W a x ≤ b) →
      let ε := Real.exp (-(originLateralCutoffBaseTime ρ + (τ : ℝ)))
      let Φ := fun ω (x : K) => originLateralCircleRegularization Xc ρ ω ε x
      let B : Set K := Subtype.val ⁻¹' A
      let m := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * R + η) / 2 * (q ^ 2 + q)))
      let original := ∫⁻ ω, fieldChaosMass P Φ ν (W (originRadialPath Xc ω)) γ ω ^ (-q) ∂P
      let copied := ∫⁻ a, ∫⁻ ω,
        fieldChaosMass (P.prod P) (reflected_decoupled_field Φ B) ν (W a) γ ω ^ (-q)
          ∂P.prod P ∂P.map (originRadialPath Xc)
      original ≤ m * copied ∧ copied ≤ m * original := by
  obtain ⟨d, hd, hb⟩ := reflected_lateral_compact_decoupling P X Xc hX hc hm
    ρ hρ K hK hKU A hA R r η hR0 hR hr hη hinner houter
  refine ⟨d, hd, ?_⟩
  intro ν _ τ hτ γ q hq W hW hWb
  let ε := Real.exp (-(originLateralCutoffBaseTime ρ + (τ : ℝ)))
  let Φ := fun ω (x : K) => originLateralCircleRegularization Xc ρ ω ε x
  let B : Set K := Subtype.val ⁻¹' A
  let m := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * R + η) / 2 * (q ^ 2 + q)))
  have hc' (a : TwoSidedPath) := hb ε (Real.exp_pos _) hτ ν (W a)
    (hW.comp (measurable_const.prodMk measurable_id)) (hWb a) γ q hq
  have he := reflected_lateral_random_weight_factorization P X Xc hX hc hm hcont
    ρ hρ K hKU ν τ γ q W hW
  change (∫⁻ ω, fieldChaosMass P Φ ν (W (originRadialPath Xc ω)) γ ω ^ (-q) ∂P) =
    ∫⁻ a, ∫⁻ ω, fieldChaosMass P Φ ν (W a) γ ω ^ (-q) ∂P
      ∂P.map (originRadialPath Xc) at he
  change (∫⁻ ω, fieldChaosMass P Φ ν (W (originRadialPath Xc ω)) γ ω ^ (-q) ∂P) ≤
      m * (∫⁻ a, ∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ B)
        ν (W a) γ ω ^ (-q) ∂P.prod P ∂P.map (originRadialPath Xc)) ∧
    (∫⁻ a, ∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ B)
        ν (W a) γ ω ^ (-q) ∂P.prod P ∂P.map (originRadialPath Xc)) ≤
      m * (∫⁻ ω, fieldChaosMass P Φ ν (W (originRadialPath Xc ω)) γ ω ^ (-q) ∂P)
  rw [he]
  constructor
  · calc
      _ ≤ ∫⁻ a, m * (∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ B)
          ν (W a) γ ω ^ (-q) ∂P.prod P) ∂P.map (originRadialPath Xc) :=
        lintegral_mono fun a => (hc' a).1
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · calc
      _ ≤ ∫⁻ a, m * (∫⁻ ω, fieldChaosMass P Φ ν (W a) γ ω ^ (-q) ∂P)
          ∂P.map (originRadialPath Xc) := lintegral_mono fun a => (hc' a).2
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end DOZZ.Proofs
