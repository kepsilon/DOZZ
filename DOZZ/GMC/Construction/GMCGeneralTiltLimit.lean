/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCJointCoordinateLimit

/-! The general GMC tilt identity after passing the finite-coordinate laws to their limit. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem exists_measurable_unweighted_path_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ G : Ω → gmcTiltCoordinateIndex → ℝ,
      Measurable G ∧
      (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω)) =ᵐ[P] G := by
  obtain ⟨E, hE, hEae⟩ := equatorGFF_GMC_finiteEval_field_proxy P X hX γ M hM
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  have heval : Measurable eval := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  let G : Ω → gmcTiltCoordinateIndex → ℝ := fun ω i =>
    match i with
    | .inl f => eval ω f
    | .inr j => (E (eval ω) j).toReal
  have hG : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    cases i with
    | inl f => exact (hX.2 f).1
    | inr j =>
      exact ENNReal.measurable_toReal.comp
        ((measurable_pi_apply j).comp (hE.comp heval))
  have hEq : (fun ω => gmcTiltCoordinatePath (eval ω) (M ω)) =ᵐ[P] G := by
    filter_upwards [hEae] with ω hω
    funext i
    cases i with
    | inl f => rfl
    | inr j =>
      change (M ω (gmcTiltCoordinateSet j)).toReal = (E (eval ω) j).toReal
      have hcoord := congrFun hω j
      change M ω (gmcTiltCoordinateSet j) = E (eval ω) j at hcoord
      exact congrArg ENNReal.toReal hcoord
  exact ⟨G, hG, hEq⟩

private theorem exists_measurable_weighted_path_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (shift : TestFn → ℝ) (w : BoundedContinuousFunction ℂ ℝ) :
    ∃ G : Ω → gmcTiltCoordinateIndex → ℝ,
      Measurable G ∧
      (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) =ᵐ[P] G := by
  classical
  have heval : Measurable (fun ω f => X ω f) := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hW : Measurable (fun z : ℂ => ENNReal.ofReal (w z)) :=
    ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hcoord : ∀ j : Option (ℚ × ℚ),
      ∃ g : (TestFn → ℝ) → ℝ, Measurable g ∧
        (fun ω => ((M ω).withDensity (fun z => ENNReal.ofReal (w z))
          (gmcTiltCoordinateSet j)).toReal) =ᵐ[P]
          fun ω => g (fun f => X ω f) := by
    intro j
    let B := gmcTiltCoordinateSet j
    have hB : MeasurableSet B := by
      cases j with
      | none => exact MeasurableSet.univ
      | some i => exact gmcLowerBox_measurableSet i
    let H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun _ μ =>
      (μ.withDensity (fun z => ENNReal.ofReal (w z))) B
    have hH : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2) := by
      have hEval : (fun μ : Measure ℂ =>
          (μ.withDensity (fun z => ENNReal.ofReal (w z))) B) =
          fun μ => ∫⁻ z, B.indicator (fun z => ENNReal.ofReal (w z)) z ∂μ := by
        funext μ
        rw [withDensity_apply _ hB, ← lintegral_indicator hB]
      rw [show (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2) =
          fun p => ∫⁻ z, B.indicator (fun z => ENNReal.ofReal (w z)) z ∂p.2 by
            funext p
            exact congrFun hEval p.2]
      exact (Measure.measurable_lintegral (hW.indicator hB)).comp measurable_snd
    obtain ⟨gE, hgE, hEq⟩ :=
      equatorGFF_GMC_function_field_proxy P X hX γ M hM H hH
    let g : (TestFn → ℝ) → ℝ := fun q => (gE q).toReal
    have hg : Measurable g := ENNReal.measurable_toReal.comp hgE
    refine ⟨g, hg, ?_⟩
    filter_upwards [hEq] with ω hω
    change ((M ω).withDensity (fun z => ENNReal.ofReal (w z)) B).toReal = _
    exact congrArg ENNReal.toReal hω
  choose g hg hEq using hcoord
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let G : Ω → gmcTiltCoordinateIndex → ℝ := fun ω i =>
    match i with
    | .inl f => eval ω f + shift f
    | .inr j => g j (eval ω)
  have hG : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    cases i with
    | inl f => exact (hX.2 f).1.add measurable_const
    | inr j => exact (hg j).comp heval
  have hEqAll : (fun ω => gmcTiltCoordinatePath
      (fun f => X ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) =ᵐ[P] G := by
    have hpoint : ∀ᵐ ω ∂P, ∀ j : Option (ℚ × ℚ),
        ((M ω).withDensity (fun z => ENNReal.ofReal (w z))
          (gmcTiltCoordinateSet j)).toReal = g j (eval ω) :=
      ae_all_iff.mpr hEq
    filter_upwards [hpoint] with ω hω
    funext i
    cases i with
    | inl f => rfl
    | inr j => exact hω j
  exact ⟨G, hG, hEqAll⟩

private theorem weightedMeasure_isFinite
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (w : BoundedContinuousFunction ℂ ℝ) :
    IsFiniteMeasure (μ.withDensity (fun z => ENNReal.ofReal (w z))) := by
  apply MeasureTheory.isFiniteMeasure_withDensity
  have hpoint : ∀ z, ENNReal.ofReal (w z) ≤ ENNReal.ofReal ‖w‖ := by
    intro z
    apply ENNReal.ofReal_le_ofReal
    exact le_trans (le_abs_self _) (w.norm_coe_le_norm z)
  have hbound : (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≤ ENNReal.ofReal ‖w‖ * μ Set.univ := by
    calc
      (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≤ ∫⁻ z, ENNReal.ofReal ‖w‖ ∂μ :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal ‖w‖ * μ Set.univ := lintegral_const _
  have hprod : ENNReal.ofReal ‖w‖ * μ Set.univ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (measure_lt_top μ Set.univ))
  exact ne_of_lt (lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hprod))

private theorem gmcTilt_density_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) :
    let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
      (Real.exp (L ω - gaussianVariance P L / 2))
    AEMeasurable density P ∧ ∀ᵐ ω ∂P, density ω ≠ 0 := by
  dsimp
  constructor
  · have hLmeas : AEMeasurable L P := hL.1.aestronglyMeasurable.aemeasurable
    have hExpArg : AEMeasurable (fun ω => L ω - gaussianVariance P L / 2) P :=
      hLmeas.sub_const _
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (Real.measurable_exp.comp_aemeasurable hExpArg)
  · filter_upwards [] with ω
    exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

/-- General GMC Cameron--Martin identity for every measurable nonnegative functional of the
test field and the limiting chaos measure. -/
theorem equatorGFF_GMC_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x r) L) c atTop)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P := by
  have _ := hγ
  have _ := hγ2
  classical
  let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q : Measure Ω := P.withDensity density
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let shift : TestFn → ℝ := fun f => gaussianCovariance P (fun ω => X ω f) L
  let leftPath : Ω → gmcTiltCoordinateIndex → ℝ := fun ω =>
    gmcTiltCoordinatePath (eval ω) (M ω)
  let rightPath : Ω → gmcTiltCoordinateIndex → ℝ := fun ω =>
    gmcTiltCoordinatePath (fun f => eval ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
  let decode : (gmcTiltCoordinateIndex → ℝ) →
      (TestFn → ℝ) × (Option (ℚ × ℚ) → ℝ≥0∞) := fun v =>
    (fun f => v (.inl f), fun j => ENNReal.ofReal (v (.inr j)))
  obtain ⟨G, hG, hGfactor⟩ := gmc_measurable_function_factors_through_finite_eval H hH
  have hdecode : Measurable decode := by
    apply Measurable.prodMk
    · rw [measurable_pi_iff]
      intro f
      exact measurable_pi_apply (Sum.inl f : gmcTiltCoordinateIndex)
    · rw [measurable_pi_iff]
      intro j
      exact ENNReal.measurable_ofReal.comp
        (measurable_pi_apply (Sum.inr j : gmcTiltCoordinateIndex))
  let K : (gmcTiltCoordinateIndex → ℝ) → ℝ≥0∞ := fun v => G (decode v)
  have hK : Measurable K := hG.comp hdecode
  obtain ⟨u, w, -, hw, hconv, heventual, -⟩ :=
    equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
      P X hX Xc hXc γ M hM L hL c hc (∅ : Finset gmcTiltCoordinateIndex)
  have hwEq : ∀ z : ℂ, w z = Real.exp (γ * c z) := by
    intro z
    exact equatorGFF_expCovariance_weight_limit_value
      P Xc L γ c hc u w hconv heventual z
  obtain ⟨leftProxy, hleftProxyMeas, hleftProxyAE⟩ :=
    exists_measurable_unweighted_path_proxy P X hX γ M hM
  have hleftAE_P : leftPath =ᵐ[P] leftProxy := by
    simpa [leftPath, eval] using hleftProxyAE
  have hleftAEMeasP : AEMeasurable leftPath P :=
    hleftProxyMeas.aemeasurable.congr hleftAE_P.symm
  have hdenData := gmcTilt_density_aemeasurable P X L hL
  have hdenAEMeas : AEMeasurable density P := by
    simpa [density] using hdenData.1
  have hdenNe : ∀ᵐ ω ∂P, density ω ≠ 0 := by
    simpa [density] using hdenData.2
  have hleftAE_Q : leftPath =ᵐ[Q] leftProxy := by
    exact (withDensity_ae_eq hdenAEMeas hdenNe).2 hleftAE_P
  have hleftAEMeasQ : AEMeasurable leftPath Q :=
    hleftProxyMeas.aemeasurable.congr hleftAE_Q.symm
  obtain ⟨rightProxy, hrightProxyMeas, hrightProxyAE⟩ :=
    exists_measurable_weighted_path_proxy P X hX γ M hM shift w
  have hweightEq (ω : Ω) :
      (M ω).withDensity (fun z => ENNReal.ofReal (w z)) =
      (M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))) := by
    congr 1
    funext z
    rw [hwEq z]
  have hrightAE_P : rightPath =ᵐ[P] rightProxy := by
    have hEq : (fun ω => gmcTiltCoordinatePath (fun f => eval ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) = rightPath := by
      funext ω
      rw [hweightEq ω]
    exact hEq.symm ▸ hrightProxyAE
  have hrightAEMeasP : AEMeasurable rightPath P :=
    hrightProxyMeas.aemeasurable.congr hrightAE_P.symm
  have hjoint := equatorGFF_GMC_fullCoordinate_limit_law
    P X hX γ M hM Xc hXc L hL c hc
  have hFiniteLeft (ω : Ω) : IsFiniteMeasure (M ω) := hM.1 ω
  have hDecodeLeft (ω : Ω) : decode (leftPath ω) =
      (eval ω, gmcFiniteMeasureEval ⟨M ω, hFiniteLeft ω⟩) := by
    apply Prod.ext
    · funext f
      rfl
    · funext j
      simp only [decode, leftPath, gmcTiltCoordinatePath,
        gmcFiniteMeasureEval, gmcTiltCoordinateSet]
      rw [ENNReal.ofReal_toReal
        (@MeasureTheory.measure_ne_top ℂ _ (M ω) (hFiniteLeft ω) _)]
      rfl
  have hLeftFactor (ω : Ω) : H (eval ω) (M ω) = K (leftPath ω) := by
    have hfactor := congrFun hGfactor (eval ω, ⟨M ω, hFiniteLeft ω⟩)
    have hfactor' : H (eval ω) (M ω) =
        G (eval ω, gmcFiniteMeasureEval ⟨M ω, hFiniteLeft ω⟩) := by
      simpa [gmcJointFiniteEval] using hfactor
    calc
      H (eval ω) (M ω) =
          G (eval ω, gmcFiniteMeasureEval ⟨M ω, hFiniteLeft ω⟩) := hfactor'
      _ = G (decode (leftPath ω)) := by rw [hDecodeLeft]
      _ = K (leftPath ω) := rfl
  have hFiniteRight (ω : Ω) : IsFiniteMeasure
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) := by
    rw [← hweightEq ω]
    exact weightedMeasure_isFinite (M ω) w
  have hDecodeRight (ω : Ω) : decode (rightPath ω) =
      ((fun f => eval ω f + shift f),
        gmcFiniteMeasureEval ⟨(M ω).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * c z))), hFiniteRight ω⟩) := by
    apply Prod.ext
    · funext f
      rfl
    · funext j
      simp only [decode, rightPath, gmcTiltCoordinatePath,
        gmcFiniteMeasureEval, gmcTiltCoordinateSet]
      rw [ENNReal.ofReal_toReal
        (@MeasureTheory.measure_ne_top ℂ _
          ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
          (hFiniteRight ω) _)]
      rfl
  have hRightFactor (ω : Ω) :
      H (fun f => eval ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) =
      K (rightPath ω) := by
    let μω := (M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))
    have hfactor := congrFun hGfactor
      ((fun f => eval ω f + shift f), ⟨μω, hFiniteRight ω⟩)
    have hfactor' : H (fun f => eval ω f + shift f) μω =
        G ((fun f => eval ω f + shift f), gmcFiniteMeasureEval ⟨μω, hFiniteRight ω⟩) := by
      simpa [gmcJointFiniteEval, μω] using hfactor
    calc
      H (fun f => eval ω f + shift f) μω =
          G ((fun f => eval ω f + shift f), gmcFiniteMeasureEval ⟨μω, hFiniteRight ω⟩) := hfactor'
      _ = G (decode (rightPath ω)) := by rw [hDecodeRight]
      _ = K (rightPath ω) := rfl
  have hObsLeftAEMeas : AEMeasurable (fun ω => K (leftPath ω)) P :=
    hK.aemeasurable.comp_aemeasurable hleftAEMeasP
  have hObsRightAEMeas : AEMeasurable (fun ω => K (rightPath ω)) P :=
    hK.aemeasurable.comp_aemeasurable hrightAEMeasP
  have hObsLeftAEMeasQ : AEMeasurable (fun ω => K (leftPath ω)) Q :=
    hK.aemeasurable.comp_aemeasurable hleftAEMeasQ
  calc
    (∫⁻ ω, density ω * H (eval ω) (M ω) ∂P) =
        ∫⁻ ω, density ω * K (leftPath ω) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          rw [hLeftFactor ω]
    _ = ∫⁻ ω, K (leftPath ω) ∂Q := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul₀ hdenAEMeas hObsLeftAEMeas
    _ = ∫⁻ y, K y ∂Measure.map leftPath Q :=
      (lintegral_map' hK.aemeasurable hleftAEMeasQ).symm
    _ = ∫⁻ y, K y ∂Measure.map rightPath P := by rw [hjoint]
    _ = ∫⁻ ω, K (rightPath ω) ∂P :=
      lintegral_map' hK.aemeasurable hrightAEMeasP
    _ = ∫⁻ ω, H (fun f => eval ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          rw [hRightFactor ω]

end DOZZ.Proofs
