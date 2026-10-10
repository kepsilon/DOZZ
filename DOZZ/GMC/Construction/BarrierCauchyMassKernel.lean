/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.BarrierCauchyMass
public import DOZZ.GMC.Construction.BarrierCauchyKernel
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.Complex.Tietze

/-! Tonelli identities connecting growing-barrier test masses to their spatial pair kernel. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- On a compact subset of the chart, the product reference measure can be written as planar
volume with the two continuous density factors. The support hypothesis lets this replace the
global reference measure in spatial kernel estimates. -/
theorem logRegularizationReference_pair_lintegral_eq_volume_restrict
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    [SFinite (logRegularizationReference U dens)]
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (G : ℂ × ℂ → ℝ≥0∞) (hG : Measurable G)
    (hGsupport : ∀ p, p ∉ K ×ˢ K → G p = 0) :
    ∫⁻ p, G p ∂((logRegularizationReference U dens).prod
        (logRegularizationReference U dens)) =
      ∫⁻ p in K ×ˢ K,
        ENNReal.ofReal (dens p.1) * ENNReal.ofReal (dens p.2) * G p
          ∂(volume.prod volume) := by
  classical
  let S : Set (ℂ × ℂ) := K ×ˢ K
  let μ : Measure ℂ := logRegularizationReference U dens
  let dK : C(K, ℝ) :=
    ⟨fun x => dens x, (hY.densityContinuous.mono hKU).comp_continuous
      continuous_subtype_val (fun x => x.2)⟩
  obtain ⟨dExt, hdExt⟩ := ContinuousMap.exists_restrict_eq hK.isClosed dK
  let d : ℂ → ℝ := dExt
  let dENN : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (d x)
  have hdENN : Measurable dENN := ENNReal.measurable_ofReal.comp dExt.continuous.measurable
  have hdK (x : ℂ) (hx : x ∈ K) : d x = dens x := by
    have h := congrArg (fun f : C(K, ℝ) => f ⟨x, hx⟩) hdExt
    simpa [dK, d] using h
  have hμK : μ.restrict K = (volume.restrict K).withDensity dENN := by
    have hKmeas : MeasurableSet K := hK.measurableSet
    have hrestrict : (volume.restrict U).restrict K = volume.restrict K := by
      rw [Measure.restrict_restrict hKmeas]
      congr 1
      ext x
      simp only [Set.mem_inter_iff]
      exact ⟨fun hx => hx.1, fun hx => ⟨hx, hKU hx⟩⟩
    change ((volume.restrict U).withDensity
      (fun x => ENNReal.ofReal (dens x))).restrict K = _
    rw [restrict_withDensity hKmeas]
    rw [hrestrict]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hKmeas] with x hx
    simp only [dENN]
    congr 1
    exact (hdK x hx).symm
  have hS : MeasurableSet S := hK.measurableSet.prod hK.measurableSet
  have hdPair : Measurable (fun p : ℂ × ℂ => dENN p.1 * dENN p.2) :=
    (hdENN.comp measurable_fst).mul (hdENN.comp measurable_snd)
  have hsupport : ∫⁻ p, G p ∂(μ.prod μ) = ∫⁻ p, G p ∂(μ.prod μ).restrict S := by
    calc
      ∫⁻ p, G p ∂(μ.prod μ) = ∫⁻ p, S.indicator G p ∂(μ.prod μ) := by
        apply lintegral_congr
        intro p
        by_cases hp : p ∈ S
        · simp [hp]
        · simp [hp, hGsupport p hp]
      _ = ∫⁻ p, G p ∂(μ.prod μ).restrict S := by
        rw [lintegral_indicator hS]
  rw [hsupport, ← Measure.prod_restrict, hμK,
    prod_withDensity hdENN hdENN, Measure.prod_restrict]
  rw [lintegral_withDensity_eq_lintegral_mul _ hdPair hG]
  change (∫⁻ p in S, dENN p.1 * dENN p.2 * G p
      ∂(volume.prod volume)) = _
  apply setLIntegral_congr_fun hS
  intro p hp
  have hfirst : d p.1 = dens p.1 := hdK p.1 hp.1
  have hsecond : d p.2 = dens p.2 := hdK p.2 hp.2
  simp [dENN, hfirst, hsecond, mul_assoc]

/-- The nonnegative extended-real version of the growing-barrier test mass. -/
noncomputable def compatibleGrowingBarrierTestMassENN
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ) (γ a : ℝ) (k₀ : ℕ)
    (r : ℝ) (b : Bool) (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) : ℝ≥0∞ := by
  classical
  exact ∫⁻ x, ENNReal.ofReal (f x) *
    admissibleLogWickWeight P (if b then Y else Z) γ (Real.exp (-r)) x ω *
    Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
      (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂logRegularizationReference U dens

/-- A selected admissible Wick weight has extended expectation one at every allowed cutoff. -/
theorem compatibleAdmissibleSelectedWickWeight_lintegral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (b : Bool) (ε : ℝ) (hε : 0 < ε)
    (hεcut : ε ≤ min ε₀ ε₁) (x : ℂ) (γ : ℝ) :
    ∫⁻ ω, admissibleLogWickWeight P (if b then Y else Z) γ ε x ω ∂P = 1 := by
  let q : Fin 1 → ℝ × ℂ := fun _ => (ε, x)
  let V : Ω → Fin 1 → ℝ := fun ω _ => (if b then Y else Z) ω ε x
  have hq : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ min ε₀ ε₁ := by
    intro i
    simp only [q]
    exact ⟨hε, hεcut⟩
  have hqY : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₀ := by
    intro i
    exact ⟨(hq i).1, le_trans (hq i).2 (min_le_left _ _)⟩
  have hqZ : ∀ i, 0 < (q i).1 ∧ (q i).1 ≤ ε₁ := by
    intro i
    exact ⟨(hq i).1, le_trans (hq i).2 (min_le_right _ _)⟩
  have hV : IsCenteredJointlyGaussian P V := by
    cases b with
    | false => simpa [V] using hZ.gaussian 1 q hqZ
    | true => simpa [V] using hY.gaussian 1 q hqY
  have hwick := wick_exponential_lintegral_expectation P V hV 0 γ
  simpa [admissibleLogWickWeight, V, q] using hwick

/-- A selected Wick weight is jointly measurable in the sample and spatial point at every
admissible cutoff. -/
theorem compatibleAdmissibleSelectedWickWeight_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (b : Bool) (γ ε : ℝ) :
    Measurable (fun q : Ω × ℂ =>
      admissibleLogWickWeight P (if b then Y else Z) γ ε q.2 q.1) := by
  cases b with
  | false =>
      change Measurable (fun q : Ω × ℂ => ENNReal.ofReal (Real.exp
        (γ * Z q.1 ε q.2 - γ ^ 2 / 2 *
          gaussianVariance P (fun ω => Z ω ε q.2))))
      have hv0 := admissibleLogRegularization_variance_measurable
        P U dens ε₁ Z hZ ε
      have hvar : Measurable (fun q : Ω × ℂ => gaussianVariance P
          (fun ω => Z ω ε q.2)) := hv0.comp measurable_snd
      have hfield : Measurable (fun q : Ω × ℂ => Z q.1 ε q.2) :=
        hZ.measurableAtScale ε
      fun_prop
  | true =>
      change Measurable (fun q : Ω × ℂ => ENNReal.ofReal (Real.exp
        (γ * Y q.1 ε q.2 - γ ^ 2 / 2 *
          gaussianVariance P (fun ω => Y ω ε q.2))))
      have hv0 := admissibleLogRegularization_variance_measurable
        P U dens ε₀ Y hY ε
      have hvar : Measurable (fun q : Ω × ℂ => gaussianVariance P
          (fun ω => Y ω ε q.2)) := hv0.comp measurable_snd
      have hfield : Measurable (fun q : Ω × ℂ => Y q.1 ε q.2) :=
        hY.measurableAtScale ε
      fun_prop

/-- The mixed growing-barrier pair kernel is measurable in its two spatial roots. -/
theorem compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (γ a : ℝ) (k₀ : ℕ) (r s : ℝ) (b₁ b₂ : Bool) :
    Measurable (fun p : ℂ × ℂ =>
      compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
        P Y Z γ a k₀ r s p.1 p.2 b₁ b₂) := by
  classical
  let F : Ω × (ℂ × ℂ) → ℝ≥0∞ := fun q =>
    admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) q.2.1 q.1 *
      admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) q.2.2 q.1 *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.1) *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.2)
  have hbar₁ : Measurable (fun q : Ω × (ℂ × ℂ) =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.1)) := by
    exact measurable_const.indicator
      (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r |>.preimage
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  have hbar₂ : Measurable (fun q : Ω × (ℂ × ℂ) =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) (q.1, q.2.2)) := by
    exact measurable_const.indicator
      (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ s |>.preimage
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hwick₁ : Measurable (fun q : Ω × (ℂ × ℂ) =>
      admissibleLogWickWeight P (if b₁ then Y else Z) γ
        (Real.exp (-r)) q.2.1 q.1) := by
    have h := compatibleAdmissibleSelectedWickWeight_measurable
      P U dens ε₀ ε₁ Y Z hY hZ b₁ γ (Real.exp (-r))
    exact h.comp (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hwick₂ : Measurable (fun q : Ω × (ℂ × ℂ) =>
      admissibleLogWickWeight P (if b₂ then Y else Z) γ
        (Real.exp (-s)) q.2.2 q.1) := by
    have h := compatibleAdmissibleSelectedWickWeight_measurable
      P U dens ε₀ ε₁ Y Z hY hZ b₂ γ (Real.exp (-s))
    exact h.comp (f := fun q : Ω × (ℂ × ℂ) => (q.1, q.2.2))
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hF : Measurable F := by
    dsimp [F]
    exact ((hwick₁.mul hwick₂).mul hbar₁).mul hbar₂
  let μ : Measure ℂ := logRegularizationReference U dens
  have hEq : (fun p : ℂ × ℂ =>
      compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
        P Y Z γ a k₀ r s p.1 p.2 b₁ b₂) =
      fun p => ∫⁻ ω, F (ω, p) ∂P := by
    funext p
    rfl
  rw [hEq]
  exact (hF.comp measurable_swap).lintegral_prod_right'

/-- The nonnegative extended good mass is finite almost surely whenever its deterministic test
mass against the reference measure is finite. The barrier can only decrease the expected mass. -/
theorem compatibleGrowingBarrierTestMassENN_finite_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    [SFinite (logRegularizationReference U dens)]
    (γ a : ℝ) (k₀ : ℕ) (r : ℝ) (b : Bool)
    (f : BoundedContinuousFunction ℂ ℝ) (_hf : ∀ x, 0 ≤ f x)
    (hcut : 0 < Real.exp (-r))
    (hcutle : Real.exp (-r) ≤ min ε₀ ε₁)
    (htest : ∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens ≠ ∞) :
    ∀ᵐ ω ∂P, compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ r b ω f < ∞ := by
  classical
  let μ : Measure ℂ := logRegularizationReference U dens
  let W : Ω × ℂ → ℝ≥0∞ := fun q =>
    admissibleLogWickWeight P (if b then Y else Z) γ (Real.exp (-r)) q.2 q.1 *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) q
  let F : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (f q.2) * W q
  have hvar : Measurable (fun x : ℂ => gaussianVariance P
      (fun ω => compatibleAdmissibleFineField Y Z b ω (Real.exp (-r)) x)) :=
    compatibleAdmissibleFineField_variance_measurable P U dens ε₀ ε₁ Y Z hY hZ b
      (Real.exp (-r))
  have hfield : Measurable (fun q : Ω × ℂ =>
      compatibleAdmissibleFineField Y Z b q.1 (Real.exp (-r)) q.2) := by
    cases b with
    | false => exact hZ.measurableAtScale (Real.exp (-r))
    | true => exact hY.measurableAtScale (Real.exp (-r))
  have hWick : Measurable (fun q : Ω × ℂ =>
      admissibleLogWickWeight P (if b then Y else Z) γ (Real.exp (-r)) q.2 q.1) := by
    cases b with
    | false =>
        change Measurable (fun q : Ω × ℂ => ENNReal.ofReal (Real.exp
          (γ * Z q.1 (Real.exp (-r)) q.2 - γ ^ 2 / 2 * gaussianVariance P
            (fun ω => Z ω (Real.exp (-r)) q.2))))
        have hv0 := admissibleLogRegularization_variance_measurable
          P U dens ε₁ Z hZ (Real.exp (-r))
        have hv : Measurable (fun q : Ω × ℂ => gaussianVariance P
            (fun ω => Z ω (Real.exp (-r)) q.2)) := by
          change Measurable ((fun x : ℂ => gaussianVariance P
            (fun ω => Z ω (Real.exp (-r)) x)) ∘ Prod.snd)
          exact hv0.comp measurable_snd
        have hfield' : Measurable (fun q : Ω × ℂ => Z q.1 (Real.exp (-r)) q.2) :=
          hZ.measurableAtScale (Real.exp (-r))
        fun_prop
    | true =>
        change Measurable (fun q : Ω × ℂ => ENNReal.ofReal (Real.exp
          (γ * Y q.1 (Real.exp (-r)) q.2 - γ ^ 2 / 2 * gaussianVariance P
            (fun ω => Y ω (Real.exp (-r)) q.2))))
        have hv0 := admissibleLogRegularization_variance_measurable
          P U dens ε₀ Y hY (Real.exp (-r))
        have hv : Measurable (fun q : Ω × ℂ => gaussianVariance P
            (fun ω => Y ω (Real.exp (-r)) q.2)) := by
          change Measurable ((fun x : ℂ => gaussianVariance P
            (fun ω => Y ω (Real.exp (-r)) x)) ∘ Prod.snd)
          exact hv0.comp measurable_snd
        have hfield' : Measurable (fun q : Ω × ℂ => Y q.1 (Real.exp (-r)) q.2) :=
          hY.measurableAtScale (Real.exp (-r))
        fun_prop
  have hbar : Measurable (fun q : Ω × ℂ =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) q) :=
    measurable_const.indicator (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r)
  have hF : Measurable F := by
    dsimp [F, W]
    exact (ENNReal.measurable_ofReal.comp (f.continuous.measurable.comp measurable_snd)).mul
      (hWick.mul hbar)
  have hmass : (fun ω => compatibleGrowingBarrierTestMassENN
      P U dens Y Z γ a k₀ r b ω f) = fun ω => ∫⁻ x, F (ω, x) ∂μ := by
    funext ω
    change (∫⁻ x, ENNReal.ofReal (f x) *
      admissibleLogWickWeight P (if b then Y else Z) γ (Real.exp (-r)) x ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂μ) = _
    apply lintegral_congr
    intro x
    dsimp [F, W]
    ac_rfl
  have hmean :
      ∫⁻ ω, compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ r b ω f ∂P ≤
        ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    rw [hmass]
    calc
      ∫⁻ ω, ∫⁻ x, F (ω, x) ∂μ ∂P =
          ∫⁻ x, ∫⁻ ω, F (ω, x) ∂P ∂μ := by
        rw [← lintegral_prod F hF.aemeasurable, lintegral_prod_symm F hF.aemeasurable]
      _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        apply lintegral_mono
        intro x
        have hwick := compatibleAdmissibleSelectedWickWeight_lintegral_eq_one
          P U dens ε₀ ε₁ Y Z hY hZ b (Real.exp (-r)) hcut hcutle x γ
        have hbarle (ω : Ω) :
            Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
              (fun _ => (1 : ℝ≥0∞)) (ω, x) ≤ 1 := by
          by_cases hgood : (ω, x) ∈ admissibleGrowingBarrierSet Y a k₀ r
          · simp [Set.indicator, hgood]
          · simp [Set.indicator, hgood]
        calc
          ∫⁻ ω, F (ω, x) ∂P ≤
              ∫⁻ ω, ENNReal.ofReal (f x) *
                admissibleLogWickWeight P (if b then Y else Z) γ
                  (Real.exp (-r)) x ω ∂P := by
            apply lintegral_mono
            intro ω
            dsimp [F, W]
            calc
              _ = (ENNReal.ofReal (f x) * admissibleLogWickWeight P
                    (if b then Y else Z) γ (Real.exp (-r)) x ω) *
                    Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
                      (fun _ => (1 : ℝ≥0∞)) (ω, x) := by ac_rfl
              _ ≤ (ENNReal.ofReal (f x) * admissibleLogWickWeight P
                    (if b then Y else Z) γ (Real.exp (-r)) x ω) * 1 :=
                mul_le_mul_of_nonneg_left (hbarle ω) (by positivity)
              _ = _ := by simp
          _ = ENNReal.ofReal (f x) := by
            rw [lintegral_const_mul'' _]
            · rw [hwick]
              simp
            · exact (hWick.comp (measurable_id.prodMk measurable_const)).aemeasurable
  have hfinite :
      ∫⁻ ω, compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ r b ω f ∂P ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hmean (lt_top_iff_ne_top.mpr (by simpa [μ] using htest)))
  have hmassMeas : Measurable (fun ω =>
      compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ r b ω f) := by
    rw [hmass]
    exact hF.lintegral_prod_right'
  exact ae_lt_top hmassMeas hfinite


/-- For two nonnegative growing-barrier masses, their mixed second moment is the spatial integral
of the mixed two-root Wick kernel. Family choices and fine cutoffs are independent at the roots. -/
theorem compatibleGrowingBarrierTestMassENN_mixed_pair_kernel
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    [SFinite (logRegularizationReference U dens)]
    (γ a : ℝ) (k₀ : ℕ) (r s : ℝ) (b₁ b₂ : Bool)
    (f : BoundedContinuousFunction ℂ ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∫⁻ ω, compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ r b₁ ω f *
      compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ s b₂ ω f ∂P =
    ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (f p.1 * f p.2) *
      compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Z γ a k₀ r s
        p.1 p.2 b₁ b₂ ∂((logRegularizationReference U dens).prod
          (logRegularizationReference U dens)) := by
  classical
  let μ : Measure ℂ := logRegularizationReference U dens
  let C : Ω × ℂ → ℝ≥0∞ := fun q =>
    admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) q.2 q.1 *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) q
  let D : Ω × ℂ → ℝ≥0∞ := fun q =>
    admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) q.2 q.1 *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) q
  let A : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (f q.2) * C q
  let B : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal (f q.2) * D q
  let H : Ω → ℂ → ℂ → ℝ≥0∞ := fun ω x y => A (ω, x) * B (ω, y)
  have hvar₁ : Measurable (fun x : ℂ => gaussianVariance P
      (fun ω => compatibleAdmissibleFineField Y Z b₁ ω (Real.exp (-r)) x)) :=
    compatibleAdmissibleFineField_variance_measurable P U dens ε₀ ε₁ Y Z hY hZ b₁
      (Real.exp (-r))
  have hvar₂ : Measurable (fun x : ℂ => gaussianVariance P
      (fun ω => compatibleAdmissibleFineField Y Z b₂ ω (Real.exp (-s)) x)) :=
    compatibleAdmissibleFineField_variance_measurable P U dens ε₀ ε₁ Y Z hY hZ b₂
      (Real.exp (-s))
  have hbar₁ : Measurable (fun q : Ω × ℂ =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) q) :=
    measurable_const.indicator
      (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ r)
  have hbar₂ : Measurable (fun q : Ω × ℂ =>
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) q) :=
    measurable_const.indicator
      (admissibleGrowingBarrierSet_measurable P U dens ε₀ Y hY a k₀ s)
  have hWick₁ : Measurable (fun q : Ω × ℂ =>
      admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) q.2 q.1) := by
    dsimp [admissibleLogWickWeight]
    have hfield : Measurable (fun q : Ω × ℂ =>
        (if b₁ then Y else Z) q.1 (Real.exp (-r)) q.2) := by
      cases b₁ with
      | false => exact hZ.measurableAtScale (Real.exp (-r))
      | true => exact hY.measurableAtScale (Real.exp (-r))
    have hv : Measurable (fun q : Ω × ℂ => gaussianVariance P
        (fun ω => (if b₁ then Y else Z) ω (Real.exp (-r)) q.2)) := by
      cases b₁ with
      | false =>
          exact hvar₁.comp measurable_snd
      | true =>
          exact hvar₁.comp measurable_snd
    fun_prop
  have hWick₂ : Measurable (fun q : Ω × ℂ =>
      admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) q.2 q.1) := by
    dsimp [admissibleLogWickWeight]
    have hfield : Measurable (fun q : Ω × ℂ =>
        (if b₂ then Y else Z) q.1 (Real.exp (-s)) q.2) := by
      cases b₂ with
      | false => exact hZ.measurableAtScale (Real.exp (-s))
      | true => exact hY.measurableAtScale (Real.exp (-s))
    have hv : Measurable (fun q : Ω × ℂ => gaussianVariance P
        (fun ω => (if b₂ then Y else Z) ω (Real.exp (-s)) q.2)) := by
      cases b₂ with
      | false =>
          exact hvar₂.comp measurable_snd
      | true =>
          exact hvar₂.comp measurable_snd
    fun_prop
  have hC : Measurable C := by
    dsimp [C]
    exact hWick₁.mul hbar₁
  have hD : Measurable D := by
    dsimp [D]
    exact hWick₂.mul hbar₂
  have hA : Measurable A := by
    dsimp [A]
    exact (ENNReal.measurable_ofReal.comp (f.continuous.measurable.comp measurable_snd)).mul hC
  have hB : Measurable B := by
    dsimp [B]
    exact (ENNReal.measurable_ofReal.comp (f.continuous.measurable.comp measurable_snd)).mul hD
  have hH : Measurable (Function.uncurry (fun ω x => Function.uncurry (H ω) x)) := by
    dsimp [H]
    have hproj₁ : Measurable (fun q : Ω × (ℂ × ℂ) => (q.1, q.2.1)) :=
      measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hproj₂ : Measurable (fun q : Ω × (ℂ × ℂ) => (q.1, q.2.2)) :=
      measurable_fst.prodMk (measurable_snd.comp measurable_snd)
    exact (hA.comp hproj₁).mul (hB.comp hproj₂)
  have hmass₁ (ω : Ω) :
      compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ r b₁ ω f =
        ∫⁻ x, A (ω, x) ∂μ := by
    change (∫⁻ x, ENNReal.ofReal (f x) *
      admissibleLogWickWeight P (if b₁ then Y else Z) γ (Real.exp (-r)) x ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ r)
        (fun _ => (1 : ℝ≥0∞)) (ω, x) ∂μ) = _
    simp only [A, C]
    apply lintegral_congr
    intro x
    ac_rfl
  have hmass₂ (ω : Ω) :
      compatibleGrowingBarrierTestMassENN P U dens Y Z γ a k₀ s b₂ ω f =
        ∫⁻ y, B (ω, y) ∂μ := by
    change (∫⁻ y, ENNReal.ofReal (f y) *
      admissibleLogWickWeight P (if b₂ then Y else Z) γ (Real.exp (-s)) y ω *
      Set.indicator (admissibleGrowingBarrierSet Y a k₀ s)
        (fun _ => (1 : ℝ≥0∞)) (ω, y) ∂μ) = _
    simp only [B, D]
    apply lintegral_congr
    intro y
    ac_rfl
  have hAsection (ω : Ω) : AEMeasurable (fun x => A (ω, x)) μ :=
    (hA.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hBsection (ω : Ω) : AEMeasurable (fun y => B (ω, y)) μ :=
    (hB.comp (measurable_const.prodMk measurable_id)).aemeasurable
  have hfactor (ω : Ω) :
      (∫⁻ x, A (ω, x) ∂μ) * (∫⁻ y, B (ω, y) ∂μ) =
        ∫⁻ x, ∫⁻ y, H ω x y ∂μ ∂μ := by
    symm
    exact lintegral_lintegral_mul (hAsection ω) (hBsection ω)
  have hHmeas : AEMeasurable (Function.uncurry (fun ω x => Function.uncurry (H ω) x))
      (P.prod (μ.prod μ)) := hH.aemeasurable
  have hcurried : AEMeasurable (Function.uncurry (fun ω p => H ω p.1 p.2))
      (P.prod (μ.prod μ)) := hHmeas
  have hswapOuter := lintegral_lintegral_swap
    (μ := P) (ν := μ.prod μ) (f := fun ω p => H ω p.1 p.2) hcurried
  have hHsection (ω : Ω) : AEMeasurable (fun p : ℂ × ℂ => H ω p.1 p.2)
      (μ.prod μ) :=
    (hH.comp (measurable_const.prodMk measurable_id)).aemeasurable
  calc
    _ = ∫⁻ ω, (∫⁻ x, A (ω, x) ∂μ) * (∫⁻ y, B (ω, y) ∂μ) ∂P := by
      apply lintegral_congr
      intro ω
      rw [hmass₁ ω, hmass₂ ω]
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, H ω x y ∂μ ∂μ ∂P := by
      apply lintegral_congr
      intro ω
      exact hfactor ω
    _ = ∫⁻ ω, ∫⁻ p : ℂ × ℂ, H ω p.1 p.2 ∂(μ.prod μ) ∂P := by
      apply lintegral_congr
      intro ω
      exact lintegral_lintegral (f := fun x y => H ω x y) (hHsection ω)
    _ = ∫⁻ p : ℂ × ℂ, ∫⁻ ω, H ω p.1 p.2 ∂P ∂(μ.prod μ) := hswapOuter
    _ = ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (f p.1 * f p.2) *
        compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel P Y Z γ a k₀ r s
          p.1 p.2 b₁ b₂ ∂(μ.prod μ) := by
      apply lintegral_congr
      intro p
      have hCsection : Measurable (fun ω : Ω => C (ω, p.1)) :=
        hC.comp (measurable_id.prodMk measurable_const)
      have hDsection : Measurable (fun ω : Ω => D (ω, p.2)) :=
        hD.comp (measurable_id.prodMk measurable_const)
      have hCD : AEMeasurable (fun ω => C (ω, p.1) * D (ω, p.2)) P :=
        (hCsection.mul hDsection).aemeasurable
      have hfactorF : ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2) =
          ENNReal.ofReal (f p.1 * f p.2) :=
        (ENNReal.ofReal_mul (hf p.1)).symm
      calc
        ∫⁻ ω, H ω p.1 p.2 ∂P =
            ∫⁻ ω, ENNReal.ofReal (f p.1 * f p.2) *
              (C (ω, p.1) * D (ω, p.2)) ∂P := by
          apply lintegral_congr
          intro ω
          calc
            H ω p.1 p.2 =
                (ENNReal.ofReal (f p.1) * ENNReal.ofReal (f p.2)) *
                  (C (ω, p.1) * D (ω, p.2)) := by
              dsimp [H, A, B]
              ac_rfl
            _ = ENNReal.ofReal (f p.1 * f p.2) *
                  (C (ω, p.1) * D (ω, p.2)) := by rw [hfactorF]
        _ = ENNReal.ofReal (f p.1 * f p.2) *
              (∫⁻ ω, C (ω, p.1) * D (ω, p.2) ∂P) :=
          lintegral_const_mul'' _ hCD
        _ = ENNReal.ofReal (f p.1 * f p.2) *
              compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel
                P Y Z γ a k₀ r s p.1 p.2 b₁ b₂ := by
            congr 1
            rw [compatibleAdmissibleSelectedMixedGrowingBarrierPairKernel]
            apply lintegral_congr
            intro ω
            dsimp [C, D]
            ac_rfl


end DOZZ.Proofs
