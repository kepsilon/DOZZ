/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTiltLimit
public import DOZZ.GMC.Construction.GMCGeneralTiltRawCutoff
public import DOZZ.GMC.Construction.GMCUniqueAe

/-! # Cameron–Martin tilt for the field, one cutoff chaos and the limit chaos

At a fixed radius the circle cutoff chaos is almost surely a measurable function of the test
field, through its countably many box coordinates. Combined with the finite-cutoff tilt, which
identifies the shifted coordinates, this reduces the joint tilt of the field, one cutoff chaos
and the limit chaos to the field/limit tilt `equatorGFF_GMC_tilt`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- Box coordinates of an arbitrary planar measure: total mass and rational lower-box masses. -/
noncomputable def gmcBoxEval (μ : Measure ℂ) : Option (ℚ × ℚ) → ℝ≥0∞ :=
  fun j => μ (gmcTiltCoordinateSet j)

theorem gmcTiltCoordinateSet_measurableSet (j : Option (ℚ × ℚ)) :
    MeasurableSet (gmcTiltCoordinateSet j) := by
  cases j with
  | none => exact MeasurableSet.univ
  | some i => exact gmcLowerBox_measurableSet i

theorem measurable_gmcBoxEval : Measurable gmcBoxEval := by
  rw [measurable_pi_iff]
  intro j
  exact Measure.measurable_coe (gmcTiltCoordinateSet_measurableSet j)

theorem gmcBoxEval_eq_finiteMeasureEval (μ : FiniteMeasure ℂ) :
    gmcBoxEval (μ : Measure ℂ) = gmcFiniteMeasureEval μ := by
  funext j
  cases j <;> rfl

/-- Weighting a measure by a fixed measurable density is a measurable operation. -/
theorem measurable_measure_withDensity (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    Measurable (fun μ : Measure ℂ => μ.withDensity w) := by
  refine Measure.measurable_of_measurable_coe _ (fun A hA => ?_)
  have hEq : (fun μ : Measure ℂ => μ.withDensity w A) =
      fun μ => ∫⁻ x, A.indicator w x ∂μ := by
    funext μ
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  rw [hEq]
  exact Measure.measurable_lintegral (hw.indicator hA)

/-- A measurable functional of a parameter and a finite measure factors measurably through the
parameter and the box coordinates of the measure. -/
theorem gmc_measurable_factor_finiteEval_param {α : Type*} [MeasurableSpace α]
    (H : α → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun p : α × Measure ℂ => H p.1 p.2)) :
    ∃ G : α × (Option (ℚ × ℚ) → ℝ≥0∞) → ℝ≥0∞, Measurable G ∧
      ∀ (a : α) (μ : FiniteMeasure ℂ), H a (μ : Measure ℂ) = G (a, gmcFiniteMeasureEval μ) := by
  let mA : MeasurableSpace α := inferInstance
  let mFM : MeasurableSpace (FiniteMeasure ℂ) := inferInstance
  let mCoord : MeasurableSpace (Option (ℚ × ℚ) → ℝ≥0∞) := MeasurableSpace.pi
  let j : α × FiniteMeasure ℂ → α × (Option (ℚ × ℚ) → ℝ≥0∞) :=
    fun p => (p.1, gmcFiniteMeasureEval p.2)
  have hSigma : MeasurableSpace.comap j (mA.prod mCoord) = mA.prod mFM := by
    rw [MeasurableSpace.comap_prodMk, MeasurableSpace.prod]
    rw [show mFM = MeasurableSpace.comap gmcFiniteMeasureEval mCoord from by
      simpa [mFM, mCoord] using gmcFiniteMeasure_sigma_eq]
    rw [MeasurableSpace.comap_comp]
    rfl
  have hInput : Measurable (fun p : α × FiniteMeasure ℂ => (p.1, (p.2 : Measure ℂ))) :=
    Measurable.prodMk measurable_fst (measurable_subtype_coe.comp measurable_snd)
  have hPull : Measurable (fun p : α × FiniteMeasure ℂ => H p.1 (p.2 : Measure ℂ)) :=
    hH.comp hInput
  have hPull' : @Measurable (α × FiniteMeasure ℂ) ℝ≥0∞
      (MeasurableSpace.comap j (mA.prod mCoord)) _
      (fun p => H p.1 (p.2 : Measure ℂ)) := by
    rw [hSigma]
    exact hPull
  obtain ⟨G, hG, hGfactor⟩ := hPull'.exists_eq_measurable_comp
  exact ⟨G, hG, fun a μ => congrFun hGfactor (a, μ)⟩

/-- A measurable functional of a parameter and two finite measures factors measurably through
the parameter and the box coordinates of both measures. -/
theorem gmc_measurable_factor_two_finiteEval {α : Type*} [MeasurableSpace α]
    (H : α → Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : α × Measure ℂ × Measure ℂ => H q.1 q.2.1 q.2.2)) :
    ∃ G : α × (Option (ℚ × ℚ) → ℝ≥0∞) × (Option (ℚ × ℚ) → ℝ≥0∞) → ℝ≥0∞, Measurable G ∧
      ∀ (a : α) (μ ν : FiniteMeasure ℂ),
        H a (μ : Measure ℂ) (ν : Measure ℂ) =
          G (a, gmcFiniteMeasureEval μ, gmcFiniteMeasureEval ν) := by
  have hH₁ : Measurable (fun q : (α × Measure ℂ) × Measure ℂ => H q.1.1 q.1.2 q.2) :=
    hH.comp (f := fun q : (α × Measure ℂ) × Measure ℂ => (q.1.1, q.1.2, q.2)) (by fun_prop)
  obtain ⟨G₁, hG₁, hfac₁⟩ := gmc_measurable_factor_finiteEval_param
    (α := α × Measure ℂ) (fun p ν => H p.1 p.2 ν) hH₁
  have hH₂ : Measurable (fun q : (α × (Option (ℚ × ℚ) → ℝ≥0∞)) × Measure ℂ =>
      G₁ ((q.1.1, q.2), q.1.2)) :=
    hG₁.comp (f := fun q : (α × (Option (ℚ × ℚ) → ℝ≥0∞)) × Measure ℂ =>
      ((q.1.1, q.2), q.1.2)) (by fun_prop)
  obtain ⟨G₂, hG₂, hfac₂⟩ := gmc_measurable_factor_finiteEval_param
    (α := α × (Option (ℚ × ℚ) → ℝ≥0∞)) (fun p μ => G₁ ((p.1, μ), p.2)) hH₂
  refine ⟨fun q => G₂ ((q.1, q.2.2), q.2.1),
    hG₂.comp (f := fun q : α × (Option (ℚ × ℚ) → ℝ≥0∞) × (Option (ℚ × ℚ) → ℝ≥0∞) =>
      ((q.1, q.2.2), q.2.1)) (by fun_prop), ?_⟩
  intro a μ ν
  have h₁ : H a (μ : Measure ℂ) (ν : Measure ℂ) =
      G₁ ((a, (μ : Measure ℂ)), gmcFiniteMeasureEval ν) := hfac₁ (a, (μ : Measure ℂ)) ν
  have h₂ : G₁ ((a, (μ : Measure ℂ)), gmcFiniteMeasureEval ν) =
      G₂ ((a, gmcFiniteMeasureEval ν), gmcFiniteMeasureEval μ) :=
    hfac₂ (a, gmcFiniteMeasureEval ν) μ
  rw [h₁, h₂]

/-- The box coordinates of a fixed-radius circle cutoff are almost surely a measurable function
of the test field. -/
theorem regularizedGMC_boxEval_field_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ) :
    ∃ E : (TestFn → ℝ) → (Option (ℚ × ℚ) → ℝ≥0∞), Measurable E ∧
      ∀ᵐ ω ∂P, gmcBoxEval (regularizedGMC P Xc γ r ω) = E (fun f => X ω f) := by
  obtain ⟨Xr, hXr, hRaw⟩ := exists_raw_equatorGFF_circle_average_witness X hX
  have hMeas := regularizedGMC_raw_measurable_of_joint P X hX Xr hXr γ r (hRaw r)
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  have hComap : Measurable[(MeasurableSpace.pi).comap eval]
      (fun ω => gmcBoxEval (regularizedGMC P Xr γ r ω)) :=
    @Measurable.comp Ω (Measure ℂ) (Option (ℚ × ℚ) → ℝ≥0∞)
      (equatorGFFRawDistributionSigma X) _ _ gmcBoxEval _ measurable_gmcBoxEval hMeas
  obtain ⟨E, hE, hfac⟩ := hComap.exists_eq_measurable_comp
  refine ⟨E, hE, ?_⟩
  filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX Xc Xr hXc hXr γ r] with ω hω
  rw [hω]
  exact congrFun hfac ω

/-- Under the Cameron–Martin shift the field proxy of the cutoff box coordinates computes the
coordinates of the tilted cutoff chaos, which is moreover almost surely finite. -/
theorem regularizedGMC_tilted_boxEval_field_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (E : (TestFn → ℝ) → (Option (ℚ × ℚ) → ℝ≥0∞)) (hE : Measurable E)
    (hEae : ∀ᵐ ω ∂P, gmcBoxEval (regularizedGMC P Xc γ r ω) = E (fun f => X ω f)) :
    ∀ᵐ ω ∂P,
      gmcBoxEval ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L)))) =
        E (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L) ∧
      (regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L))) Set.univ ≠ ⊤ := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  let S : Set ((TestFn → ℝ) × Measure ℂ) :=
    {q | gmcBoxEval q.2 = E q.1} ∩ {q | q.2 Set.univ ≠ ⊤}
  have hS : MeasurableSet S := by
    refine (measurableSet_eq_fun (measurable_gmcBoxEval.comp measurable_snd)
      (hE.comp measurable_fst)).inter ?_
    exact (measurableSet_singleton ⊤).compl.preimage
      ((Measure.measurable_coe MeasurableSet.univ).comp measurable_snd)
  let H₀ : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun φ μ => Sᶜ.indicator 1 (φ, μ)
  have hH₀ : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H₀ q.1 q.2) :=
    measurable_one.indicator hS.compl
  have hTilt := equatorGFF_tilted_test_regularizedGMC_cutoff_lintegral
    P X hX Xc hXc γ r L hL H₀ hH₀
  have hLeftZero : (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
      H₀ (fun f => X ω f) (regularizedGMC P Xc γ r ω) ∂P) = 0 := by
    rw [lintegral_eq_zero_iff']
    · filter_upwards [hEae, regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω hfin
      have hmem : ((fun f => X ω f), regularizedGMC P Xc γ r ω) ∈ S :=
        ⟨hω, measure_ne_top _ _⟩
      simp [H₀, Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]
    · have hfield : Measurable (fun ω => fun f : TestFn => X ω f) :=
        measurable_pi_iff.mpr (fun f => (hX.2 f).1)
      have hden : AEMeasurable
          (fun ω => ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2))) P :=
        ((Real.measurable_exp.comp_aemeasurable
          (hL.1.aestronglyMeasurable.aemeasurable.sub_const _))).ennreal_ofReal
      exact hden.mul (hH₀.comp (hfield.prodMk
        (regularizedGMC_measurable P X hX Xc hXc γ r))).aemeasurable
  rw [hLeftZero] at hTilt
  have hRightMeas : Measurable (fun ω => H₀
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L))))) := by
    have hshift : Measurable (fun ω => fun f : TestFn =>
        X ω f + gaussianCovariance P (fun ω' => X ω' f) L) :=
      measurable_pi_iff.mpr (fun f => (hX.2 f).1.add_const _)
    have hcovCont : Continuous (fun x : ℂ =>
        gaussianCovariance P (fun ω' => Xc ω' x r) L) :=
      continuous_gaussianCovariance_circle_of_IsGaussianL2Limit P X hX Xc hXc L hL r
    have hw : Measurable (fun x : ℂ => ENNReal.ofReal
        (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (hcovCont.measurable.const_mul γ))
    exact hH₀.comp (hshift.prodMk ((measurable_measure_withDensity _ hw).comp
      (regularizedGMC_measurable P X hX Xc hXc γ r)))
  have hZero := (lintegral_eq_zero_iff hRightMeas).mp hTilt.symm
  filter_upwards [hZero] with ω hω
  have hmem : ((fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L),
      (regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
        (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L)))) ∈ S := by
    by_contra hnot
    have hone : H₀ (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal
          (Real.exp (γ * gaussianCovariance P (fun ω' => Xc ω' x r) L)))) = 1 := by
      simp [H₀, Set.indicator_of_mem (Set.mem_compl hnot)]
    have h0 := hω
    simp only [Pi.zero_apply] at h0
    rw [h0] at hone
    exact zero_ne_one hone
  exact hmem

/-- Weighting a finite measure by the exponential of a bounded continuous function keeps it
finite. -/
theorem isFiniteMeasure_withDensity_exp_bcf (μ : Measure ℂ) [IsFiniteMeasure μ]
    (γ : ℝ) (c : BoundedContinuousFunction ℂ ℝ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) := by
  apply isFiniteMeasure_withDensity
  have hpoint : ∀ x, ENNReal.ofReal (Real.exp (γ * c x)) ≤
      ENNReal.ofReal (Real.exp (|γ| * ‖c‖)) := by
    intro x
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    calc γ * c x ≤ |γ * c x| := le_abs_self _
      _ = |γ| * |c x| := abs_mul _ _
      _ ≤ |γ| * ‖c‖ := by
        gcongr
        exact (Real.norm_eq_abs (c x)).symm.le.trans (c.norm_coe_le_norm x)
  have hbound : (∫⁻ x, ENNReal.ofReal (Real.exp (γ * c x)) ∂μ) ≤
      ENNReal.ofReal (Real.exp (|γ| * ‖c‖)) * μ Set.univ :=
    (lintegral_mono hpoint).trans (lintegral_const _).le
  exact ne_of_lt (lt_of_le_of_lt hbound
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)))

/-- Cameron–Martin for joint functionals of the test coordinates, one cutoff chaos and the limit
chaos: tilting by `L` multiplies the cutoff chaos by `exp (γ Cov(X_r(x), L))` and the limit chaos
by `exp (γ c)`. With `L = γ X_r(u)` and Tonelli this gives finite-cutoff rooting. -/
theorem equatorGFF_GMC_tilt_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x r) L) c atTop)
    (r : ℝ) (H : (TestFn → ℝ) → Measure ℂ → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ × Measure ℂ =>
      H q.1 q.2.1 q.2.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (regularizedGMC P Xc γ r ω) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω => Xc ω x r) L))))
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P := by
  classical
  obtain ⟨G, hG, hGfac⟩ := gmc_measurable_factor_two_finiteEval H hH
  obtain ⟨E, hE, hEae⟩ := regularizedGMC_boxEval_field_proxy P X hX Xc hXc γ r
  let H' : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun φ μ => G (φ, E φ, gmcBoxEval μ)
  have hH' : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H' q.1 q.2) :=
    hG.comp (measurable_fst.prodMk ((hE.comp measurable_fst).prodMk
      (measurable_gmcBoxEval.comp measurable_snd)))
  have htilt := equatorGFF_GMC_tilt P X hX γ hγ hγ2 M hM Xc hXc L hL c hc H' hH'
  have hShift := regularizedGMC_tilted_boxEval_field_proxy P X hX Xc hXc γ r L hL E hE hEae
  have hMfin : ∀ ω, IsFiniteMeasure (M ω) := hM.1
  have hleft : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
          H (fun f => X ω f) (regularizedGMC P Xc γ r ω) (M ω) =
        ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
          H' (fun f => X ω f) (M ω) := by
    filter_upwards [hEae, regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω hfin
    congr 1
    have h1 : H (fun f => X ω f) (regularizedGMC P Xc γ r ω) (M ω) =
        G ((fun f => X ω f), gmcFiniteMeasureEval ⟨regularizedGMC P Xc γ r ω, hfin⟩,
          gmcFiniteMeasureEval ⟨M ω, hMfin ω⟩) :=
      hGfac (fun f => X ω f) ⟨regularizedGMC P Xc γ r ω, hfin⟩ ⟨M ω, hMfin ω⟩
    have e1 : gmcFiniteMeasureEval ⟨regularizedGMC P Xc γ r ω, hfin⟩ =
        E (fun f => X ω f) := by
      rw [← hω]
      exact (gmcBoxEval_eq_finiteMeasureEval _).symm
    have e2 : gmcFiniteMeasureEval ⟨M ω, hMfin ω⟩ = gmcBoxEval (M ω) :=
      (gmcBoxEval_eq_finiteMeasureEval _).symm
    rw [h1, e1, e2]
  have hright : ∀ᵐ ω ∂P,
      H' (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
          ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) =
        H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
          ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal (Real.exp
            (γ * gaussianCovariance P (fun ω => Xc ω x r) L))))
          ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) := by
    filter_upwards [hShift] with ω hω
    have hfinR : IsFiniteMeasure ((regularizedGMC P Xc γ r ω).withDensity
        (fun x => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω => Xc ω x r) L)))) := ⟨hω.2.lt_top⟩
    have hfinM : IsFiniteMeasure ((M ω).withDensity
        (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) := by
      have := hMfin ω
      exact isFiniteMeasure_withDensity_exp_bcf (M ω) γ c
    have h1 : H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
        ((regularizedGMC P Xc γ r ω).withDensity (fun x => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω => Xc ω x r) L))))
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) =
        G ((fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L),
          gmcFiniteMeasureEval ⟨_, hfinR⟩, gmcFiniteMeasureEval ⟨_, hfinM⟩) :=
      hGfac (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L) ⟨_, hfinR⟩ ⟨_, hfinM⟩
    have e1 : gmcFiniteMeasureEval ⟨_, hfinR⟩ =
        E (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L) := by
      rw [← hω.1]
      exact (gmcBoxEval_eq_finiteMeasureEval _).symm
    have e2 : gmcFiniteMeasureEval ⟨_, hfinM⟩ =
        gmcBoxEval ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) :=
      (gmcBoxEval_eq_finiteMeasureEval _).symm
    rw [h1, e1, e2]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
          H' (fun f => X ω f) (M ω) ∂P := lintegral_congr_ae hleft
    _ = ∫⁻ ω, H' (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
          ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P := htilt
    _ = _ := lintegral_congr_ae hright

end DOZZ.Proofs
