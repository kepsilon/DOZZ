/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.CovarianceSymmetry
public import DOZZ.Brownian.Lateral.LocalIntensity
public import DOZZ.GMC.Moments.AffineVolume
public import DOZZ.GMC.Moments.InversionSpatialLaw
public import DOZZ.GMC.Moments.ChaosLawFDDLimit

/-! Dilation transport for the actual radial-removed chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open DOZZ.Assembly
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Exact dilation change of variables for the full flat lateral planar reference. -/
theorem lintegral_flatLateralReference_dilation
    (c : ℝ) (hc : 0 < c) (f : ℂ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f (c * x) ∂(volume : Measure ℂ).withDensity
      (fun x => ENNReal.ofReal (originLateralPlaneDensity x))) =
    ∫⁻ x, f x ∂(volume : Measure ℂ).withDensity
      (fun x => ENNReal.ofReal (originLateralPlaneDensity x)) := by
  let d : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (originLateralPlaneDensity x)
  have hd : Measurable d := by
    dsimp [d, originLateralPlaneDensity]
    fun_prop
  have hm : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hdc (x : ℂ) : ENNReal.ofReal (c ^ 2) * d (c * x) = d x := by
    dsimp [d]
    rw [originLateralPlaneDensity_dilation c hc,
      Real.rpow_neg hc.le, Real.rpow_two,
      ← ENNReal.ofReal_mul (sq_nonneg c)]
    congr 1
    rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'), one_mul]
  have hv : (volume : Measure ℂ).map (fun x : ℂ => (c : ℂ) * x) =
      ENNReal.ofReal ((c ^ 2)⁻¹) • volume := by
    simpa only [Complex.real_smul, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hc))] using
      complexVolume_map_smul hc.ne'
  have hfc : Measurable (fun x : ℂ => f (c * x)) := hf.comp hm
  change (∫⁻ x, f (c * x) ∂(volume : Measure ℂ).withDensity d) =
    ∫⁻ x, f x ∂(volume : Measure ℂ).withDensity d
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hfc,
    lintegral_withDensity_eq_lintegral_mul _ hd hf]
  change (∫⁻ x : ℂ, d x * f (c * x)) = ∫⁻ x : ℂ, d x * f x
  have hprod : Measurable (fun x : ℂ => d (c * x) * f (c * x)) :=
    (hd.comp hm).mul hfc
  have hdf : Measurable (fun x : ℂ => d x * f x) := hd.mul hf
  calc
    (∫⁻ x : ℂ, d x * f (c * x)) =
        ENNReal.ofReal (c ^ 2) * ∫⁻ x : ℂ, d (c * x) * f (c * x) := by
      rw [← lintegral_const_mul _ hprod]
      apply lintegral_congr
      intro x
      rw [← mul_assoc, hdc]
    _ = ENNReal.ofReal (c ^ 2) * ∫⁻ x : ℂ, d x * f x
        ∂(volume : Measure ℂ).map (fun x : ℂ => (c : ℂ) * x) := by
      rw [lintegral_map hdf hm]
    _ = ∫⁻ x : ℂ, d x * f x := by
      rw [hv, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
        ← ENNReal.ofReal_mul (sq_nonneg c),
        mul_inv_cancel₀ (pow_ne_zero 2 hc.ne'), ENNReal.ofReal_one, one_mul]

/-- The flat planar reference is a measure-preserving dilation measure. -/
theorem flatLateralReference_dilation (c : ℝ) (hc : 0 < c) :
    ((volume : Measure ℂ).withDensity
      (fun x => ENNReal.ofReal (originLateralPlaneDensity x))).map (fun x : ℂ => c * x) =
      (volume : Measure ℂ).withDensity
        (fun x => ENNReal.ofReal (originLateralPlaneDensity x)) := by
  apply Measure.ext
  intro S hS
  have h := lintegral_flatLateralReference_dilation c hc (S.indicator (1 : ℂ → ℝ≥0∞))
    (measurable_const.indicator hS)
  have hm : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have he := lintegral_map (μ := (volume : Measure ℂ).withDensity
    (fun x => ENNReal.ofReal (originLateralPlaneDensity x)))
    (g := fun x : ℂ => (c : ℂ) * x) (f := S.indicator (1 : ℂ → ℝ≥0∞))
    ((measurable_const : Measurable (1 : ℂ → ℝ≥0∞)).indicator hS) hm
  rw [← he] at h
  simpa only [lintegral_indicator_one hS] using h

/-- Chart restriction commutes with dilation of the flat reference measure. -/
theorem originLateralReference_dilation (ρ c : ℝ) (hc : 0 < c) :
    (logRegularizationReference (originLateralChart ρ) originLateralPlaneDensity).map
      (fun x : ℂ => (c : ℂ) * x) =
    logRegularizationReference (originLateralChart (c * ρ)) originLateralPlaneDensity := by
  have hm : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hs := (isOpen_originLateralChart (c * ρ)).measurableSet
  have he : (fun x : ℂ => (c : ℂ) * x) ⁻¹' originLateralChart (c * ρ) =
      originLateralChart ρ := by
    ext x
    exact originLateralChart_dilation_mem ρ c hc x
  unfold logRegularizationReference
  rw [← restrict_withDensity (isOpen_originLateralChart ρ).measurableSet,
    ← restrict_withDensity hs]
  calc
    _ = (((volume : Measure ℂ).withDensity
        (fun x => ENNReal.ofReal (originLateralPlaneDensity x))).map
          (fun x : ℂ => (c : ℂ) * x)).restrict (originLateralChart (c * ρ)) := by
      rw [Measure.restrict_map hm hs, he]
    _ = _ := by rw [flatLateralReference_dilation c hc]

/-- The reference transport is a measure-preserving map between the two charts. -/
theorem originLateralReference_measurePreserving_dilation (ρ c : ℝ) (hc : 0 < c) :
    MeasurePreserving (fun x : ℂ => (c : ℂ) * x)
      (logRegularizationReference (originLateralChart ρ) originLateralPlaneDensity)
      (logRegularizationReference (originLateralChart (c * ρ)) originLateralPlaneDensity) :=
  ⟨by fun_prop, originLateralReference_dilation ρ c hc⟩

/-- Extending a chart cutoff by zero preserves the dilation finite-dimensional law on the
whole plane. This permits spatial-law transfer against a finite compact reference. -/
theorem originLateralCircleRegularization_dilation_zeroed_fdd_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ c ε : ℝ) (hρ : 0 < ρ) (hcpos : 0 < c) (hε : 0 < ε) (hερ : ε ≤ ρ)
    (K : Set ℂ) (hKU : K ⊆ originLateralChart ρ) (n : ℕ) (xs : Fin n → ℂ) :
    P.map (fun ω i => K.indicator
      (fun x => originLateralCircleRegularization Xc (c * ρ) ω (c * ε) (c * x)) (xs i)) =
    P.map (fun ω i => K.indicator
      (fun x => originLateralCircleRegularization Xc ρ ω ε x) (xs i)) := by
  classical
  let x₀ : ℂ := (3 * ρ : ℝ)
  have hx₀ : x₀ ∈ originLateralChart ρ := by
    change 2 * ρ < ‖((3 * ρ : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hρ)]
    linarith
  let ys : Fin n → ℂ := fun i => if xs i ∈ K then xs i else x₀
  have hys i : ys i ∈ originLateralChart ρ := by
    dsimp [ys]
    split
    · exact hKU ‹xs i ∈ K›
    · exact hx₀
  let mask : (Fin n → ℝ) → (Fin n → ℝ) := fun u i => if xs i ∈ K then u i else 0
  have hmask : Measurable mask := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [mask]
    split
    · exact measurable_pi_apply i
    · exact measurable_const
  have hmy : Measurable (fun ω i =>
      originLateralCircleRegularization Xc (c * ρ) ω (c * ε) (c * ys i)) :=
    measurable_pi_iff.mpr fun i =>
      (originLateralCircleRegularization_measurableAtScale Xc hm (c * ρ)
        (mul_pos hcpos hρ) (c * ε)).comp (measurable_id.prodMk measurable_const)
  have hmx : Measurable (fun ω i => originLateralCircleRegularization Xc ρ ω ε (ys i)) :=
    measurable_pi_iff.mpr fun i =>
      (originLateralCircleRegularization_measurableAtScale Xc hm ρ hρ ε).comp
        (measurable_id.prodMk measurable_const)
  have h := congrArg (fun μ => μ.map mask)
    (originLateralCircleRegularization_dilation_fdd_law P X Xc hX hc hm
      ρ c ε hρ hcpos hε hερ n ys hys)
  rw [Measure.map_map hmask hmy, Measure.map_map hmask hmx] at h
  convert h using 1
  · congr 1
    funext ω i
    by_cases hi : xs i ∈ K <;> simp [mask, ys, hi]
  · congr 1
    funext ω i
    by_cases hi : xs i ∈ K <;> simp [mask, ys, hi]

/-- Transport of the actual cutoff integral, with the exact scaled cutoff radius and
reference Jacobian. It does not assert equality of source and transformed samples. -/
theorem originLateralCutoff_dilation_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (ρ c : ℝ) (hc : 0 < c) (γ r : ℝ)
    (ω : Ω) (f : BoundedContinuousFunction ℂ ℝ) :
    regularizedLogChaosTestMass P (originLateralChart (c * ρ)) originLateralPlaneDensity
      (originLateralCircleRegularization Xc (c * ρ)) γ (r - Real.log c) ω f =
    ∫ x, f (c * x) * Real.exp
      (γ * originLateralCircleRegularization Xc (c * ρ) ω (c * Real.exp (-r)) (c * x) -
        γ ^ 2 / 2 * gaussianVariance P (fun η =>
          originLateralCircleRegularization Xc (c * ρ) η (c * Real.exp (-r)) (c * x)))
      ∂logRegularizationReference (originLateralChart ρ) originLateralPlaneDensity := by
  have hcn : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hm : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have he : MeasurableEmbedding (fun x : ℂ => (c : ℂ) * x) :=
    hm.measurableEmbedding (fun _ _ h => mul_left_cancel₀ hcn h)
  have hexp : Real.exp (-(r - Real.log c)) = c * Real.exp (-r) := by
    have ha : -(r - Real.log c) = Real.log c + -r := by ring
    rw [ha, Real.exp_add, Real.exp_log hc]
  unfold regularizedLogChaosTestMass
  rw [hexp]
  have h := ((originLateralReference_measurePreserving_dilation ρ c hc).integral_comp he
    (fun x => f x * Real.exp (γ * originLateralCircleRegularization Xc (c * ρ) ω
      (c * Real.exp (-r)) x - γ ^ 2 / 2 * gaussianVariance P (fun η =>
        originLateralCircleRegularization Xc (c * ρ) η (c * Real.exp (-r)) x)))).symm
  simpa only [gaussianVariance, gaussianCovariance, pow_two] using h

/-- Every finite compact test vector of the actual lateral Wick cutoffs has the exact
spatial dilation law, with the transformed cutoff radius kept explicit. -/
theorem originLateralCutoff_dilation_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ c : ℝ) (hρ : 0 < ρ) (hcpos : 0 < c) (γ r : ℝ)
    (hr : Real.exp (-r) ≤ min ρ 1)
    (hrc : c * Real.exp (-r) ≤ min (c * ρ) 1)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ)
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hzero : ∀ j x, x ∉ K → f j (c * x) = 0) :
    P.map (fun ω j => regularizedLogChaosTestMass P (originLateralChart (c * ρ))
      originLateralPlaneDensity (originLateralCircleRegularization Xc (c * ρ))
      γ (r - Real.log c) ω (f j)) =
    P.map (fun ω j => regularizedLogChaosTestMass P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω
      ((f j).compContinuous ⟨fun x : ℂ => (c : ℂ) * x, by fun_prop⟩)) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let U := originLateralChart ρ
  let V := originLateralChart (c * ρ)
  let Y := originLateralCircleRegularization Xc ρ
  let Z := originLateralCircleRegularization Xc (c * ρ)
  let ε := Real.exp (-r)
  let ν : Measure ℂ := (logRegularizationReference U originLateralPlaneDensity).restrict K
  have hY := originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ
  have hZ := originLateralCircleRegularization_admissible P X Xc hX hc hm
    (c * ρ) (mul_pos hcpos hρ)
  have hKmeas := hK.measurableSet
  have hν : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    dsimp only [ν]
    rw [Measure.restrict_apply_univ]
    exact (admissible_logRegularization_reference_measure_ne_top P U originLateralPlaneDensity
      (min ρ 1) Y hY K hK hKU).lt_top
  let : IsFiniteMeasure ν := hν
  let νf : FiniteMeasure ℂ := ⟨ν, hν⟩
  let variance : ℂ → ℝ := fun x => gaussianVariance P (fun ω => Y ω ε x)
  have hv : Measurable variance :=
    admissibleLogRegularization_variance_measurable P U originLateralPlaneDensity
      (min ρ 1) Y hY ε
  let W : Ω → ℂ → ℝ := fun ω x => K.indicator (fun x => Y ω ε x) x
  let W' : Ω → ℂ → ℝ := fun ω x => K.indicator (fun x => Z ω (c * ε) (c * x)) x
  have hW : Measurable (fun p : Ω × ℂ => W p.1 p.2) := by
    exact (hY.measurableAtScale ε).indicator (hKmeas.preimage measurable_snd)
  have harg : Measurable (fun p : Ω × ℂ => (p.1, (c : ℂ) * p.2)) :=
    measurable_fst.prodMk (measurable_const.mul measurable_snd)
  have hZs : Measurable (fun p : Ω × ℂ => Z p.1 (c * ε) (c * p.2)) :=
    (hZ.measurableAtScale (c * ε)).comp harg
  have hW' : Measurable (fun p : Ω × ℂ => W' p.1 p.2) :=
    hZs.indicator (hKmeas.preimage measurable_snd)
  let z : Fin m → ℂ → ℝ → ℝ := fun j x t => f j (c * x) *
    Real.exp (γ * t - γ ^ 2 / 2 * variance x)
  have hz j : Measurable (fun p : ℂ × ℝ => z j p.1 p.2) := by
    dsimp [z]
    fun_prop
  have hiW j : ∀ᵐ ω ∂P, Integrable (fun x => z j x (W ω x)) ν := by
    have hi := admissibleCutoff_integrand_integrable_ae P U originLateralPlaneDensity
      (min ρ 1) Y hY K hK hKU γ r hr ‖f j‖ (fun x => f j (c * x))
      (by fun_prop) (fun x => by simpa only [← Real.norm_eq_abs] using (f j).norm_coe_le_norm (c * x))
      (hzero j)
    filter_upwards [hi] with ω hω
    apply hω.restrict.congr
    filter_upwards [ae_restrict_mem hKmeas] with x hx
    simp only [z, W, indicator_of_mem hx, variance, ε, gaussianVariance,
      gaussianCovariance, pow_two]
  let scale : ℂ → ℂ := fun x => (c : ℂ) * x
  have hscale : Measurable scale := by fun_prop
  have hcn : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hinj : Function.Injective scale := fun _ _ h => mul_left_cancel₀ hcn h
  have hemb : MeasurableEmbedding scale := hscale.measurableEmbedding hinj
  have hsK : IsCompact (scale '' K) := hK.image (by fun_prop)
  have hsKU : scale '' K ⊆ V := by
    rintro x ⟨y, hy, rfl⟩
    exact (originLateralChart_dilation_mem ρ c hcpos y).mpr (hKU hy)
  have hzerotarget j x (hx : x ∉ scale '' K) : f j x = 0 := by
    let y : ℂ := (c : ℂ)⁻¹ * x
    have hxy : scale y = x := by
      dsimp [scale, y]
      rw [← mul_assoc, mul_inv_cancel₀ hcn, one_mul]
    have hy : y ∉ K := fun hy => hx ⟨y, hy, hxy⟩
    simpa only [← hxy] using hzero j y hy
  have hexp : Real.exp (-(r - Real.log c)) = c * ε := by
    have ha : -(r - Real.log c) = Real.log c + -r := by ring
    rw [ha, Real.exp_add, Real.exp_log hcpos]
  have hiW' j : ∀ᵐ ω ∂P, Integrable (fun x => z j x (W' ω x)) ν := by
    have hi := admissibleCutoff_integrand_integrable_ae P V originLateralPlaneDensity
      (min (c * ρ) 1) Z hZ (scale '' K) hsK hsKU γ (r - Real.log c)
      (by rw [hexp]; exact hrc) ‖f j‖ (f j) (f j).continuous.measurable
      (fun x => by simpa only [← Real.norm_eq_abs] using (f j).norm_coe_le_norm x)
      (hzerotarget j)
    filter_upwards [hi] with ω hω
    rw [hexp] at hω
    rw [← originLateralReference_dilation ρ c hcpos] at hω
    have hipull := hemb.integrable_map_iff.mp hω
    apply hipull.restrict.congr
    filter_upwards [ae_restrict_mem hKmeas] with x hx
    dsimp only [Function.comp_apply, scale]
    have hvx := originLateralCircleRegularization_dilation_variance P X Xc hX hc hm
      ρ c ε hρ hcpos (Real.exp_pos _) (hr.trans (min_le_left _ _)) x (hKU hx)
    have hvraw : (∫ η, Z η (c * ε) (c * x) ^ 2 ∂P) =
        gaussianVariance P (fun η => Y η ε x) := by
      simpa only [gaussianVariance, gaussianCovariance, pow_two] using hvx
    simp only [z, W', indicator_of_mem hx, variance]
    rw [hvraw]
  have hfdd (n : ℕ) (xs : Fin n → ℂ) : P.map (fun ω i => W ω (xs i)) =
      P.map (fun ω i => W' ω (xs i)) :=
    (originLateralCircleRegularization_dilation_zeroed_fdd_law P X Xc hX hc hm
      ρ c ε hρ hcpos (Real.exp_pos _) (hr.trans (min_le_left _ _)) K hKU n xs).symm
  have hlaw := spatialIntegral_vector_law_of_fdd_finite νf W W' z hW hW' hz hiW hiW' hfdd
  have hleft ω j : (∫ x, z j x (W ω x) ∂ν) =
      regularizedLogChaosTestMass P U originLateralPlaneDensity Y γ r ω
        ((f j).compContinuous ⟨scale, by fun_prop⟩) := by
    dsimp only [ν]
    rw [← integral_indicator hKmeas]
    unfold regularizedLogChaosTestMass
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ K
      · simp [W, z, variance, ε, scale, hx, BoundedContinuousFunction.compContinuous_apply,
          gaussianVariance, gaussianCovariance, pow_two]
      · simp [hx, hzero j x hx, BoundedContinuousFunction.compContinuous_apply, scale]
  have hright ω j : (∫ x, z j x (W' ω x) ∂ν) =
      regularizedLogChaosTestMass P V originLateralPlaneDensity Z γ (r - Real.log c) ω (f j) := by
    rw [originLateralCutoff_dilation_integral P Xc ρ c hcpos γ r ω (f j)]
    dsimp only [ν]
    rw [← integral_indicator hKmeas]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ K
      · simp only [indicator_of_mem hx, W', z, variance]
        rw [originLateralCircleRegularization_dilation_variance P X Xc hX hc hm
          ρ c ε hρ hcpos (Real.exp_pos _) (hr.trans (min_le_left _ _)) x (hKU hx)]
      · simp only [indicator_of_notMem hx, z, hzero j x hx, zero_mul]
  change P.map (fun ω j => ∫ x, z j x (W ω x) ∂ν) =
    P.map (fun ω j => ∫ x, z j x (W' ω x) ∂ν) at hlaw
  simp_rw [hleft, hright] at hlaw
  exact hlaw.symm

/-- Compact tests of the actual radial-removed measure are limits of its actual lateral Wick
cutoffs. The local independent chaos is used only through its proved identification. -/
theorem originRadialRemovedGMC_test_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ) :
    TendstoInMeasure P
      (fun r ω => regularizedLogChaosTestMass P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ r ω f) atTop
      (fun ω => ∫ x, f x ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  obtain ⟨N, hN, _, hid⟩ := exists_originLateralChartGMC_radial_removed_identity
    P X Xc hX hc hm hcont ρ γ hρ hγ hγ2 M hM
  apply TendstoInMeasure.congr_right _ (hN.2.2.2 f hfc hfU)
  filter_upwards [hid] with ω hω
  rw [hω, ← integral_indicator (isOpen_originLateralChart ρ).measurableSet]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ originLateralChart ρ
    · exact indicator_of_mem hx _
    · have hzero : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hf => hx (hfU hf))
      simp only [indicator_of_notMem hx, hzero]

/-- The exact dilation law of every finite compact test vector passes to the actual
radial-removed GMC on the original probability space. -/
theorem originRadialRemovedGMC_dilation_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ c γ : ℝ) (hρ : 0 < ρ) (hcpos : 0 < c) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ originLateralChart ρ)
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfV : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ originLateralChart (c * ρ))
    (hzero : ∀ j x, x ∉ K → f j (c * x) = 0)
    (hgc : ∀ j, HasCompactSupport (fun x : ℂ => f j (c * x)))
    (hgU : ∀ j, tsupport (fun x : ℂ => f j (c * x)) ⊆ originLateralChart ρ) :
    P.map (fun ω j => ∫ x, f j x
      ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) =
    P.map (fun ω j => ∫ x, f j (c * x)
      ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  let : IsProbabilityMeasure P := hX.1
  let g : Fin m → BoundedContinuousFunction ℂ ℝ := fun j =>
    (f j).compContinuous ⟨fun x : ℂ => (c : ℂ) * x, by fun_prop⟩
  let T := fun r ω j => regularizedLogChaosTestMass P (originLateralChart (c * ρ))
    originLateralPlaneDensity (originLateralCircleRegularization Xc (c * ρ)) γ r ω (f j)
  let S := fun r ω j => regularizedLogChaosTestMass P (originLateralChart ρ)
    originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω (g j)
  have hA := originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ
  have hB := originLateralCircleRegularization_admissible P X Xc hX hc hm
    (c * ρ) (mul_pos hcpos hρ)
  have hmT r j : Measurable (fun ω => T r ω j) :=
    admissibleCutoffIntegral_measurable P _ _ _ _ hB γ r (f j) (f j).continuous.measurable
  have hmS r j : Measurable (fun ω => S r ω j) :=
    admissibleCutoffIntegral_measurable P _ _ _ _ hA γ r (g j) (g j).continuous.measurable
  have heps : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  have hbound : 0 < min (min ρ 1) ((min (c * ρ) 1) / c) :=
    lt_min (lt_min hρ zero_lt_one) (div_pos (lt_min (mul_pos hcpos hρ) zero_lt_one) hcpos)
  obtain ⟨L, hL⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds hbound))
  let t : ℕ → ℝ := fun n => ((L + n : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    simpa only [t, Nat.add_comm, Function.comp_def] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat L)
  have htt : Tendsto (fun n => t n - Real.log c) atTop atTop :=
    (tendsto_atTop_add_const_right atTop (-Real.log c) ht).congr fun _ => by ring
  have hlimT j := (originRadialRemovedGMC_test_limit P X Xc hX hc hm hcont
    (c * ρ) γ (mul_pos hcpos hρ) hγ hγ2 M hM (f j) (hfc j) (hfV j)).comp htt
  have hlimS j := (originRadialRemovedGMC_test_limit P X Xc hX hc hm hcont
    ρ γ hρ hγ hγ2 M hM (g j) (hgc j) (hgU j)).comp ht
  apply gmc_limit_test_vector_law
    (fun n ω j => T (t n - Real.log c) ω j) (fun n ω j => S (t n) ω j)
  · intro n
    exact (measurable_pi_iff.mpr (hmT _)).aemeasurable
  · intro n
    exact (measurable_pi_iff.mpr (hmS _)).aemeasurable
  · exact AEMeasurable.of_eval fun j =>
      ((hlimT j).aestronglyMeasurable (fun n => (hmT _ j).aestronglyMeasurable)).aemeasurable
  · exact AEMeasurable.of_eval fun j =>
      ((hlimS j).aestronglyMeasurable (fun n => (hmS _ j).aestronglyMeasurable)).aemeasurable
  · intro n
    have hb := (hL (L + n) (Nat.le_add_right L n)).le
    have hbc : c * Real.exp (-t n) ≤ min (c * ρ) 1 := by
      simpa only [t, mul_comm] using
        (le_div_iff₀ hcpos).mp (hb.trans (min_le_right _ _))
    exact originLateralCutoff_dilation_test_vector_law P X Xc hX hc hm
      ρ c hρ hcpos γ (t n) (hb.trans (min_le_left _ _)) hbc K hK hKU f hzero
  · exact hlimT
  · exact hlimS

end DOZZ.Proofs
