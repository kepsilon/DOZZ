/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.AnnularMeasureLaw
public import DOZZ.GMC.Moments.InversionAdmissibleLaw
@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal NNReal
open DOZZ.Assembly
namespace DOZZ.Proofs

/-- Inversion reverses the radial covariance coordinate. -/
theorem originRadialCovariance_inversion (s : ℝ) (x : ℂ) :
    originRadialCovariance (-s) x⁻¹ = originRadialCovariance s x := by
  simp only [originRadialCovariance, norm_inv, Real.log_inv, neg_neg]
  simp only [min_def, max_def]
  split_ifs <;> linarith

/-- The concentric potential of the reversed circle, evaluated at the inverse point,
is the original circle potential away from zero. -/
theorem innerPot_origin_inversion (s : ℝ) (x : ℂ) (hx : x ≠ 0) :
    CirclePotential.innerPot 0 (-s) x⁻¹ = CirclePotential.innerPot 0 s x := by
  rw [← CirclePotential.integral_gffKernel_circleMeasure,
    ← CirclePotential.integral_gffKernel_circleMeasure,
    origin_circleKernelPotential_eq _ _ (inv_ne_zero hx),
    origin_circleKernelPotential_eq _ _ hx, originRadialCovariance_inversion]

/-- Inverted tests have exactly the reversed concentric source pairing. -/
theorem circleCross_origin_inversionTest (s : ℝ) (f : TestFn)
    (hf : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    circleCross 0 (-s) (inversionTest f hf) = circleCross 0 s f := by
  rw [circleCross_inversionTest]
  change _ = ∫ x, f x * ∫ w, gffKernel x w ∂circleMeasure 0 s
  simp_rw [CirclePotential.integral_gffKernel_circleMeasure]
  apply integral_congr_ae
  filter_upwards [(volume : Measure ℂ).ae_ne 0] with x hx
  rw [innerPot_origin_inversion s x hx]

/-- The actual coupled inverted concentric circle is the source circle with its
logarithmic radius reversed. This supplies the joint radial input, not just its marginal law. -/
theorem inversionCircle_origin_ae_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (s : ℝ) (Z : Ω → ℝ) (hZ : MemLp Z 2 P)
    (f : ℕ → TestFn) (hf : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : Tendsto (fun n => circleEnergyGap 0 s (f n)) atTop (𝓝 0))
    (hlim : Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f n) (hf n)) - Z ω) 2 P) atTop (𝓝 0)) :
    Z =ᵐ[P] (fun ω => Xc ω 0 (-s)) := by
  let : IsProbabilityMeasure P := hX.1
  let U := fun ω => Xc ω 0 (-s)
  let V := fun ω => Xc ω 0 s
  have hU : MemLp U 2 P := hc.2.1 _ _
  have hV : MemLp V 2 P := hc.2.1 _ _
  have hzeroU : Tendsto (fun _ : ℕ => eLpNorm (fun ω => U ω - U ω) 2 P)
      atTop (𝓝 0) := by simp only [sub_self, ← Pi.zero_def, eLpNorm_zero]; exact tendsto_const_nhds
  have hzeroV : Tendsto (fun _ : ℕ => eLpNorm (fun ω => V ω - V ω) 2 P)
      atTop (𝓝 0) := by simp only [sub_self, ← Pi.zero_def, eLpNorm_zero]; exact tendsto_const_nhds
  have hinv := tendsto_covariance_of_eLpNorm_sub
    (fun _ => hU) (fun n => equatorGFF_test_memLp X hX (inversionTest (f n) (hf n)))
    hU hZ hzeroU hlim
  have hsrc := tendsto_covariance_of_eLpNorm_sub
    (fun _ => hV) (fun n => equatorGFF_test_memLp X hX (f n))
    hV hV hzeroV (hc.2.2 0 s f hgap)
  have he n : covariance U (fun ω => X ω (inversionTest (f n) (hf n))) P =
      covariance V (fun ω => X ω (f n)) P := by
    rw [circleAverage_test_covariance P X Xc hX hc,
      circleAverage_test_covariance P X Xc hX hc, circleCross_origin_inversionTest]
  have hmix : covariance U Z P = covariance V V P :=
    tendsto_nhds_unique (hinv.congr' (Eventually.of_forall he)) hsrc
  have hselfU : covariance U U P = |s| := by
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin, origin_circle_variance_algebra, abs_neg]
  have hselfV : covariance V V P = |s| := by
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin, origin_circle_variance_algebra]
  have hmeanZ : (∫ ω, Z ω ∂P) = 0 := integral_eq_zero_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX _) hZ
    (fun n => equatorGFF_test_integral X hX _) hlim
  obtain ⟨_, hmean⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hlaw := inversionCircle_fdd_law P X hX P X hX Xc hc
    (fun _ : Fin 1 => (0, s)) (fun _ => Z) (fun _ => hZ)
    (fun _ => f) (fun _ => hf) (fun _ => hgap) (fun _ => hlim)
  have hs := congrArg (fun μ : Measure (Fin 1 → ℝ) => ∫ v, (v 0) ^ 2 ∂μ) hlaw
  have hZm : AEMeasurable (fun ω (_ : Fin 1) => Z ω) P := AEMeasurable.of_eval fun _ => hZ.aemeasurable
  have hVm : AEMeasurable (fun ω (_ : Fin 1) => V ω) P := AEMeasurable.of_eval fun _ => hV.aemeasurable
  rw [integral_map hZm ((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable,
    integral_map hVm ((measurable_pi_apply 0).pow_const 2).aestronglyMeasurable] at hs
  have hselfZ : covariance Z Z P = |s| := by
    simpa only [covariance, hmeanZ, hmean, sub_zero, ← pow_two, V] using hs.trans
      (by simpa only [covariance, hmean, sub_zero, ← pow_two, V] using hselfV)
  have hD : MemLp (fun ω => Z ω - U ω) 2 P := hZ.sub hU
  have hDmean : (∫ ω, Z ω - U ω ∂P) = 0 := by
    rw [integral_sub (hZ.integrable (by norm_num)) (hU.integrable (by norm_num)), hmeanZ]
    change 0 - (∫ ω, Xc ω 0 (-s) ∂P) = 0
    rw [hmean, sub_zero]
  have hDcov : covariance (fun ω => Z ω - U ω) (fun ω => Z ω - U ω) P = 0 := by
    rw [covariance_fun_sub_fun_sub hZ hU hZ hU, covariance_comm Z U,
      hmix, hselfZ, hselfU, hselfV]
    ring
  have hDsquare : (∫ ω, (Z ω - U ω) ^ 2 ∂P) = 0 := by
    simpa only [covariance, hDmean, sub_zero, ← pow_two] using hDcov
  have hi : Integrable (fun ω => (Z ω - U ω) ^ 2) P := by
    have ht : Integrable (fun ω => (Z ω - U ω) * (Z ω - U ω)) P := hD.integrable_mul hD
    simpa only [pow_two] using ht
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hi).mp hDsquare
  filter_upwards [hae] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

/-- Finite-reference spatial law transfer retains arbitrary auxiliary finite coordinates.
The normalization argument preserves their coupling to the whole sampled field. -/
theorem spatialIntegral_joint_vector_law_of_fdd_finite
    {Ω Ω' S : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace S] [Nonempty S]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (ν : FiniteMeasure S) {k m : ℕ} (X : Ω → S → ℝ) (Y : Ω' → S → ℝ)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (z : Fin m → S → ℝ → ℝ)
    (hX : Measurable (fun p : Ω × S => X p.1 p.2))
    (hY : Measurable (fun p : Ω' × S => Y p.1 p.2))
    (hz : ∀ j, Measurable (fun p : S × ℝ => z j p.1 p.2))
    (hintX : ∀ j, ∀ᵐ ω ∂P, Integrable (fun x => z j x (X ω x)) (ν : Measure S))
    (hintY : ∀ j, ∀ᵐ ω ∂P', Integrable (fun x => z j x (Y ω x)) (ν : Measure S))
    (hFDD : ∀ n (xs : Fin n → S), P.map (fun ω => (V ω, fun i => X ω (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Y ω (xs i)))) :
    P.map (fun ω => (V ω, fun j => ∫ x, z j x (X ω x) ∂(ν : Measure S))) =
      P'.map (fun ω => (V' ω, fun j => ∫ x, z j x (Y ω x) ∂(ν : Measure S))) := by
  classical
  let z' : Fin m → S → ℝ → ℝ := fun j x t => (ν.mass : ℝ) * z j x t
  have hmeasure : (ν : Measure S) = (ν.mass : ℝ≥0) • (ν.normalize : Measure S) :=
    congrArg (fun μ : FiniteMeasure S => (μ : Measure S)) ν.self_eq_mass_smul_normalize
  have hiX j : ∀ᵐ ω ∂P, Integrable (fun x => z' j x (X ω x)) (ν.normalize : Measure S) := by
    by_cases hm : ν.mass = 0
    · exact ae_of_all _ fun ω => by simp only [z', hm, NNReal.coe_zero, zero_mul]; exact integrable_zero _ _ _
    · filter_upwards [hintX j] with ω hω
      rw [hmeasure] at hω
      have ht : Integrable (fun x => z j x (X ω x)) (ν.normalize : Measure S) :=
        (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) (by finiteness)).mp hω
      exact ht.const_mul _
  have hiY j : ∀ᵐ ω ∂P', Integrable (fun x => z' j x (Y ω x)) (ν.normalize : Measure S) := by
    by_cases hm : ν.mass = 0
    · exact ae_of_all _ fun ω => by simp only [z', hm, NNReal.coe_zero, zero_mul]; exact integrable_zero _ _ _
    · filter_upwards [hintY j] with ω hω
      rw [hmeasure] at hω
      have ht : Integrable (fun x => z j x (Y ω x)) (ν.normalize : Measure S) :=
        (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hm) (by finiteness)).mp hω
      exact ht.const_mul _
  have he := (chaosLawFDD_of_integrable (ν.normalize : Measure S) X Y V V' z'
    hV hV' hX hY
    (fun j => measurable_const.mul (hz j)) hiX hiY hFDD
    (0 : BoundedContinuousFunction ((Fin k → ℝ) × (Fin m → ℝ)) ℝ)).1
  have hmass (a : S → ℝ) : (∫ x, (ν.mass : ℝ) * a x ∂(ν.normalize : Measure S)) =
      ∫ x, a x ∂(ν : Measure S) := by
    rw [hmeasure, integral_smul_nnreal_measure, integral_const_mul]
    rfl
  simpa only [z', hmass] using he

/-- The cutoff chaos law retains its coupling to auxiliary finite coordinates. -/
theorem admissibleLogChaos_cutoff_joint_vector_law_of_fdd
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (Z : Ω' → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P' U dens ε₁ Z)
    [IsFiniteMeasure (logRegularizationReference U dens)]
    {k m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U)
    (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (γ r : ℝ) (hrY : Real.exp (-r) ≤ ε₀) (hrZ : Real.exp (-r) ≤ ε₁)
    (hfdd : ∀ n (xs : Fin n → ℂ),
      P.map (fun ω => (V ω, fun i => Y ω (Real.exp (-r)) (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Z ω (Real.exp (-r)) (xs i)))) :
    P.map (fun ω => (V ω, fun j => regularizedLogChaosTestMass P U dens Y γ r ω (f j))) =
      P'.map (fun ω => (V' ω, fun j => regularizedLogChaosTestMass P' U dens Z γ r ω (f j))) := by
  let ε := Real.exp (-r)
  have hv (x : ℂ) : (∫ ω, Y ω ε x ^ 2 ∂P) = ∫ ω, Z ω ε x ^ 2 ∂P' := by
    have hMY : Measurable (fun ω => (V ω, fun (_ : Fin 1) => Y ω ε x)) :=
      hV.prodMk (measurable_pi_iff.mpr (fun _ => (hY.measurableAtScale ε).comp
        (measurable_id.prodMk measurable_const)))
    have hMZ : Measurable (fun ω => (V' ω, fun (_ : Fin 1) => Z ω ε x)) :=
      hV'.prodMk (measurable_pi_iff.mpr (fun _ => (hZ.measurableAtScale ε).comp
        (measurable_id.prodMk measurable_const)))
    have ht := congrArg (fun μ : Measure ((Fin k → ℝ) × (Fin 1 → ℝ)) => ∫ v, (v.2 0) ^ 2 ∂μ)
      (hfdd 1 (fun _ => x))
    have hφ : Measurable (fun v : (Fin k → ℝ) × (Fin 1 → ℝ) => (v.2 0) ^ 2) := by fun_prop
    change (∫ v, (v.2 0) ^ 2 ∂P.map (fun ω => (V ω, fun (_ : Fin 1) => Y ω ε x))) =
      ∫ v, (v.2 0) ^ 2 ∂P'.map (fun ω => (V' ω, fun (_ : Fin 1) => Z ω ε x)) at ht
    rw [integral_map hMY.aemeasurable hφ.aestronglyMeasurable,
      integral_map hMZ.aemeasurable hφ.aestronglyMeasurable] at ht
    exact ht
  let variance : ℂ → ℝ := fun x => ∫ ω, Y ω ε x ^ 2 ∂P
  have hvariance : Measurable variance := by
    have ht := admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε
    simpa only [variance, gaussianVariance, gaussianCovariance, pow_two] using ht
  let ν : FiniteMeasure ℂ := ⟨logRegularizationReference U dens, inferInstance⟩
  let z : Fin m → ℂ → ℝ → ℝ := fun j x t => f j x *
    Real.exp (γ * t - γ ^ 2 / 2 * variance x)
  have hz j : Measurable (fun p : ℂ × ℝ => z j p.1 p.2) := by
    dsimp [z]
    exact ((f j).continuous.measurable.comp measurable_fst).mul
      ((measurable_const.mul measurable_snd).sub
        (measurable_const.mul (hvariance.comp measurable_fst))).exp
  have hiY j : ∀ᵐ ω ∂P, Integrable (fun x => z j x (Y ω ε x)) (ν : Measure ℂ) := by
    exact admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY
      (tsupport (f j : ℂ → ℝ)) (hfc j) (hfU j) γ r hrY ‖f j‖ (f j)
      (f j).continuous.measurable
      (fun x => by simpa only [← Real.norm_eq_abs] using (f j).norm_coe_le_norm x)
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have hiZ j : ∀ᵐ ω ∂P', Integrable (fun x => z j x (Z ω ε x)) (ν : Measure ℂ) := by
    have ht := admissibleCutoff_integrand_integrable_ae P' U dens ε₁ Z hZ
      (tsupport (f j : ℂ → ℝ)) (hfc j) (hfU j) γ r hrZ ‖f j‖ (f j)
      (f j).continuous.measurable
      (fun x => by simpa only [← Real.norm_eq_abs] using (f j).norm_coe_le_norm x)
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
    simpa only [z, variance, hv, ε, ν, FiniteMeasure.toMeasure_mk] using ht
  have ht := spatialIntegral_joint_vector_law_of_fdd_finite ν
    (fun ω x => Y ω ε x) (fun ω x => Z ω ε x) V V' hV hV' z
    (hY.measurableAtScale ε) (hZ.measurableAtScale ε) hz hiY hiZ hfdd
  simpa only [z, variance, ν, ε, FiniteMeasure.toMeasure_mk, regularizedLogChaosTestMass, hv] using ht

/-- Appending a fixed random coordinate preserves convergence in measure exactly. -/
theorem tendstoInMeasure_pair_with_fixed
    {Ω E F : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedAddCommGroup F]
    (P : Measure Ω) (V : Ω → E) (f : ℕ → Ω → F) (g : Ω → F)
    (h : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n ω => (V ω, f n ω)) atTop (fun ω => (V ω, g ω)) := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, norm_zero,
    max_eq_right (norm_nonneg _)] using h

/-- Passing finite chaos test laws to the limit preserves their coupling to fixed
auxiliary coordinates on each probability space. -/
theorem gmc_limit_joint_test_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {k m : ℕ} (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : AEMeasurable V P) (hV' : AEMeasurable V' P')
    (cutoffX : ℕ → Ω → Fin m → ℝ) (cutoffY : ℕ → Ω' → Fin m → ℝ)
    (limitX : Ω → Fin m → ℝ) (limitY : Ω' → Fin m → ℝ)
    (hcutoffX : ∀ n, AEMeasurable (cutoffX n) P)
    (hcutoffY : ∀ n, AEMeasurable (cutoffY n) P')
    (hlimitX : AEMeasurable limitX P) (hlimitY : AEMeasurable limitY P')
    (hlaw : ∀ n, P.map (fun ω => (V ω, cutoffX n ω)) =
      P'.map (fun ω => (V' ω, cutoffY n ω)))
    (hconvX : ∀ j, TendstoInMeasure P (fun n ω => cutoffX n ω j) atTop (fun ω => limitX ω j))
    (hconvY : ∀ j, TendstoInMeasure P' (fun n ω => cutoffY n ω j) atTop (fun ω => limitY ω j)) :
    P.map (fun ω => (V ω, limitX ω)) = P'.map (fun ω => (V' ω, limitY ω)) := by
  apply map_eq_of_seq_map_eq_of_tendstoInMeasure
    (fun n ω => (V ω, cutoffX n ω)) (fun n ω => (V' ω, cutoffY n ω))
    (fun ω => (V ω, limitX ω)) (fun ω => (V' ω, limitY ω))
  · exact fun n => hV.prodMk (hcutoffX n)
  · exact fun n => hV'.prodMk (hcutoffY n)
  · exact hV.prodMk hlimitX
  · exact hV'.prodMk hlimitY
  · exact hlaw
  · exact tendstoInMeasure_pair_with_fixed P V cutoffX limitX
      (tendstoInMeasure_pi_finite P cutoffX limitX hconvX)
  · exact tendstoInMeasure_pair_with_fixed P' V' cutoffY limitY
      (tendstoInMeasure_pi_finite P' cutoffY limitY hconvY)

/-- Compatible cutoff laws pass to limiting chaos jointly with their auxiliary coordinates. -/
theorem admissibleLogChaos_limit_joint_vector_law_of_fdd
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (Z : Ω' → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P' U dens ε₁ Z)
    [IsFiniteMeasure (logRegularizationReference U dens)]
    (γ : ℝ) (M : Ω → Measure ℂ) (N : Ω' → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P' U dens Z γ N)
    {k : ℕ} (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hfdd : ∀ ε, 0 < ε → ε ≤ min ε₀ ε₁ → ∀ n (xs : Fin n → ℂ),
      P.map (fun ω => (V ω, fun i => Y ω ε (xs i))) =
      P'.map (fun ω => (V' ω, fun i => Z ω ε (xs i))))
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω => (V ω, fun j => ∫ x, f j x ∂M ω)) =
      P'.map (fun ω => (V' ω, fun j => ∫ x, f j x ∂N ω)) := by
  have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have heps : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hT
  have hmin : 0 < min ε₀ ε₁ := lt_min hY.cutoffPositive hZ.cutoffPositive
  obtain ⟨L, hL⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds hmin))
  let t : ℕ → ℝ := fun n => ((L + n : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    simpa only [t, Nat.add_comm, Function.comp_def] using hT.comp (tendsto_add_atTop_nat L)
  have hb n : Real.exp (-t n) ≤ min ε₀ ε₁ := (hL (L + n) (Nat.le_add_right L n)).le
  have hmY r j : Measurable (fun ω => regularizedLogChaosTestMass P U dens Y γ r ω (f j)) :=
    admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r (f j) (f j).continuous.measurable
  have hmZ r j : Measurable (fun ω => regularizedLogChaosTestMass P' U dens Z γ r ω (f j)) :=
    admissibleCutoffIntegral_measurable P' U dens ε₁ Z hZ γ r (f j) (f j).continuous.measurable
  apply gmc_limit_joint_test_vector_law V V' hV.aemeasurable hV'.aemeasurable
    (fun n ω j => regularizedLogChaosTestMass P U dens Y γ (t n) ω (f j))
    (fun n ω j => regularizedLogChaosTestMass P' U dens Z γ (t n) ω (f j))
    (fun ω j => ∫ x, f j x ∂M ω) (fun ω j => ∫ x, f j x ∂N ω)
  · intro n
    exact (measurable_pi_iff.mpr (fun j => hmY (t n) j)).aemeasurable
  · intro n
    exact (measurable_pi_iff.mpr (fun j => hmZ (t n) j)).aemeasurable
  · apply AEMeasurable.of_eval
    intro j
    exact ((hM.2.2.2 (f j) (hfc j) (hfU j)).aestronglyMeasurable
      (fun r => (hmY r j).aestronglyMeasurable)).aemeasurable
  · apply AEMeasurable.of_eval
    intro j
    exact ((hN.2.2.2 (f j) (hfc j) (hfU j)).aestronglyMeasurable
      (fun r => (hmZ r j).aestronglyMeasurable)).aemeasurable
  · intro n
    exact admissibleLogChaos_cutoff_joint_vector_law_of_fdd P P' U dens ε₀ ε₁ Y Z hY hZ
      f hfc hfU V V' hV hV' γ (t n) ((hb n).trans (min_le_left _ _))
      ((hb n).trans (min_le_right _ _))
      (hfdd _ (Real.exp_pos _) (hb n))
  · intro j
    exact (hM.2.2.2 (f j) (hfc j) (hfU j)).comp ht
  · intro j
    exact (hN.2.2.2 (f j) (hfc j) (hfU j)).comp ht

/-- Inverted cutoffs retain the reversed source radial coordinates in their full joint
finite-dimensional law. All circles come from one coupled inverted-test construction. -/
theorem inversionCircle_radial_joint_fdd_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (Z : Ω → ℂ → ℝ → ℝ) (f : (ℂ × ℝ) → ℕ → TestFn)
    (hf : ∀ p n, tsupport (f p n : ℂ → ℝ) ⊆ inversionChart)
    (hgap : ∀ p, Tendsto (fun n => circleEnergyGap p.1 p.2 (f p n)) atTop (𝓝 0))
    (hmem : ∀ x r, MemLp (fun ω => Z ω x r) 2 P)
    (hlim : ∀ p, Tendsto (fun n => eLpNorm (fun ω =>
      X ω (inversionTest (f p n) (hf p n)) - Z ω p.1 p.2) 2 P) atTop (𝓝 0))
    {k m : ℕ} (s : Fin k → ℝ) (q : Fin m → ℂ × ℝ) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => Z ω (q j).1 (q j).2)) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => Xc ω (q j).1 (q j).2)) := by
  let Q : Fin (k + m) → ℂ × ℝ := Fin.append (fun i => (0, s i)) q
  have hv := inversionCircle_fdd_law P X hX P X hX Xc hc Q
    (fun i ω => Z ω (Q i).1 (Q i).2) (fun i => hmem _ _)
    (fun i => f (Q i)) (fun i => hf (Q i)) (fun i => hgap (Q i)) (fun i => hlim (Q i))
  let L : (Fin (k + m) → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) := fun v =>
    (fun i => v (Fin.castAdd m i), fun j => v (Fin.natAdd k j))
  have hL : Measurable L := by fun_prop
  have hZm : AEMeasurable (fun ω i => Z ω (Q i).1 (Q i).2) P :=
    AEMeasurable.of_eval fun i => (hmem _ _).aemeasurable
  have hXm : AEMeasurable (fun ω i => Xc ω (Q i).1 (Q i).2) P :=
    AEMeasurable.of_eval fun i => (hc.2.1 _ _).aemeasurable
  have hp := congrArg (fun μ => μ.map L) hv
  rw [AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hZm,
    AEMeasurable.map_map_of_aemeasurable hL.aemeasurable hXm] at hp
  simp only [Function.comp_def, L, Q, Fin.append_left, Fin.append_right] at hp
  have he : ∀ᵐ ω ∂P, ∀ i, Z ω 0 (s i) = Xc ω 0 (-s i) :=
    ae_all_iff.mpr fun i => inversionCircle_origin_ae_eq P X Xc hX hc (s i)
      (fun ω => Z ω 0 (s i)) (hmem _ _) (f (0, s i)) (hf _) (hgap _) (hlim _)
  calc
    _ = P.map (fun ω => (fun i => Z ω 0 (s i), fun j => Z ω (q j).1 (q j).2)) := by
      apply Measure.map_congr
      filter_upwards [he] with ω hω
      exact Prod.ext (funext fun i => (hω i).symm) rfl
    _ = _ := hp

/-- Reverse the logarithmic-radius parameter of a continuous radial path. -/
def originReversedRadialPath (A : TwoSidedPath) : TwoSidedPath :=
  A.comp ⟨fun s : ℝ => -s, continuous_neg⟩

/-- Reversal preserves measurability up to a null event of the entire radial path. -/
theorem originReversedRadialPath_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Ω → TwoSidedPath) (hA : AEMeasurable A P) :
    AEMeasurable (fun ω => originReversedRadialPath (A ω)) P := by
  apply aemeasurable_twoSidedPath_of_eval
  intro s
  exact (ContinuousMap.measurable_eval (-s)).comp_aemeasurable hA

/-- The radial removal weight reverses exactly under complex inversion,
including at its stipulated zero value at the origin. -/
theorem lateralRadialWeight_inversion (γ : ℝ) (A : TwoSidedPath) (x : ℂ) :
    lateralRadialWeight γ (originReversedRadialPath A) x⁻¹ = lateralRadialWeight γ A x := by
  simp only [lateralRadialWeight, norm_inv, inv_eq_zero, Real.log_inv,
    originReversedRadialPath, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
    neg_neg, abs_neg]

/-- Inversion of the measure and reversal of its coupled radial path commute with
radial removal. This identity retains their coupling sample by sample. -/
theorem originRadialRemovedGMC_inversion_commutes
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) :
    (M.map (fun x : ℂ => x⁻¹)).withDensity (lateralRadialWeight γ (originReversedRadialPath A)) =
      (M.withDensity (lateralRadialWeight γ A)).map (fun x : ℂ => x⁻¹) := by
  have harg : Measurable (fun x : ℂ => ((γ, originReversedRadialPath A), x)) :=
    measurable_const.prodMk measurable_id
  have hw : Measurable (lateralRadialWeight γ (originReversedRadialPath A)) :=
    measurable_lateralRadialWeight.comp harg
  apply Measure.ext
  intro S hS
  rw [withDensity_apply _ hS, Measure.map_apply measurable_inv hS,
    withDensity_apply _ (hS.preimage measurable_inv), setLIntegral_map hS hw measurable_inv]
  apply setLIntegral_congr_fun (hS.preimage measurable_inv)
  intro x _
  exact lateralRadialWeight_inversion γ A x

/-- The actual polar projection `DOZZ.lateralProjectedGMC` turns simultaneous
source inversion and radial reversal into reflection of the whole cylinder
measure. -/
theorem lateralProjectedGMC_reversed_inversion
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) :
    lateralProjectedGMC γ (originReversedRadialPath A) (M.map (fun x : ℂ => x⁻¹)) =
      (lateralProjectedGMC γ A M).map (fun s : ℝ => -s) := by
  change ((M.map (fun x : ℂ => x⁻¹)).withDensity
    (lateralRadialWeight γ (originReversedRadialPath A))).map (fun x => -Real.log ‖x‖) = _
  rw [originRadialRemovedGMC_inversion_commutes, logRadiusProjection_inversion]
  rfl

end DOZZ.Proofs
