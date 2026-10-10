/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Moments.ExactScaleBallMoment
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-! # Exact affine scaling of open-set masses

The exact affine mass law and moment scaling of `gmc_affine_openBall_mass_law` and
`gmc_affine_openBall_moment_scale` hold for an arbitrary open set `U ⊆ closedBall 0 R` and its
affine image `y ↦ a + c • y`, not only for balls. The only ball-specific ingredient is the family of
continuous inner approximants: for an open set `U` they are `min 1 (n * infDist x Uᶜ)`, which vanish
off `U` and increase to the indicator of `U`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Inner approximants of an open set -/

/-- A continuous cutoff increasing to the indicator of an open set `U`. It vanishes off `U` and
saturates at `1` once the distance to `Uᶜ` exceeds `1 / n`. -/
noncomputable def openSetApproxFun (U : Set ℂ) (n : ℕ) (x : ℂ) : ℝ :=
  min 1 ((n : ℝ) * Metric.infDist x Uᶜ)

theorem openSetApproxFun_continuous (U : Set ℂ) (n : ℕ) :
    Continuous (openSetApproxFun U n) := by
  unfold openSetApproxFun
  fun_prop

theorem openSetApproxFun_bounds (U : Set ℂ) (n : ℕ) (x : ℂ) :
    0 ≤ openSetApproxFun U n x ∧ openSetApproxFun U n x ≤ 1 :=
  ⟨le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg), min_le_left _ _⟩

theorem openSetApproxFun_eq_zero_of_notMem {U : Set ℂ} {x : ℂ} (hx : x ∉ U) (n : ℕ) :
    openSetApproxFun U n x = 0 := by
  have h : Metric.infDist x Uᶜ = 0 := Metric.infDist_zero_of_mem (by simpa using hx)
  simp [openSetApproxFun, h]

/-- The open-set approximants as bounded continuous functions. -/
noncomputable def openSetApprox (U : Set ℂ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (openSetApproxFun U n)
    (openSetApproxFun_continuous U n) 1 (fun x => by
      have h := openSetApproxFun_bounds U n x
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2)

theorem openSetApprox_apply (U : Set ℂ) (n : ℕ) (x : ℂ) :
    openSetApprox U n x = openSetApproxFun U n x := rfl

/-- Off the open set the cutoffs vanish, so their topological support stays in any closed set
containing it. -/
theorem openSetApprox_tsupport_subset {U K : Set ℂ} (hK : IsClosed K) (hUK : U ⊆ K) (n : ℕ) :
    tsupport (openSetApprox U n : ℂ → ℝ) ⊆ K := by
  refine closure_minimal (fun x hx => hUK ?_) hK
  by_contra hxU
  exact hx (openSetApproxFun_eq_zero_of_notMem hxU n)

/-- The cutoffs converge pointwise to the indicator of an open set with nonempty complement. -/
theorem openSetApproxFun_tendsto {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty) (x : ℂ) :
    Tendsto (fun n : ℕ => openSetApproxFun U n x) atTop
      (𝓝 (U.indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ U
  · have hpos : 0 < Metric.infDist x Uᶜ :=
      (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (by simpa using hx)
    have hev : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * Metric.infDist x Uᶜ :=
      (tendsto_natCast_atTop_atTop.atTop_mul_const hpos).eventually_ge_atTop 1
    have hT : Tendsto (fun n : ℕ => openSetApproxFun U n x) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn => by simp [openSetApproxFun, hn])
    simpa [hx] using hT
  · have hT : Tendsto (fun n : ℕ => openSetApproxFun U n x) atTop (𝓝 0) := by
      simp [openSetApproxFun_eq_zero_of_notMem hx]
    simpa [hx] using hT

/-- Dominated convergence for cutoffs with values in `[0, 1]` converging pointwise to the indicator
of a measurable set. -/
theorem openSetScale_integral_tendsto_of_pointwise
    {f : ℕ → BoundedContinuousFunction ℂ ℝ} {A : Set ℂ} (hA : MeasurableSet A)
    (hbd : ∀ n x, 0 ≤ f n x ∧ f n x ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (A.indicator (fun _ => (1 : ℝ)) x)))
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ x, f n x ∂μ) atTop (𝓝 (μ.real A)) := by
  have hdom : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ (1 : ℝ) := fun n =>
    ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbd n x).1]
      exact (hbd n x).2
  have hconv := tendsto_integral_of_dominated_convergence (fun _ : ℂ => (1 : ℝ))
    (fun n => (f n).continuous.measurable.aestronglyMeasurable)
    (integrable_const 1) hdom (ae_of_all _ hlim)
  rw [← integral_indicator_one hA]
  exact hconv

/-- Integrals of the open-set cutoffs converge to the mass of the open set. -/
theorem openSetApprox_integral_tendsto {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ x, openSetApprox U n x ∂μ) atTop (𝓝 (μ.real U)) :=
  openSetScale_integral_tendsto_of_pointwise hU.measurableSet
    (fun n x => openSetApproxFun_bounds U n x) (openSetApproxFun_tendsto hU hne) μ

/-! ### Affine pullbacks -/

/-- The affine image of a set under `y ↦ a + c • y` is the preimage under the inverse map. -/
theorem openSetScale_image_eq_preimage {c : ℝ} (hc : c ≠ 0) (a : ℂ) (U : Set ℂ) :
    (fun y : ℂ => a + c • y) '' U = (fun y : ℂ => c⁻¹ • (y - a)) ⁻¹' U :=
  congrFun (Set.image_eq_preimage_of_inverse
    (fun x => by simp [hc]) (fun y => by simp [hc])) U

/-- The affine image of an open set is open. -/
theorem openSetScale_image_isOpen {c : ℝ} (hc : c ≠ 0) (a : ℂ) {U : Set ℂ} (hU : IsOpen U) :
    IsOpen ((fun y : ℂ => a + c • y) '' U) := by
  rw [openSetScale_image_eq_preimage hc a U]
  exact hU.preimage (by fun_prop)

/-- The affine image of a subset of `closedBall 0 R` lies in `closedBall a (c * R)`. -/
theorem openSetScale_image_subset_closedBall {c R : ℝ} (hc : 0 < c) (a : ℂ) {U : Set ℂ}
    (hUR : U ⊆ Metric.closedBall 0 R) :
    (fun y : ℂ => a + c • y) '' U ⊆ Metric.closedBall a (c * R) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxR : ‖x‖ ≤ R := by simpa using hUR hx
  rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg hc.le]
  exact mul_le_mul_of_nonneg_left hxR hc.le

/-- A subset of a closed ball has nonempty complement. -/
theorem openSetScale_compl_nonempty {R : ℝ} {U : Set ℂ} (hUR : U ⊆ Metric.closedBall 0 R) :
    Uᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := NormedField.exists_lt_norm ℂ R
  exact ⟨x, fun hxU => absurd (by simpa using hUR hxU) (not_le_of_gt hx)⟩

/-- Pulling back the centered cutoff of `U` by the inverse affine map `y ↦ c⁻¹ • (y - a)`. -/
noncomputable def openSetAffineApprox (U : Set ℂ) (a : ℂ) (c : ℝ) (n : ℕ) :
    BoundedContinuousFunction ℂ ℝ :=
  (openSetApprox U n).compContinuous ⟨fun y => c⁻¹ • (y - a), by fun_prop⟩

theorem openSetAffineApprox_apply (U : Set ℂ) (a : ℂ) (c : ℝ) (n : ℕ) (y : ℂ) :
    openSetAffineApprox U a c n y = openSetApproxFun U n (c⁻¹ • (y - a)) := rfl

/-- Applying the affine map to the pulled-back cutoff recovers the source cutoff. -/
theorem openSetAffineApprox_comp_affine (U : Set ℂ) (a : ℂ) {c : ℝ} (hc : c ≠ 0) (n : ℕ)
    (x : ℂ) : openSetAffineApprox U a c n (a + c • x) = openSetApprox U n x := by
  simp [openSetAffineApprox_apply, hc, openSetApprox_apply]

/-- The affine pullback cutoff has support inside any closed set containing the affine image. -/
theorem openSetAffineApprox_tsupport_subset {U : Set ℂ} {a : ℂ} {c : ℝ} (hc : c ≠ 0)
    {K : Set ℂ} (hK : IsClosed K) (hUK : (fun y : ℂ => a + c • y) '' U ⊆ K) (n : ℕ) :
    tsupport (openSetAffineApprox U a c n : ℂ → ℝ) ⊆ K := by
  refine closure_minimal (fun y hy => hUK ?_) hK
  rw [openSetScale_image_eq_preimage hc a U, Set.mem_preimage]
  by_contra hyU
  exact hy (openSetApproxFun_eq_zero_of_notMem hyU n)

/-- Integrals of the affine pullback cutoffs converge to the mass of the affine image. -/
theorem openSetAffineApprox_integral_tendsto {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty)
    {a : ℂ} {c : ℝ} (hc : c ≠ 0) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Tendsto (fun n : ℕ => ∫ y, openSetAffineApprox U a c n y ∂μ) atTop
      (𝓝 (μ.real ((fun y : ℂ => a + c • y) '' U))) := by
  refine openSetScale_integral_tendsto_of_pointwise
    (openSetScale_image_isOpen hc a hU).measurableSet
    (fun n y => openSetApproxFun_bounds U n (c⁻¹ • (y - a))) (fun y => ?_) μ
  have h := openSetApproxFun_tendsto hU hne (c⁻¹ • (y - a))
  have hind : ((fun y : ℂ => c⁻¹ • (y - a)) ⁻¹' U).indicator (fun _ => (1 : ℝ)) y =
      U.indicator (fun _ => (1 : ℝ)) (c⁻¹ • (y - a)) :=
    Set.indicator_comp_right (s := U) (g := fun _ => (1 : ℝ)) (fun y : ℂ => c⁻¹ • (y - a))
  rw [openSetScale_image_eq_preimage hc a U, hind]
  exact h

/-! ### Passing the cutoff laws to the limit -/

/-- Compactly supported test integrals of an `IsGMCOf` version are a.e. measurable, since they are
limits in measure of the measurable cutoff test integrals. This is the form of
`gmc_test_integral_aemeasurable_of_support` that is private to `ExactScaleBallMass`. -/
theorem openSetScale_test_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : MeasurableSet K) (hKunit : ∀ x ∈ K, ‖x‖ ≤ 1)
    (f : BoundedContinuousFunction ℂ ℝ) (hfzero : ∀ x, x ∉ K → f x = 0) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  obtain ⟨Xc, hXc, hMlim⟩ := hM.2
  have hcut (n : ℕ) : AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ n ω) P :=
    regularizedGMC_test_integral_aemeasurable P X hX Xc hXc γ n K hK hKunit f
      f.continuous.measurable hfzero
  exact ((hMlim f).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)).aemeasurable hcut

/-- Cutoffs supported in a closed ball inside the unit disk have a.e. measurable test integrals,
and these converge in measure to the real mass of the limit set. -/
theorem openSetScale_cutoff_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {z : ℂ} {r : ℝ} (hzr : ‖z‖ + r ≤ 1) (A : Set ℂ)
    (f : ℕ → BoundedContinuousFunction ℂ ℝ)
    (hsupp : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ Metric.closedBall z r)
    (hlim : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ],
      Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (μ.real A))) :
    (∀ n, AEMeasurable (fun ω => ∫ x, f n x ∂M ω) P) ∧
      TendstoInMeasure P (fun n ω => ∫ x, f n x ∂M ω) atTop (fun ω => (M ω A).toReal) := by
  have : IsProbabilityMeasure P := hX.1
  have hunit : ∀ x ∈ Metric.closedBall z r, ‖x‖ ≤ 1 := by
    intro x hx
    have hx' : ‖x - z‖ ≤ r := by simpa [dist_eq_norm] using hx
    calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
      _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ 1 := by linarith
  have hmeas (n : ℕ) : AEMeasurable (fun ω => ∫ x, f n x ∂M ω) P :=
    openSetScale_test_integral_aemeasurable P X hX γ M hM (Metric.closedBall z r)
      Metric.isClosed_closedBall.measurableSet hunit (f n)
      (boundedContinuousFunction_eq_zero_off_tsupport_subset (f n) _ (hsupp n))
  refine ⟨hmeas, tendstoInMeasure_of_tendsto_ae (fun n => (hmeas n).aestronglyMeasurable)
    (ae_of_all P fun ω => ?_)⟩
  have := hM.1 ω
  simpa [Measure.real_def] using hlim (M ω)

/-- If the cutoff vectors have equal laws for every `n` and the cutoff integrals converge in measure
to the masses, then the limiting mass vectors have equal laws. The target side lives on `Ω` and the
source side on the product with an independent factor `G`, scaled by a measurable function `s`. -/
theorem openSetScale_limit_law
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Measure ℝ} [IsProbabilityMeasure G] {s : ℝ → ℝ} (hs : Measurable s)
    (If Ig : ℕ → Ω → ℝ) (mA mB : Ω → ℝ)
    (hIf : ∀ n, AEMeasurable (If n) P) (hIg : ∀ n, AEMeasurable (Ig n) P)
    (hmA : AEMeasurable mA P) (hmB : AEMeasurable mB P)
    (hfconv : TendstoInMeasure P If atTop mA) (hgconv : TendstoInMeasure P Ig atTop mB)
    (hlaw : ∀ n, Measure.map (fun ω (_ : Fin 1) => If n ω) P =
      Measure.map (fun q : Ω × ℝ => fun _ : Fin 1 => s q.2 * Ig n q.1) (P.prod G)) :
    Measure.map (fun ω (_ : Fin 1) => mA ω) P =
      Measure.map (fun q : Ω × ℝ => fun _ : Fin 1 => s q.2 * mB q.1) (P.prod G) := by
  have hsnd : AEMeasurable (fun q : Ω × ℝ => s q.2) (P.prod G) :=
    (hs.comp measurable_snd).aemeasurable
  exact gmc_limit_test_vector_law (fun n ω (_ : Fin 1) => If n ω)
    (fun n (q : Ω × ℝ) (_ : Fin 1) => s q.2 * Ig n q.1) (fun ω (_ : Fin 1) => mA ω)
    (fun (q : Ω × ℝ) (_ : Fin 1) => s q.2 * mB q.1)
    (fun n => aemeasurable_pi_iff.2 fun _ => hIf n)
    (fun n => aemeasurable_pi_iff.2 fun _ => hsnd.mul (hIg n).comp_fst)
    (aemeasurable_pi_iff.2 fun _ => hmA) (aemeasurable_pi_iff.2 fun _ => hsnd.mul hmB.comp_fst)
    hlaw (fun _ => hfconv)
    (fun _ => tendstoInMeasure_mul_snd_of_tendstoInMeasure Ig mB s hs hgconv)

/-- The exact affine mass law for any pair of measurable sets with cutoff approximants: the
cutoffs `f n` on the target and `g n` on the source are nonnegative, supported in the target and
source closed balls, related by `f n (a + c • x) = g n x`, and their integrals converge to the
masses of the two sets. -/
theorem openSetScale_mass_law_of_approx
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    {A B : Set ℂ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (f g : ℕ → BoundedContinuousFunction ℂ ℝ) (hfNonneg : ∀ n x, 0 ≤ f n x)
    (hfSupport : ∀ n, tsupport (f n : ℂ → ℝ) ⊆ Metric.closedBall a (c * R))
    (hgSupport : ∀ n, tsupport (g n : ℂ → ℝ) ⊆ Metric.closedBall 0 R)
    (hfg : ∀ n x, f n (a + c • x) = g n x)
    (hfLim : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ],
      Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 (μ.real A)))
    (hgLim : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ],
      Tendsto (fun n => ∫ x, g n x ∂μ) atTop (𝓝 (μ.real B))) :
    Measure.map (fun ω : Ω => fun _ : Fin 1 => (M ω A).toReal) P =
    Measure.map (fun p : Ω × ℝ => fun _ : Fin 1 =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) * (M p.1 B).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) := by
  have : IsProbabilityMeasure P := hX.1
  have : IsProbabilityMeasure (gaussianReal 0 ⟨-Real.log c,
      neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩) :=
    instIsProbabilityMeasureGaussianReal 0 _
  obtain ⟨hfmeas, hfconv⟩ := openSetScale_cutoff_tendstoInMeasure P X hX γ M hM
    (z := a) (r := c * R) hTsmall.le A f hfSupport hfLim
  obtain ⟨hgmeas, hgconv⟩ := openSetScale_cutoff_tendstoInMeasure P X hX γ M hM
    (z := 0) (r := R) (by simpa using hRsmall.le) B g hgSupport hgLim
  refine openSetScale_limit_law
    (s := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))) (by fun_prop)
    (fun n ω => ∫ x, f n x ∂M ω) (fun n ω => ∫ x, g n x ∂M ω)
    (fun ω => (M ω A).toReal) (fun ω => (M ω B).toReal) hfmeas hgmeas
    (ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM A hA))
    (ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B hB))
    hfconv hgconv fun n => ?_
  have h := gmc_affine_test_vector_law P X hX γ M hM (a := a) (c := c) (R := R)
    hc hc1 hR hRsmall hTsmall (fun _ : Fin 1 => f n) (fun _ x => hfNonneg n x)
    (fun _ => hfSupport n)
  simp only [hfg] at h
  exact h

/-! ### The exact affine mass law for open sets -/

/-- Exact affine scaling of the mass of an open set `U ⊆ closedBall 0 R` and of its affine image
under `y ↦ a + c • y`, for every `IsGMCOf` version: the target mass vector has the law of the source
mass scaled by `c ^ 2 * exp (γ w - γ ^ 2 / 2 * (-log c))` for an independent Gaussian `w`. -/
theorem gmc_affine_openSet_mass_law
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (U : Set ℂ) (hU : IsOpen U) (hUR : U ⊆ Metric.closedBall 0 R) :
    Measure.map (fun ω : Ω => fun _ : Fin 1 =>
      (M ω ((fun y => a + c • y) '' U)).toReal) P =
    Measure.map (fun p : Ω × ℝ => fun _ : Fin 1 =>
      c ^ 2 * Real.exp (γ * p.2 - γ ^ 2 / 2 * (-Real.log c)) * (M p.1 U).toReal)
      (P.prod (gaussianReal 0 ⟨-Real.log c,
        neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩)) :=
  have hne := openSetScale_compl_nonempty hUR
  openSetScale_mass_law_of_approx P X hX γ hγ hγ2 M hM hc hc1 hR hRsmall hTsmall
    (openSetScale_image_isOpen hc.ne' a hU).measurableSet hU.measurableSet
    (fun n => openSetAffineApprox U a c n) (fun n => openSetApprox U n)
    (fun n _ => (openSetApproxFun_bounds U n _).1)
    (fun n => openSetAffineApprox_tsupport_subset hc.ne' Metric.isClosed_closedBall
      (openSetScale_image_subset_closedBall hc a hUR) n)
    (fun n => openSetApprox_tsupport_subset Metric.isClosed_closedBall hUR n)
    (fun n x => openSetAffineApprox_comp_affine U a hc.ne' n x)
    (fun μ _ => openSetAffineApprox_integral_tendsto hU hne hc.ne' μ)
    (fun μ _ => openSetApprox_integral_tendsto hU hne μ)

/-! ### Moment scaling -/

/-- An extended power of a real factor times a finite mass splits as a product of extended
powers. -/
private theorem openSetScale_rpow_ofReal_mul_toReal {s : ℝ} {m : ℝ≥0∞} (hm : m ≠ ∞) (p : ℝ) :
    ENNReal.rpow (ENNReal.ofReal (s * m.toReal)) p =
      ENNReal.rpow m p * ENNReal.rpow (ENNReal.ofReal s) p := by
  rw [ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hm]
  simpa [mul_comm] using
    ENNReal.mul_rpow_of_ne_top (x := ENNReal.ofReal s) (y := m) ENNReal.ofReal_ne_top hm p

/-- Integrating an extended power against the one-coordinate pushforward of a real function. -/
private theorem openSetScale_lintegral_map_fin_one {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {φ : α → ℝ} (hφ : AEMeasurable φ μ) (p : ℝ) :
    ∫⁻ v, ENNReal.rpow (ENNReal.ofReal (v 0)) p ∂Measure.map (fun x (_ : Fin 1) => φ x) μ =
      ∫⁻ x, ENNReal.rpow (ENNReal.ofReal (φ x)) p ∂μ := by
  have hψ : Measurable (fun v : Fin 1 → ℝ => ENNReal.rpow (ENNReal.ofReal (v 0)) p) :=
    ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp (measurable_pi_apply 0))
  rw [lintegral_map' hψ.aemeasurable (aemeasurable_pi_iff.2 fun _ => hφ)]

/-- Moment transfer through an equality of mass laws: if the mass vector of `A` has the law of the
mass of `B` scaled by an independent factor `s w`, then the `p`th moments are related by the `p`th
moment of the factor. -/
theorem openSetScale_moment_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Measure ℝ} [IsProbabilityMeasure G] {s : ℝ → ℝ} (hs : Measurable s)
    {M : Ω → Measure ℂ} (hfin : ∀ ω, IsFiniteMeasure (M ω)) {A B : Set ℂ}
    (hmassA : AEMeasurable (fun ω => M ω A) P) (hmassB : AEMeasurable (fun ω => M ω B) P)
    (hLaw : Measure.map (fun ω : Ω => fun _ : Fin 1 => (M ω A).toReal) P =
      Measure.map (fun q : Ω × ℝ => fun _ : Fin 1 => s q.2 * (M q.1 B).toReal) (P.prod G))
    (p : ℝ) :
    gmcMassMoment P M A p =
      gmcMassMoment P M B p * ∫⁻ w, ENNReal.rpow (ENNReal.ofReal (s w)) p ∂G := by
  have hAreal : AEMeasurable (fun ω => (M ω A).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable hmassA
  have hBreal : AEMeasurable (fun ω => (M ω B).toReal) P :=
    ENNReal.measurable_toReal.comp_aemeasurable hmassB
  have hprodMeas : AEMeasurable (fun q : Ω × ℝ => s q.2 * (M q.1 B).toReal) (P.prod G) :=
    (hs.comp measurable_snd).aemeasurable.mul hBreal.comp_fst
  have hfactorMom : AEMeasurable (fun w => ENNReal.rpow (ENNReal.ofReal (s w)) p) G :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (ENNReal.measurable_ofReal.comp_aemeasurable hs.aemeasurable)
  have hbaseMom : AEMeasurable (fun ω => ENNReal.rpow (M ω B) p) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmassB
  calc
    gmcMassMoment P M A p = ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (M ω A).toReal) p ∂P := by
      refine lintegral_congr fun ω => ?_
      have := hfin ω
      rw [ENNReal.ofReal_toReal (measure_ne_top (M ω) _)]
    _ = ∫⁻ v, ENNReal.rpow (ENNReal.ofReal (v 0)) p
          ∂Measure.map (fun ω (_ : Fin 1) => (M ω A).toReal) P :=
      (openSetScale_lintegral_map_fin_one hAreal p).symm
    _ = ∫⁻ v, ENNReal.rpow (ENNReal.ofReal (v 0)) p
          ∂Measure.map (fun q : Ω × ℝ => fun _ : Fin 1 => s q.2 * (M q.1 B).toReal)
            (P.prod G) := by rw [hLaw]
    _ = ∫⁻ q, ENNReal.rpow (ENNReal.ofReal (s q.2 * (M q.1 B).toReal)) p ∂P.prod G :=
      openSetScale_lintegral_map_fin_one hprodMeas p
    _ = ∫⁻ q, ENNReal.rpow (M q.1 B) p * ENNReal.rpow (ENNReal.ofReal (s q.2)) p ∂P.prod G := by
      refine lintegral_congr fun q => ?_
      have := hfin q.1
      exact openSetScale_rpow_ofReal_mul_toReal (measure_ne_top (M q.1) _) p
    _ = (∫⁻ ω, ENNReal.rpow (M ω B) p ∂P) * ∫⁻ w, ENNReal.rpow (ENNReal.ofReal (s w)) p ∂G :=
      lintegral_prod_mul hbaseMom hfactorMom

/-- Exact scaling of the `p`th moment of the mass of an open set `U ⊆ closedBall 0 R` under the
affine map `y ↦ a + c • y`, for every `IsGMCOf` version and every real order. At zero mass the
extended-power convention is retained, in particular zero to a negative power is infinite. -/
theorem gmc_affine_openSet_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {a : ℂ} {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hR : 0 < R) (hRsmall : R < 1) (hTsmall : ‖a‖ + c * R < 1)
    (U : Set ℂ) (hU : IsOpen U) (hUR : U ⊆ Metric.closedBall 0 R) (p : ℝ) :
    gmcMassMoment P M ((fun y => a + c • y) '' U) p =
      ENNReal.ofReal (c ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        gmcMassMoment P M U p := by
  have : IsProbabilityMeasure P := hX.1
  have : IsProbabilityMeasure (gaussianReal 0 ⟨-Real.log c,
      neg_nonneg.mpr (Real.log_nonpos hc.le hc1)⟩) :=
    instIsProbabilityMeasureGaussianReal 0 _
  rw [openSetScale_moment_transfer
    (s := fun w => c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))) (by fun_prop) hM.1
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      (openSetScale_image_isOpen hc.ne' a hU).measurableSet)
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM U hU.measurableSet)
    (gmc_affine_openSet_mass_law P X hX γ hγ hγ2 M hM hc hc1 hR hRsmall hTsmall U hU hUR) p,
    gaussianScaleFactor_rpow_integral γ c p hc hc1, mul_comm]

end DOZZ.Proofs
