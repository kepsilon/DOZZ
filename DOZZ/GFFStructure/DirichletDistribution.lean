/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.DiskFourierDistribution
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
/-!
# Supported versions of the actual Dirichlet completion

A fixed smooth cutoff turns the Fourier chart into a global random distribution
on the original probability space. Every evaluation is measurable and equals
its actual completed L² variable. The separable coefficient-space factorization
provides one event on which all exterior tests vanish. Gaussianity, Green
covariance, centering and independence transfer to this supported version.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace lp
namespace DOZZ.Proofs

/-- Radius of a Fourier chart surrounding a fixed disk. -/
noncomputable def diskDistributionChartRadius (c : ℂ) (ρ : ℝ) : ℝ := ‖c‖+|ρ|+5

/-- The Fourier chart has strictly positive radius. -/
theorem diskDistributionChartRadius_pos (c : ℂ) (ρ : ℝ) : 0 < diskDistributionChartRadius c ρ := by
  unfold diskDistributionChartRadius
  positivity

/-- The physical torus box side for one disk chart. -/
noncomputable def diskDistributionChartSide (c : ℂ) (ρ : ℝ) : ℝ := 2*(diskDistributionChartRadius c ρ+2)

/-- A fixed smooth cutoff which equals one on the closed target disk. -/
noncomputable def diskDistributionCutoff (c : ℂ) (ρ : ℝ) : ContDiffBump (0 : ℂ) :=
  DOZZ.localTorusCutoff (‖c‖+|ρ|+1) (by positivity)

/-- The fixed cutoff is one throughout the target disk. -/
theorem diskDistributionCutoff_eq_one (c : ℂ) (ρ : ℝ) (z : ℂ) (hz : z ∈ ball c ρ) :
    diskDistributionCutoff c ρ z = 1 := by
  apply DOZZ.localTorusCutoff_eq_one
  rw [mem_closedBall_iff_norm,sub_zero]
  have hbound : ‖z‖ ≤ ‖z-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (z-c) c
  have hz' := mem_ball_iff_norm.mp hz
  linarith [le_abs_self ρ]

/-- Multiplication by the fixed disk cutoff is continuous in the test-function topology. -/
noncomputable def diskDistributionCutoffCLM (c : ℂ) (ρ : ℝ) : TestFn →L[ℝ] TestFn :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) (diskDistributionCutoff c ρ).contDiff

/-- The cutoff test has its literal product value. -/
theorem diskDistributionCutoffCLM_apply (c : ℂ) (ρ : ℝ) (f : TestFn) (z : ℂ) :
    diskDistributionCutoffCLM c ρ f z = f z*diskDistributionCutoff c ρ z := rfl

/-- Each cutoff test lies strictly within the Fourier chart's approximation region. -/
theorem diskDistributionCutoffCLM_support_subset (c : ℂ) (ρ : ℝ) (f : TestFn) :
    Function.support (diskDistributionCutoffCLM c ρ f) ⊆
      ball (0 : ℂ) (diskDistributionChartRadius c ρ-1) := by
  have hs : tsupport (diskDistributionCutoffCLM c ρ f) ⊆ tsupport (diskDistributionCutoff c ρ) := by
    change tsupport (fun z => f z*diskDistributionCutoff c ρ z) ⊆ _
    exact tsupport_mul_subset_right
  rw [show tsupport (diskDistributionCutoff c ρ) = closedBall (0 : ℂ) (‖c‖+|ρ|+1+2) from
    DOZZ.localTorusCutoff_tsupport _ _] at hs
  exact subset_tsupport _ |>.trans (hs.trans (closedBall_subset_ball (by
    unfold diskDistributionChartRadius; linarith)))

/-- The fixed cutoff does not change any target disk L² restriction. -/
theorem diskTestRestrictionL2_cutoff (c : ℂ) (ρ : ℝ) (f : TestFn) :
    diskTestRestrictionL2 c ρ (diskDistributionCutoffCLM c ρ f) = diskTestRestrictionL2 c ρ f := by
  apply Lp.ext
  filter_upwards [diskTestRestrictionL2_ae_eq c ρ (diskDistributionCutoffCLM c ρ f),
    diskTestRestrictionL2_ae_eq c ρ f,ae_restrict_mem measurableSet_ball] with z hcut hf hz
  rw [hcut,hf,diskDistributionCutoffCLM_apply,diskDistributionCutoff_eq_one c ρ z hz,mul_one]

section Distribution
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) (c : ℂ) (ρ : ℝ)
variable (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P)

/-- The actual global Fourier version of the bounded disk map as a continuous test functional. -/
noncomputable def completedDiskDistributionCLM (ω : Ω) : TestFn →L[ℝ] ℝ :=
  (diskFourierDistribution P c ρ (diskDistributionChartRadius c ρ)
    (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) T ω).comp
      (diskDistributionCutoffCLM c ρ)

/-- The supported random distribution constructed on the original sample space. -/
noncomputable def completedDiskDistribution : Ω → Distr := completedDiskDistributionCLM P c ρ T

/-- Every global test evaluation of the distribution version is measurable. -/
theorem measurable_completedDiskDistribution_apply (f : TestFn) :
    Measurable (fun ω => completedDiskDistribution P c ρ T ω f) :=
  measurable_diskFourierDistribution_apply P c ρ (diskDistributionChartRadius c ρ)
    (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) T
      (diskDistributionCutoffCLM c ρ f)

/-- The global distribution version represents the actual completed variable on each test. -/
theorem completedDiskDistribution_apply_ae_eq (f : TestFn) :
    (fun ω => completedDiskDistribution P c ρ T ω f) =ᵐ[P] ⇑(T (diskTestRestrictionL2 c ρ f)) := by
  have hL : 0 < diskDistributionChartSide c ρ := by
    unfold diskDistributionChartSide; linarith [diskDistributionChartRadius_pos c ρ]
  have hbox : diskDistributionChartSide c ρ/2 = diskDistributionChartRadius c ρ+2 := by
    unfold diskDistributionChartSide; ring
  have h := diskFourierDistribution_apply_ae_eq P c ρ (diskDistributionChartRadius c ρ)
    (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) hL hbox T
    (diskDistributionCutoffCLM c ρ f) (diskDistributionCutoffCLM_support_subset c ρ f)
  rw [diskTestRestrictionL2_cutoff] at h
  exact h

/-- Every global evaluation of the actual distribution version belongs to random L². -/
theorem completedDiskDistribution_apply_memLp (f : TestFn) :
    MemLp (fun ω => completedDiskDistribution P c ρ T ω f) 2 P :=
  (Lp.memLp (T (diskTestRestrictionL2 c ρ f))).ae_eq (completedDiskDistribution_apply_ae_eq P c ρ T f).symm

/-- A centered completed map gives centered distribution evaluations. -/
theorem completedDiskDistribution_apply_integral_zero
    (hT : ∀ f : TestFn, (∫ ω, T (diskTestRestrictionL2 c ρ f) ω ∂P) = 0) (f : TestFn) :
    (∫ ω, completedDiskDistribution P c ρ T ω f ∂P) = 0 := by
  rw [integral_congr_ae (completedDiskDistribution_apply_ae_eq P c ρ T f)]
  exact hT f

/-- The globally indexed distribution version retains joint Gaussianity. -/
theorem completedDiskDistribution_isGaussianProcess
    (hT : IsGaussianProcess (fun f : TestFn => ⇑(T (diskTestRestrictionL2 c ρ f))) P) :
    IsGaussianProcess (fun f : TestFn => fun ω => completedDiskDistribution P c ρ T ω f) P :=
  hT.congr (fun f => (completedDiskDistribution_apply_ae_eq P c ρ T f).symm)

/-- Every covariance of the global distribution version is the actual completed covariance. -/
theorem completedDiskDistribution_covariance_eq (f g : TestFn) :
    covariance (fun ω => completedDiskDistribution P c ρ T ω f)
      (fun ω => completedDiskDistribution P c ρ T ω g) P =
      covariance (T (diskTestRestrictionL2 c ρ f)) (T (diskTestRestrictionL2 c ρ g)) P :=
  covariance_congr_ae (completedDiskDistribution_apply_ae_eq P c ρ T f)
    (completedDiskDistribution_apply_ae_eq P c ρ T g)
end Distribution

/-- Countably indexed complex ℓ² is separable. -/
theorem separableSpace_complex_l2 {ι : Type*} [Countable ι] :
    SeparableSpace (lp (fun _ : ι => ℂ) (2 : ℝ≥0∞)) := by
  classical
  let b : HilbertBasis ι ℂ (lp (fun _ : ι => ℂ) (2 : ℝ≥0∞)) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs := (Set.countable_range b).isSeparable.span (R := ℂ)
  have hc := hs.closure
  rw [← Submodule.topologicalClosure_coe,b.dense_span] at hc
  exact (isSeparable_univ_iff).mp hc

/-- Testwise vanishing upgrades to one event on a separable parameter space of continuous functions. -/
theorem ae_forall_continuous_eq_zero {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [SeparableSpace E] (P : Measure Ω) (F : Ω → E → ℝ)
    (hF : ∀ ω, Continuous (F ω)) (hzero : ∀ x, (fun ω => F ω x) =ᵐ[P] 0) :
    ∀ᵐ ω ∂P, ∀ x, F ω x = 0 := by
  obtain ⟨s,hs,hd⟩ := exists_countable_dense E
  let _ := hs.to_subtype
  have hz : ∀ᵐ ω ∂P, ∀ x : s, F ω x.1 = 0 := ae_all_iff.mpr (fun x => hzero x.1)
  filter_upwards [hz] with ω hω
  have he : EqOn (F ω) 0 s := fun x hx => hω ⟨x,hx⟩
  have hc : EqOn (F ω) 0 (closure s) := he.closure (hF ω) continuous_const
  intro x
  exact hc (hd x)

/-- The coefficient map through which the global disk distribution factors. -/
noncomputable def completedDiskFourierCoeffCLM (c : ℂ) (ρ : ℝ) :
    TestFn →L[ℝ] lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) :=
  (DOZZ.torusH2WeightedFourierCoeffCLM (diskDistributionChartSide c ρ)).comp (diskDistributionCutoffCLM c ρ)

/-- The selected random continuous functional on the Fourier coefficient space. -/
noncomputable def completedDiskFourierPairingCLM {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (ω : Ω) :
    lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) →L[ℝ] ℝ := by
  classical
  exact if hω : diskFourierGood P c ρ (diskDistributionChartRadius c ρ)
    (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) T ω then
      diskFourierPairingCLM P c ρ (diskDistributionChartRadius c ρ)
        (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) T ω hω else 0

/-- The global disk distribution factors through a fixed separable Fourier coefficient space. -/
theorem completedDiskDistribution_eq_fourierPairing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (ω : Ω) (f : TestFn) :
    completedDiskDistribution P c ρ T ω f = completedDiskFourierPairingCLM P c ρ T ω
      (completedDiskFourierCoeffCLM c ρ f) := by
  change diskFourierDistribution P c ρ (diskDistributionChartRadius c ρ)
    (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) T ω (diskDistributionCutoffCLM c ρ f) = _
  by_cases hω : diskFourierGood P c ρ (diskDistributionChartRadius c ρ)
    (diskDistributionChartSide c ρ) (diskDistributionChartRadius_pos c ρ) T ω
  · rw [diskFourierDistribution,dite_eq_left hω,completedDiskFourierPairingCLM,dite_eq_left hω]
    rfl
  · rw [diskFourierDistribution,dite_eq_right hω,completedDiskFourierPairingCLM,dite_eq_right hω]
    rfl

/-- The distribution version vanishes on all exterior tests on one full-measure event. -/
theorem ae_completedDiskDistribution_exterior_tests_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) :
    ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ (closedBall c ρ)ᶜ → completedDiskDistribution P c ρ T ω f = 0 := by
  let E := lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞)
  let _ : SeparableSpace E := separableSpace_complex_l2
  let S : Set E := (completedDiskFourierCoeffCLM c ρ) '' {f : TestFn | tsupport f ⊆ (closedBall c ρ)ᶜ}
  let F : Ω → S → ℝ := fun ω u => completedDiskFourierPairingCLM P c ρ T ω u.1
  have hzero : ∀ u : S, (fun ω => F ω u) =ᵐ[P] 0 := by
    intro u
    obtain ⟨f,hf,he⟩ := u.2
    have hres := diskTestRestrictionL2_eq_zero_of_exterior c ρ f hf
    filter_upwards [completedDiskDistribution_apply_ae_eq P c ρ T f,Lp.coeFn_zero ℝ 2 P] with ω hω hz
    change completedDiskFourierPairingCLM P c ρ T ω u.1 = 0
    rw [← he,← completedDiskDistribution_eq_fourierPairing P c ρ T ω f,hω,hres,map_zero,hz]
    rfl
  have h := ae_forall_continuous_eq_zero P F
    (fun ω => (completedDiskFourierPairingCLM P c ρ T ω).continuous.comp continuous_subtype_val) hzero
  filter_upwards [h] with ω hω
  intro f hf
  rw [completedDiskDistribution_eq_fourierPairing]
  exact hω ⟨completedDiskFourierCoeffCLM c ρ f,⟨f,hf,rfl⟩⟩

/-- The actual supported Dirichlet distribution obtained from the completed residual map. -/
noncomputable def dirichletDistribution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ)) : Ω → Distr :=
  completedDiskDistribution P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ hR V hV hU)


/-- Every global Dirichlet distribution evaluation retains the actual completed residual. -/
theorem dirichletDistribution_apply_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) : (fun ω => dirichletDistribution P X Xc hX hc c R ρ hR V hV hU ω f) =ᵐ[P] ⇑(dirichletCompletedL2Map P X Xc hX hc c R ρ hR V hV hU (diskTestRestrictionL2 c ρ f)) :=
  completedDiskDistribution_apply_ae_eq P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ hR V hV hU) f

/-- Every global Dirichlet distribution evaluation is centered. -/
theorem dirichletDistribution_apply_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (f : TestFn) : (∫ ω, dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f ∂P) = 0 :=
  completedDiskDistribution_apply_integral_zero P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU)
    (fun f => dirichletCompletedL2Map_integral_zero P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim _) f

/-- The actual supported Dirichlet distribution has exactly the Green covariance
`DOZZ.diskGreenCovariance`. -/
theorem dirichletDistribution_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (f g : TestFn) : covariance (fun ω => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f) (fun ω => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω g) P =
      diskGreenCovariance c ρ hρ f g := by
  rw [dirichletDistribution,completedDiskDistribution_covariance_eq P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU)]
  exact dirichletCompletedL2Map_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f g

/-- The supported Dirichlet distribution has jointly Gaussian global test evaluations. -/
theorem dirichletDistribution_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    : IsGaussianProcess (fun f : TestFn => fun ω => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f) P := by
  have hG := dirichletCompletedL2Map_isGaussianProcess P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim
  exact completedDiskDistribution_isGaussianProcess P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU)
    (hG.comp_right (diskTestRestrictionL2 c ρ))

/-- One event makes the actual supported Dirichlet distribution vanish on every exterior test. -/
theorem ae_dirichletDistribution_exterior_tests_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    : ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ (closedBall c ρ)ᶜ → dirichletDistribution P X Xc hX hc c R ρ hR V hV hU ω f = 0 :=
  ae_completedDiskDistribution_exterior_tests_zero P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ hR V hV hU)


/-- Replacing completed tests by their supported distribution versions preserves joint Gaussianity. -/
theorem completedDiskDistribution_joint_isGaussianProcess {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (Y : I → Ω → ℝ)
    (hG : IsGaussianProcess (Sum.elim (fun f : TestFn => ⇑(T (diskTestRestrictionL2 c ρ f))) Y) P) :
    IsGaussianProcess (Sum.elim (fun f : TestFn => fun ω => completedDiskDistribution P c ρ T ω f) Y) P := by
  apply hG.congr
  intro t
  cases t with
  | inl f => exact (completedDiskDistribution_apply_ae_eq P c ρ T f).symm
  | inr i => exact EventuallyEq.rfl

/-- A supported version remains independent of any jointly Gaussian orthogonal process. -/
theorem completedDiskDistribution_indep_of_covariance_zero {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (Y : I → Ω → ℝ)
    (hG : IsGaussianProcess (Sum.elim (fun f : TestFn => ⇑(T (diskTestRestrictionL2 c ρ f))) Y) P)
    (hcov : ∀ f i, covariance (T (diskTestRestrictionL2 c ρ f)) (Y i) P = 0) :
    IndepFun (fun ω (f : TestFn) => completedDiskDistribution P c ρ T ω f) (fun ω i => Y i ω) P := by
  have hg := completedDiskDistribution_joint_isGaussianProcess P c ρ T Y hG
  exact hg.indepFun_of_covariance_eq_zero
    (fun f => (measurable_completedDiskDistribution_apply P c ρ T f).aemeasurable)
    (fun i => hG.aemeasurable (Sum.inr i))
    (fun f i => by
      rw [covariance_congr_ae (completedDiskDistribution_apply_ae_eq P c ρ T f) EventuallyEq.rfl]
      exact hcov f i)






/-- Every actual supported Dirichlet test evaluation is measurable. -/
theorem measurable_dirichletDistribution_apply {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) : Measurable (fun ω => dirichletDistribution P X Xc hX hc c R ρ hR V hV hU ω f) :=
  measurable_completedDiskDistribution_apply P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ hR V hV hU) f

/-- Every actual supported Dirichlet test evaluation belongs to random L². -/
theorem dirichletDistribution_apply_memLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) : MemLp (fun ω => dirichletDistribution P X Xc hX hc c R ρ hR V hV hU ω f) 2 P :=
  completedDiskDistribution_apply_memLp P c ρ (dirichletCompletedL2Map P X Xc hX hc c R ρ hR V hV hU) f

end DOZZ.Proofs
