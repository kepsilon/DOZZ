/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.DirichletDistribution
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
/-!
# Common events for harmonic and finite Markov identities

Compact smooth test spaces are second-countable in their derivative topology,
and the disk interior test space is separable. Testwise harmonic agreement thus
holds on one event for every interior test. The literal finite complementary
distribution gives simultaneous decomposition and restoration, measurable
centered L² evaluations, and harmonic identification on separated disks.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace lp Distributions BoundedContinuousFunction
namespace DOZZ.Proofs

/-- Bounded continuous functions which vanish off a fixed compact set. -/
def compactSupportedBCF (F : Type*) [NormedAddCommGroup F] (K : Compacts ℂ) : Set (ℂ →ᵇ F) :=
  {f | EqOn f 0 (K : Set ℂ)ᶜ}

/-- Restriction to the compact support preserves the uniform metric exactly. -/
theorem isometry_compactSupportedBCF_restriction (F : Type*) [NormedAddCommGroup F] (K : Compacts ℂ) :
    Isometry (fun f : compactSupportedBCF F K => f.1.domRestrict (K : Set ℂ)) := by
  apply Isometry.of_dist_eq
  intro f g
  change dist (f.1.domRestrict (K : Set ℂ)) (g.1.domRestrict (K : Set ℂ)) = dist f.1 g.1
  rw [dist_eq_norm,dist_eq_norm]
  apply le_antisymm
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro z
    change ‖f.1 z.1-g.1 z.1‖ ≤ ‖f.1-g.1‖
    exact (f.1-g.1).norm_coe_le_norm z.1
  · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro z
    by_cases hz : z ∈ (K : Set ℂ)
    · exact (f.1.domRestrict (K : Set ℂ)-g.1.domRestrict (K : Set ℂ)).norm_coe_le_norm ⟨z,hz⟩
    · change ‖f.1 z-g.1 z‖ ≤ _
      rw [f.2 hz,g.2 hz,Pi.zero_apply,sub_self,norm_zero]
      exact norm_nonneg _

/-- Uniformly supported bounded continuous functions form a second-countable space. -/
theorem secondCountable_compactSupportedBCF (F : Type*) [NormedAddCommGroup F]
    [SecondCountableTopology F] (K : Compacts ℂ) : SecondCountableTopology (compactSupportedBCF F K) := by
  let _ : CompactSpace K := inferInstance
  let _ : SecondCountableTopology ((K : Set ℂ) →ᵇ F) :=
    (ContinuousMap.isometryEquivBoundedOfCompact K F).symm.isometry.isEmbedding.secondCountableTopology
  exact (isometry_compactSupportedBCF_restriction F K).isEmbedding.secondCountableTopology

/-- Each smooth compact-support jet lies in the corresponding supported bounded function space. -/
noncomputable def compactTestStructureMap (K : Compacts ℂ) (i : ℕ) :
    𝓓_{K}(ℂ,ℝ) → compactSupportedBCF (ℂ [×i]→L[ℝ] ℝ) K := fun f =>
  ⟨ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i f,by
    intro z hz
    change ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i f z = 0
    rw [ContDiffMapSupportedIn.structureMapLM_top_apply]
    exact f.iteratedFDeriv_zero_on_compl hz⟩

/-- Using supported jet codomains leaves the induced compact-test topology unchanged. -/
theorem compactTestStructureMap_induced (K : Compacts ℂ) (i : ℕ) :
    TopologicalSpace.induced (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i :
      𝓓_{K}(ℂ,ℝ) → ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ)) inferInstance =
    TopologicalSpace.induced (compactTestStructureMap K i) inferInstance := by
  change TopologicalSpace.induced _ _ = TopologicalSpace.induced (compactTestStructureMap K i)
    (TopologicalSpace.induced Subtype.val inferInstance)
  rw [induced_compose]
  rfl

/-- Smooth tests supported in any fixed compact set form a second-countable space. -/
theorem secondCountable_compactTestSpace (K : Compacts ℂ) : SecondCountableTopology 𝓓_{K}(ℂ,ℝ) := by
  change @SecondCountableTopology _ (⨅ i : ℕ, TopologicalSpace.induced
    (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i : 𝓓_{K}(ℂ,ℝ) → ℂ →ᵇ (ℂ [×i]→L[ℝ] ℝ)) inferInstance)
  apply secondCountableTopology_iInf
  intro i
  rw [compactTestStructureMap_induced]
  let _ : FiniteDimensional ℝ (ℂ [×i]→L[ℝ] ℝ) := FiniteDimensional.of_injective
    ContinuousMultilinearMap.toMultilinearMapLinear ContinuousMultilinearMap.toMultilinearMap_injective
  let _ : SecondCountableTopology (compactSupportedBCF (ℂ [×i]→L[ℝ] ℝ) K) :=
    secondCountable_compactSupportedBCF _ K
  exact secondCountableTopology_induced _ _ _

/-- The open target disk as an open subset of the plane. -/
def diskTestOpen (c : ℂ) (ρ : ℝ) : Opens ℂ := ⟨ball c ρ,isOpen_ball⟩

/-- Smooth tests with compact support strictly inside a disk. -/
abbrev InteriorDiskTest (c : ℂ) (ρ : ℝ) := TestFunction (diskTestOpen c ρ) ℝ ⊤

/-- Every compact interior test is contained in some compact disk of a countable exhaustion. -/
theorem exists_compact_disk_exhaustion_for_test (c : ℂ) (ρ : ℝ)
    (d : ℕ → ℝ) (hcover : ∀ r, r < ρ → ∃ j, r < d j) (f : InteriorDiskTest c ρ) :
    ∃ j, tsupport f ⊆ closedBall c (d j) := by
  by_cases hs : (tsupport f).Nonempty
  · obtain ⟨z,hz,hmax⟩ := f.hasCompactSupport.exists_isMaxOn hs
      ((continuous_id.sub continuous_const).norm.continuousOn)
    obtain ⟨j,hj⟩ := hcover ‖z-c‖ (mem_ball_iff_norm.mp (f.tsupport_subset hz))
    refine ⟨j,fun w hw => mem_closedBall_iff_norm.mpr ((hmax hw).trans hj.le)⟩
  · exact ⟨0,fun z hz => (hs ⟨z,hz⟩).elim⟩

/-- The smooth interior test space is separable in its actual inductive-limit topology. -/
theorem separableSpace_interiorDiskTest (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    SeparableSpace (InteriorDiskTest c ρ) := by
  obtain ⟨d,b,hdb,hcover⟩ := exists_poisson_inner_disk_exhaustion ρ hρ
  let K (j : ℕ) : Compacts ℂ := ⟨closedBall c (d j),isCompact_closedBall c (d j)⟩
  have hK j : (K j : Set ℂ) ⊆ diskTestOpen c ρ :=
    closedBall_subset_ball ((hdb j).2.1.trans (hdb j).2.2)
  let e j : 𝓓_{K j}(ℂ,ℝ) →L[ℝ] InteriorDiskTest c ρ := TestFunction.ofSupportedInCLM ℝ (hK j)
  have hsep j : IsSeparable (Set.range (e j)) := by
    let _ : SecondCountableTopology 𝓓_{K j}(ℂ,ℝ) := secondCountable_compactTestSpace (K j)
    simpa only [Set.image_univ] using (IsSeparable.of_separableSpace Set.univ).image (e j).continuous
  have huniv : (⋃ j, Set.range (e j)) = Set.univ := by
    apply eq_univ_of_forall
    intro f
    obtain ⟨j,hf⟩ := exists_compact_disk_exhaustion_for_test c ρ d hcover f
    let g : 𝓓_{K j}(ℂ,ℝ) := ContDiffMapSupportedIn.of_support_subset f.contDiff (subset_tsupport f |>.trans hf)
    exact mem_iUnion.mpr ⟨j,⟨g,by ext z; rfl⟩⟩
  have h := IsSeparable.iUnion hsep
  rw [huniv] at h
  exact isSeparable_univ_iff.mp h

/-- Inclusion of the interior test space into global tests is continuous and linear. -/
noncomputable def interiorDiskTestToGlobalCLM (c : ℂ) (ρ : ℝ) : InteriorDiskTest c ρ →L[ℝ] TestFn :=
  TestFunction.monoCLM ℝ


/-- The continuous inclusion preserves every test value. -/
theorem interiorDiskTestToGlobalCLM_apply (c : ℂ) (ρ : ℝ) (f : InteriorDiskTest c ρ) (z : ℂ) :
    interiorDiskTestToGlobalCLM c ρ f z = f z := by
  change ((TestFunction.monoCLM ℝ f : TestFn) : ℂ → ℝ) z = f z
  rw [TestFunction.monoCLM_apply]
  simp only [le_rfl,le_top,and_self,ite_true]

/-- The global inclusion retains strict interior support. -/
theorem interiorDiskTestToGlobalCLM_tsupport (c : ℂ) (ρ : ℝ) (f : InteriorDiskTest c ρ) :
    tsupport (interiorDiskTestToGlobalCLM c ρ f) ⊆ ball c ρ := by
  have he : (interiorDiskTestToGlobalCLM c ρ f : ℂ → ℝ) = f := funext (interiorDiskTestToGlobalCLM_apply c ρ f)
  rw [he]
  exact f.tsupport_subset

/-- Every global interior test is the inclusion of an actual disk test. -/
theorem exists_interiorDiskTest_of_global (c : ℂ) (ρ : ℝ) (f : TestFn)
    (hf : tsupport f ⊆ ball c ρ) : ∃ g : InteriorDiskTest c ρ, interiorDiskTestToGlobalCLM c ρ g = f := by
  let g : InteriorDiskTest c ρ := ⟨f,f.contDiff,f.hasCompactSupport,hf⟩
  refine ⟨g,?_⟩
  ext z
  rw [interiorDiskTestToGlobalCLM_apply]
  rfl

/-- Integration of a smooth compactly supported test against area measure. -/
noncomputable def testAreaIntegralCLM : TestFn →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) volume (fun _ : ℂ => (1 : ℝ))

/-- The continuous mass functional is the literal area integral. -/
theorem testAreaIntegralCLM_apply (f : TestFn) : testAreaIntegralCLM f = ∫ z : ℂ, f z := by
  rw [testAreaIntegralCLM,TestFunction.integralAgainstBilinCLM_eq_integral
    (continuous_const.continuousOn.locallyIntegrableOn MeasurableSet.univ)]
  simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul,mul_one]

/-- View a distribution as its continuous linear test functional. -/
noncomputable def distributionToTestCLM (D : Distr) : TestFn →L[ℝ] ℝ :=
  (UniformConvergenceCLM.ofFun (F := ℝ) (σ := RingHom.id ℝ) {S : Set TestFn | IsCompact S}).symm D

/-- Reinterpretation preserves every distribution evaluation. -/
theorem distributionToTestCLM_apply (D : Distr) (f : TestFn) : distributionToTestCLM D f = D f := rfl

/-- The exterior-pinned field as an actual samplewise continuous test functional. -/
noncomputable def exteriorPinnedDistributionCLM {Ω : Type*}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (_hR : 0 < R) (ω : Ω) : TestFn →L[ℝ] ℝ :=
  distributionToTestCLM (X ω)-Xc ω 0 (-Real.log R) • testAreaIntegralCLM

/-- Exterior pinning gives a distribution on the original sample space. -/
noncomputable def exteriorPinnedDistribution {Ω : Type*}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R) : Ω → Distr :=
  exteriorPinnedDistributionCLM X Xc R hR

/-- Pinned distribution evaluation agrees with the literal pinned evaluation
`DOZZ.exteriorPinnedEvaluation`. -/
theorem exteriorPinnedDistribution_apply {Ω : Type*}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R) (ω : Ω) (f : TestFn) :
    exteriorPinnedDistribution X Xc R hR ω f = exteriorPinnedEvaluation X Xc R hR ω f := by
  change X ω f-Xc ω 0 (-Real.log R)*testAreaIntegralCLM f = _
  rw [testAreaIntegralCLM_apply]
  rfl

/-- The harmonic sample integral as a continuous functional on the disk's interior test space. -/
noncomputable def interiorHarmonicIntegralCLM (c : ℂ) (ρ : ℝ) (v : ℂ → ℝ) : InteriorDiskTest c ρ →L[ℝ] ℝ :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℝ ℝ) volume v

/-- A continuous harmonic sample has its literal integral on every interior test. -/
theorem interiorHarmonicIntegralCLM_apply (c : ℂ) (ρ : ℝ) (v : ℂ → ℝ)
    (hv : ContinuousOn v (ball c ρ)) (f : InteriorDiskTest c ρ) :
    interiorHarmonicIntegralCLM c ρ v f = ∫ z : ℂ, f z*v z := by
  rw [interiorHarmonicIntegralCLM,TestFunction.integralAgainstBilinCLM_eq_integral
    (hv.locallyIntegrableOn measurableSet_ball)]
  rfl


/-- A samplewise continuous residual functional on the actual interior test space. -/
noncomputable def interiorMarkovResidualCLM {Ω : Type*} (c : ℂ) (ρ : ℝ)
    (Y D : Ω → Distr) (V : Ω → ℂ → ℝ) (ω : Ω) : InteriorDiskTest c ρ →L[ℝ] ℝ :=
  ((distributionToTestCLM (Y ω)-distributionToTestCLM (D ω)).comp (interiorDiskTestToGlobalCLM c ρ))-
    interiorHarmonicIntegralCLM c ρ (V ω)

/-- On continuous samples the residual functional has the literal integral formula. -/
theorem interiorMarkovResidualCLM_apply {Ω : Type*} (c : ℂ) (ρ : ℝ)
    (Y D : Ω → Distr) (V : Ω → ℂ → ℝ) (ω : Ω)
    (hV : ContinuousOn (V ω) (ball c ρ)) (f : InteriorDiskTest c ρ) :
    interiorMarkovResidualCLM c ρ Y D V ω f =
      Y ω (interiorDiskTestToGlobalCLM c ρ f)-D ω (interiorDiskTestToGlobalCLM c ρ f)-
        (∫ z : ℂ, interiorDiskTestToGlobalCLM c ρ f z*V ω z) := by
  change Y ω (interiorDiskTestToGlobalCLM c ρ f)-D ω (interiorDiskTestToGlobalCLM c ρ f)-
    interiorHarmonicIntegralCLM c ρ (V ω) f = _
  rw [interiorHarmonicIntegralCLM_apply c ρ (V ω) hV f]
  simp_rw [interiorDiskTestToGlobalCLM_apply]

/-- Testwise interior harmonic agreement holds for all interior tests on one event. -/
theorem ae_all_interior_harmonic_test_agreement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (Y D : Ω → Distr) (V : Ω → ℂ → ℝ)
    (hV : ∀ᵐ ω ∂P, ContinuousOn (V ω) (ball c ρ))
    (hagree : ∀ f : TestFn, tsupport f ⊆ ball c ρ →
      (fun ω => Y ω f-D ω f) =ᵐ[P] fun ω => ∫ z : ℂ, f z*V ω z) :
    ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ ball c ρ → Y ω f-D ω f = ∫ z : ℂ, f z*V ω z := by
  let _ : SeparableSpace (InteriorDiskTest c ρ) := separableSpace_interiorDiskTest c ρ hρ
  have hzero : ∀ f : InteriorDiskTest c ρ,
      (fun ω => interiorMarkovResidualCLM c ρ Y D V ω f) =ᵐ[P] 0 := by
    intro f
    filter_upwards [hV,hagree (interiorDiskTestToGlobalCLM c ρ f)
      (interiorDiskTestToGlobalCLM_tsupport c ρ f)] with ω hVω hfω
    rw [interiorMarkovResidualCLM_apply c ρ Y D V ω hVω f,hfω,sub_self]
    rfl
  have hz := ae_forall_continuous_eq_zero P (fun ω f => interiorMarkovResidualCLM c ρ Y D V ω f)
    (fun ω => (interiorMarkovResidualCLM c ρ Y D V ω).continuous) hzero
  filter_upwards [hV,hz] with ω hVω hω
  intro f hf
  obtain ⟨g,hg⟩ := exists_interiorDiskTest_of_global c ρ f hf
  have hh := hω g
  rw [interiorMarkovResidualCLM_apply c ρ Y D V ω hVω g,hg] at hh
  exact sub_eq_zero.mp hh


/-- The supported distribution retains the literal residual formula on every interior test. -/
theorem dirichletDistribution_interior_apply_ae_eq {Ω : Type*} [MeasurableSpace Ω]
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
    (hm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    (fun ω => dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f) =ᵐ[P]
      fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f-(∫ z, f z*V ω z) := by
  have h := dirichletDistribution_apply_ae_eq P X Xc hX hc c R ρ (by linarith) V hV hU f
  rw [dirichletCompletedL2Map_apply_interior P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f hf] at h
  exact h.trans (dirichletResidualL2_ae_eq P X Xc hX hc c R ρ (by linarith) V hm hV hU f hf)

/-- The actual pinned complement agrees with its harmonic family for every interior test on one event. -/
theorem ae_dirichletDistribution_interior_harmonic_agreement {Ω : Type*} [MeasurableSpace Ω]
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
    (hm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hVc : ∀ᵐ ω ∂P, ContinuousOn (V ω) (ball c ρ)) :
    ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ ball c ρ →
      exteriorPinnedEvaluation X Xc R (by linarith) ω f-dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU ω f = ∫ z : ℂ, f z*V ω z := by
  have h := ae_all_interior_harmonic_test_agreement P c ρ hρ
    (exteriorPinnedDistribution X Xc R (by linarith)) (dirichletDistribution P X Xc hX hc c R ρ (by linarith) V hV hU) V hVc
    (fun f hf => by
      filter_upwards [dirichletDistribution_interior_apply_ae_eq P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim hm f hf] with ω hω
      rw [exteriorPinnedDistribution_apply,hω]
      ring)
  simpa only [exteriorPinnedDistribution_apply] using h


/-- The finite global complementary field as a continuous samplewise test functional. -/
noncomputable def finiteMarkovComplementCLM {Ω : Type*} {n : ℕ}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (ω : Ω) : TestFn →L[ℝ] ℝ :=
  exteriorPinnedDistributionCLM X Xc R hR ω-∑ i, distributionToTestCLM (D i ω)

/-- The finite complementary field as a distribution on the original sample space. -/
noncomputable def finiteMarkovComplement {Ω : Type*} {n : ℕ}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) : Ω → Distr := finiteMarkovComplementCLM X Xc R hR D

/-- Complementary evaluation retains its literal finite sum. -/
theorem finiteMarkovComplement_apply {Ω : Type*} {n : ℕ}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (ω : Ω) (f : TestFn) :
    finiteMarkovComplement X Xc R hR D ω f = exteriorPinnedEvaluation X Xc R hR ω f-∑ i, D i ω f := by
  change exteriorPinnedDistributionCLM X Xc R hR ω f-(∑ i, distributionToTestCLM (D i ω)) f = _
  rw [sum_apply]
  simp only [distributionToTestCLM_apply]
  exact congrArg (fun y => y-∑ i, D i ω f) (exteriorPinnedDistribution_apply X Xc R hR ω f)

/-- Exterior-pinned finite decomposition holds simultaneously for every sample and every test. -/
theorem finiteMarkovComplement_decomposition {Ω : Type*} {n : ℕ}
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (ω : Ω) (f : TestFn) :
    exteriorPinnedEvaluation X Xc R hR ω f = (∑ i, D i ω f)+finiteMarkovComplement X Xc R hR D ω f := by
  rw [finiteMarkovComplement_apply]
  ring

/-- Equator restoration of the finite decomposition holds for every test on one event. -/
theorem ae_finiteMarkovComplement_restoration {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) (D : Fin n → Ω → Distr) :
    ∀ᵐ ω ∂P, ∀ f : TestFn, X ω f = (∑ i, D i ω f)+finiteMarkovComplement X Xc R hR D ω f-
      equatorRestorationScalar Xc R hR ω*(∫ z : ℂ, f z) := by
  filter_upwards [equatorRestorationScalar_ae_eq_neg_circle X Xc hc R hR] with ω hω
  intro f
  rw [finiteMarkovComplement_apply,hω]
  unfold exteriorPinnedEvaluation
  ring

/-- Every complementary test evaluation is measurable. -/
theorem measurable_finiteMarkovComplement_apply {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (hD : ∀ i (f : TestFn), Measurable (fun ω => D i ω f)) (f : TestFn) :
    Measurable (fun ω => finiteMarkovComplement X Xc R hR D ω f) := by
  simp_rw [finiteMarkovComplement_apply]
  exact (exteriorPinnedEvaluation_measurable X Xc hX hc R hR f).sub
    (Finset.measurable_sum Finset.univ (fun i _ => hD i f))

/-- Complementary test evaluations stay in random L². -/
theorem finiteMarkovComplement_apply_memLp {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (hD : ∀ i (f : TestFn), MemLp (fun ω => D i ω f) 2 P) (f : TestFn) :
    MemLp (fun ω => finiteMarkovComplement X Xc R hR D ω f) 2 P := by
  simp_rw [finiteMarkovComplement_apply]
  exact (exteriorPinnedEvaluation_memLp X Xc hX hc R hR f).sub
    (memLp_finsetSum Finset.univ (fun i _ => hD i f))

/-- Centered Dirichlet distributions give a centered global complement. -/
theorem finiteMarkovComplement_apply_integral_zero {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (hD : ∀ i (f : TestFn), MemLp (fun ω => D i ω f) 2 P)
    (hmean : ∀ i (f : TestFn), (∫ ω, D i ω f ∂P) = 0) (f : TestFn) :
    (∫ ω, finiteMarkovComplement X Xc R hR D ω f ∂P) = 0 := by
  let _ := hX.1
  simp_rw [finiteMarkovComplement_apply]
  rw [integral_sub ((exteriorPinnedEvaluation_memLp X Xc hX hc R hR f).integrable (by norm_num))
    ((memLp_finsetSum Finset.univ (fun i _ => hD i f)).integrable (by norm_num)),
    exteriorPinnedEvaluation_integral_zero P X Xc hX hc R hR,
    integral_finsetSum Finset.univ (fun i _ => (hD i f).integrable (by norm_num))]
  simp only [hmean,Finset.sum_const_zero,sub_zero]

/-- Local harmonic agreements and exterior supports assemble into one finite-family event. -/
theorem ae_finiteMarkovComplement_harmonic_agreement {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (c : Fin n → ℂ) (ρ : ℝ) (D : Fin n → Ω → Distr) (V : Fin n → Ω → ℂ → ℝ)
    (hsep : ∀ i j, j ≠ i → ∀ f : TestFn, tsupport f ⊆ ball (c i) ρ → tsupport f ⊆ (closedBall (c j) ρ)ᶜ)
    (hlocal : ∀ i, ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ ball (c i) ρ →
      exteriorPinnedEvaluation X Xc R hR ω f-D i ω f = ∫ z : ℂ, f z*V i ω z)
    (hexterior : ∀ i, ∀ᵐ ω ∂P, ∀ f : TestFn, tsupport f ⊆ (closedBall (c i) ρ)ᶜ → D i ω f = 0) :
    ∀ᵐ ω ∂P, ∀ i (f : TestFn), tsupport f ⊆ ball (c i) ρ →
      finiteMarkovComplement X Xc R hR D ω f = ∫ z : ℂ, f z*V i ω z := by
  classical
  filter_upwards [ae_all_iff.mpr hlocal,ae_all_iff.mpr hexterior] with ω hlocalω hexteriorω
  intro i f hf
  have hsum : (∑ j, D j ω f) = D i ω f := by
    exact Finset.sum_eq_single i (fun j _ hji => hexteriorω j f (hsep i j hji f hf))
      (fun hi => (hi (Finset.mem_univ i)).elim)
  rw [finiteMarkovComplement_apply,hsum]
  exact hlocalω i f hf

/-- A positive separation margin places each interior disk outside every other closed disk. -/
theorem interior_disk_subset_exterior_closed_disk (c d : ℂ) (ρ δ : ℝ) (hδ : 0 < δ)
    (hsep : 2*ρ+δ ≤ dist c d) : ball c ρ ⊆ (closedBall d ρ)ᶜ := by
  intro z hz hzd
  have hc := mem_ball.mp hz
  have hd := mem_closedBall.mp hzd
  have ht : dist c d ≤ dist z c+dist z d := by
    simpa only [dist_comm c z] using dist_triangle c z d
  linarith

/-- The finite-center separation hypothesis of `DOZZ.exists_exteriorPinned_markov_uniform` implies
the support condition for harmonic assembly. -/
theorem separated_interior_test_support_exterior {n : ℕ} (c : Fin n → ℂ) (ρ δ : ℝ)
    (hδ : 0 < δ) (hsep : ∀ i j, i ≠ j → 2*ρ+δ ≤ dist (c i) (c j))
    (i j : Fin n) (hji : j ≠ i) (f : TestFn) (hf : tsupport f ⊆ ball (c i) ρ) :
    tsupport f ⊆ (closedBall (c j) ρ)ᶜ :=
  hf.trans (interior_disk_subset_exterior_closed_disk (c i) (c j) ρ δ hδ (hsep i j hji.symm))
end DOZZ.Proofs
