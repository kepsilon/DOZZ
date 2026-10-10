/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.MarkovCommonEvents
/-!
# Finite Dirichlet block Gaussianity and independence

All disk completions and their Poisson limits stay in the shared original Gaussian
Hilbert span. Separated collars give zero cross-disk covariance, preserved by both
harmonic integration and restriction completion. Coordinatewise distribution versions
retain the Gaussian block independence, with the literal finite complement included.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped Topology ENNReal NNReal InnerProductSpace
namespace DOZZ.Proofs

/-- Inclusion of generators into a closed Gaussian span includes their whole closed span. -/
theorem gaussianHilbertSpan_le_of_mem {Ω I J : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : I → Lp ℝ 2 P) (Z : J → Lp ℝ 2 P)
    (hZ : ∀ j, Z j ∈ gaussianHilbertSpan Y) : gaussianHilbertSpan Z ≤ gaussianHilbertSpan Y := by
  apply Submodule.topologicalClosure_minimal
  · exact Submodule.span_le.mpr (fun u hu => by obtain ⟨j,rfl⟩ := hu; exact hZ j)
  · exact Submodule.isClosed_topologicalClosure _

/-- Every actual exterior-pinned test is in the original circle-and-test Gaussian span. -/
theorem exteriorPinnedTestL2_mem_original_gaussianHilbertSpan {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) (f : TestFn) :
    exteriorPinnedTestL2 P X Xc hX hc R hR f ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
  let Z := gffStructureL2Family X Xc hX hc
  have he : exteriorPinnedTestL2 P X Xc hX hc R hR f =
      Z (Sum.inr f)-(∫ z : ℂ, f z) • Z (Sum.inl (0,-Real.log R)) := by
    apply Lp.ext
    filter_upwards [exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f,
      gffStructureL2Family_ae_eq X Xc hX hc (Sum.inr f),
      gffStructureL2Family_ae_eq X Xc hX hc (Sum.inl (0,-Real.log R)),
      Lp.coeFn_smul (∫ z : ℂ, f z) (Z (Sum.inl (0,-Real.log R))),
      Lp.coeFn_sub (Z (Sum.inr f)) ((∫ z : ℂ, f z) • Z (Sum.inl (0,-Real.log R)))] with ω hy hf hp hs hsub
    rw [hsub,Pi.sub_apply,hs,Pi.smul_apply,smul_eq_mul]
    change _ = Z (Sum.inr f) ω-(∫ z : ℂ, f z)*Z (Sum.inl (0,-Real.log R)) ω
    rw [hf,hp,hy]
    unfold exteriorPinnedEvaluation
    simp only [Sum.elim_inl,Sum.elim_inr]
    ring
  rw [he]
  exact Submodule.sub_mem _ (mem_gaussianHilbertSpan Z (Sum.inr f))
    (Submodule.smul_mem _ _ (mem_gaussianHilbertSpan Z (Sum.inl (0,-Real.log R))))

/-- The actual pointwise Poisson limit stays in the original circle-and-test Gaussian span. -/
theorem poissonFamilyL2_mem_original_gaussianHilbertSpan {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R hR ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (z : ℂ) : poissonFamilyL2 P c ρ V hV z ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
  by_cases hz : z ∈ ball c ρ
  · have ht := tendsto_toLp_of_eLpNorm_sub
      (fun k => exteriorPinnedEvaluation_memLp X Xc hX hc R hR (canonicalPoissonCollarTest c z ρ ε hρ hε hz k))
      (hV z hz) (hlim z hz)
    rw [poissonFamilyL2,dite_eq_left hz]
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto ht
    exact Eventually.of_forall (fun k => exteriorPinnedTestL2_mem_original_gaussianHilbertSpan P X Xc hX hc R hR _)
  · simp only [poissonFamilyL2,dite_eq_right hz]
    exact Submodule.zero_mem _

/-- All single-disk harmonic and original test generators belong to the shared original span. -/
theorem poissonTestFamilyL2_gaussianHilbertSpan_le_original {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R hR ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) :
    gaussianHilbertSpan (poissonTestFamilyL2 P X Xc hX hc c R ρ hR V hV) ≤
      gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) := by
  apply gaussianHilbertSpan_le_of_mem P
  intro t
  cases t with
  | inl z => exact poissonFamilyL2_mem_original_gaussianHilbertSpan P X Xc hX hc c R ρ ε hR hρ hε V hV hlim z.1
  | inr f => exact exteriorPinnedTestL2_mem_original_gaussianHilbertSpan P X Xc hX hc R hR f

/-- All completed disk variables share the original circle-and-test Gaussian span. -/
theorem dirichletCompletedL2Map_mem_original_gaussianHilbertSpan {Ω : Type*} [MeasurableSpace Ω]
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
    (u : Lp ℝ 2 (volume.restrict (ball c ρ))) :
    dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU u ∈ gaussianHilbertSpan (gffStructureL2Family X Xc hX hc) :=
  poissonTestFamilyL2_gaussianHilbertSpan_le_original P X Xc hX hc c R ρ ε (by linarith) hρ hε V hV hlim
    (dirichletCompletedL2Map_mem_gaussianHilbertSpan P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim u)

/-- Finite test processes with a literal global complementary block, in random L². -/
noncomputable def finiteMarkovTestL2Family {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (Y : TestFn → Lp ℝ 2 P) (D : Fin n → TestFn → Lp ℝ 2 P) :
    Option (Fin n) → TestFn → Lp ℝ 2 P :=
  fun j f => match j with
    | none => Y f-∑ i, D i f
    | some i => D i f

/-- All finite Dirichlet blocks and their global complement retain joint Gaussianity in a shared span. -/
theorem finiteMarkovTestL2Family_isGaussianProcess {Ω I : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : I → Lp ℝ 2 P)
    (hZ : IsGaussianProcess (fun i => ⇑(Z i)) P)
    (Y : TestFn → Lp ℝ 2 P) (D : Fin n → TestFn → Lp ℝ 2 P)
    (hY : ∀ f, Y f ∈ gaussianHilbertSpan Z) (hD : ∀ i f, D i f ∈ gaussianHilbertSpan Z) :
    IsGaussianProcess (fun p : (_j : Option (Fin n)) × TestFn => ⇑(finiteMarkovTestL2Family P Y D p.1 p.2)) P := by
  apply isGaussianProcess_of_mem_gaussianHilbertSpan hZ
  intro p
  cases p.1 with
  | none => exact Submodule.sub_mem _ (hY p.2) (Submodule.sum_mem _ (fun i _ => hD i p.2))
  | some i => exact hD i p.2

/-- Exact Green mixed covariance and zero cross-disk covariance make each block orthogonal to the complement. -/
theorem finiteMarkovTestL2Family_covariance_complement_zero {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : TestFn → Lp ℝ 2 P)
    (D : Fin n → TestFn → Lp ℝ 2 P)
    (hself : ∀ i f g, covariance (D i f) (Y g) P = covariance (D i f) (D i g) P)
    (hcross : ∀ i j, i ≠ j → ∀ f g, covariance (D i f) (D j g) P = 0)
    (i : Fin n) (f g : TestFn) :
    covariance (D i f) (finiteMarkovTestL2Family P Y D none g) P = 0 := by
  classical
  change covariance (D i f) (⇑(Y g-∑ j, D j g)) P = 0
  rw [covariance_L2_sub_right]
  have hsum : covariance (D i f) (⇑(∑ j, D j g)) P = ∑ j, covariance (D i f) (D j g) P := by
    rw [covariance_L2_eq]
    simp_rw [covariance_L2_eq]
    have hm : (∫ ω, (∑ j, D j g) ω ∂P) = ∑ j, ∫ ω, D j g ω ∂P := by
      rw [integral_congr_ae (Lp.coeFn_fun_finsetSum Finset.univ (fun j => D j g))]
      exact integral_finsetSum Finset.univ (fun j _ => (Lp.memLp (D j g)).integrable (by norm_num))
    rw [inner_sum,hm,Finset.sum_sub_distrib,Finset.mul_sum]
  rw [hsum,Finset.sum_eq_single i]
  · rw [hself,sub_self]
  · intro j hj hji
    exact hcross i j hji.symm f g
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- A covariance vanishes at an L² limit if it vanishes throughout the approximating sequence. -/
theorem covariance_L2_limit_right_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (U V : Lp ℝ 2 P) (W : ℕ → Lp ℝ 2 P)
    (hW : Tendsto W atTop (𝓝 V)) (hzero : ∀ k, covariance U (W k) P = 0) :
    covariance U V P = 0 := by
  have ht := tendsto_covariance_of_tendsto_L2 (U := fun _ : ℕ => U) tendsto_const_nhds hW
  have he : (fun k => covariance U (W k) P) = fun _ : ℕ => (0 : ℝ) := funext hzero
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- A collar about one center avoids the closed disk of a separated center. -/
theorem tsupport_canonicalPoissonCollarTest_exterior_other (c d z : ℂ) (ρ ε δ : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (hεδ : ε < δ)
    (hsep : 2*ρ+δ ≤ dist c d) (hz : z ∈ ball d ρ) (k : ℕ) :
    tsupport (canonicalPoissonCollarTest d z ρ ε hρ hε hz k) ⊆ (closedBall c ρ)ᶜ := by
  intro w hw hc
  have hann := tsupport_poissonCollarValue_annulus d z ρ (ε/((k : ℝ)+1)) hρ hz
    (poissonCollarDensity ε hε k) (tsupport_poissonCollarDensity_subset ε hε k) hw
  have hd : dist w d < ρ+ε := by
    simpa only [dist_eq_norm] using hann.2.trans_le (add_le_add_right (poissonCollarWidth_le ε hε k) ρ)
  have hc' : dist w c ≤ ρ := hc
  have ht := dist_triangle c w d
  rw [dist_comm c w] at ht
  linarith only [hsep,hd,hc',ht,hεδ]

/-- Vanishing on a dense family of interior restrictions makes every completed test orthogonal. -/
theorem covariance_completed_disk_map_zero_of_interior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (W : Lp ℝ 2 P)
    (hzero : ∀ g : TestFn, tsupport g ⊆ ball c ρ → covariance W (T (diskTestRestrictionL2 c ρ g)) P = 0)
    (f : TestFn) : covariance W (T (diskTestRestrictionL2 c ρ f)) P = 0 := by
  obtain ⟨g,hg,hlim⟩ := exists_interior_test_restriction_approx c ρ hρ f
  exact covariance_L2_limit_right_eq_zero P W _ (fun k => T (diskTestRestrictionL2 c ρ (g k)))
    (T.continuous.tendsto _ |>.comp hlim) (fun k => hzero (g k) (hg k))

/-- A pointwise harmonic collar limit is orthogonal to any variable orthogonal to exterior tests. -/
theorem covariance_poissonFamilyL2_zero_of_exterior_tests {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c d : ℂ) (R ρ ε δ : ℝ) (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hsep : 2*ρ+δ ≤ dist c d)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball d ρ, MemLp (fun ω => V ω z) 2 P)
    (hlim : ∀ z (hz : z ∈ ball d ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R hR ω
        (canonicalPoissonCollarTest d z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (W : Lp ℝ 2 P)
    (hzero : ∀ f : TestFn, tsupport f ⊆ (closedBall c ρ)ᶜ →
      covariance W (exteriorPinnedTestL2 P X Xc hX hc R hR f) P = 0)
    (z : ℂ) : covariance W (poissonFamilyL2 P d ρ V hV z) P = 0 := by
  let _ := hX.1
  by_cases hz : z ∈ ball d ρ
  · rw [poissonFamilyL2,dite_eq_left hz]
    apply covariance_L2_limit_right_eq_zero P W _
      (fun k => exteriorPinnedTestL2 P X Xc hX hc R hR (canonicalPoissonCollarTest d z ρ ε hρ hε hz k))
    · exact tendsto_toLp_of_eLpNorm_sub
        (fun k => exteriorPinnedEvaluation_memLp X Xc hX hc R hR _)
        (hV z hz) (hlim z hz)
    · intro k
      exact hzero _ (tsupport_canonicalPoissonCollarTest_exterior_other c d z ρ ε δ hρ hε hεδ hsep hz k)
  · simp only [poissonFamilyL2,dite_eq_right hz]
    rw [covariance_L2_eq,inner_zero_right]
    have hm : (∫ ω, (0 : Lp ℝ 2 P) ω ∂P) = 0 := by
      rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 P)]
      exact integral_zero Ω ℝ
    rw [hm,mul_zero,sub_self]

/-- Orthogonality to every point of a harmonic family passes through compact test integration. -/
theorem covariance_poissonTestIntegralL2_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (W : Lp ℝ 2 P) (hzero : ∀ z, covariance W (poissonFamilyL2 P c ρ V hV z) P = 0)
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    covariance W (poissonTestIntegralL2 P c ρ V hV f) P = 0 := by
  rw [covariance_comm,poissonTestIntegralL2_covariance P c ρ V hV hmean hU f hf]
  simp only [← covariance_comm W,hzero,mul_zero,integral_zero]

/-- Completed Dirichlet tests on separated disks have exactly zero cross covariance. -/
theorem dirichletCompletedL2Map_separated_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
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
    (d : ℂ) (hpinD : ‖d‖+ρ ≤ R) (δ : ℝ) (hδ : 0 < δ) (hεδ : ε < δ)
    (hsep : 2*ρ+δ ≤ dist c d)
    (W : Ω → ℂ → ℝ) (hW : ∀ z ∈ ball d ρ, MemLp (fun ω => W ω z) 2 P)
    (hmeanW : ∀ z ∈ ball d ρ, (∫ ω, W ω z ∂P) = 0)
    (hUW : ContinuousOn (poissonFamilyL2 P d ρ W hW) (ball d ρ))
    (hcovW : ∀ z w, z ∈ ball d ρ → w ∈ ball d ρ →
      covariance (fun ω => W ω z) (fun ω => W ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-d)*star (w-d)‖)
    (hlimW : ∀ z (hz : z ∈ ball d ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest d z ρ ε hρ hε hz k)-W ω z) 2 P) atTop (𝓝 0))
    (f g : TestFn) :
    covariance
      (dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU (diskTestRestrictionL2 c ρ f))
      (dirichletCompletedL2Map P X Xc hX hc d R ρ (by linarith) W hW hUW (diskTestRestrictionL2 d ρ g)) P = 0 := by
  let _ := hX.1
  let T := dirichletCompletedL2Map P X Xc hX hc c R ρ (by linarith) V hV hU
  let S := dirichletCompletedL2Map P X Xc hX hc d R ρ (by linarith) W hW hUW
  have hext : ∀ t : TestFn, tsupport t ⊆ (closedBall c ρ)ᶜ →
      covariance (T (diskTestRestrictionL2 c ρ f))
        (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) t) P = 0 := by
    intro t ht
    exact dirichletCompletedL2Map_exterior_covariance_zero P X Xc hX hc c R ρ ε hR hρ hε hpin
      V hV hmean hU hcov hlim f t ht
  apply covariance_completed_disk_map_zero_of_interior P d ρ hρ S (T (diskTestRestrictionL2 c ρ f)) _ g
  intro t ht
  rw [dirichletCompletedL2Map_apply_interior P X Xc hX hc d R ρ ε hR hρ hε hpinD
    W hW hmeanW hUW hcovW hlimW t ht]
  rw [dirichletResidualL2,covariance_L2_sub_right]
  have htsep : tsupport t ⊆ (closedBall c ρ)ᶜ := by
    intro z hz
    have hz' := ht hz
    have h := interior_disk_subset_exterior_closed_disk d c ρ δ hδ (by simpa only [dist_comm] using hsep)
    exact h hz'
  rw [hext t htsep]
  have hpoint := covariance_poissonFamilyL2_zero_of_exterior_tests P X Xc hX hc c d R ρ ε δ
    (by linarith) hρ hε hεδ hsep W hW hlimW (T (diskTestRestrictionL2 c ρ f)) hext
  rw [covariance_poissonTestIntegralL2_zero P d ρ W hW hmeanW hUW _ hpoint t ht,sub_self]

/-- Coordinatewise versions of the finite Gaussian family retain joint Gaussianity. -/
theorem finiteMarkovVersion_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (Y : TestFn → Lp ℝ 2 P) (D : Fin n → TestFn → Lp ℝ 2 P)
    (U : Option (Fin n) → TestFn → Ω → ℝ)
    (hG : IsGaussianProcess (fun p : (_j : Option (Fin n)) × TestFn =>
      ⇑(finiteMarkovTestL2Family P Y D p.1 p.2)) P)
    (hU : ∀ j f, U j f =ᵐ[P] ⇑(finiteMarkovTestL2Family P Y D j f)) :
    IsGaussianProcess (fun p : (_j : Option (Fin n)) × TestFn => U p.1 p.2) P :=
  hG.congr (fun p => (hU p.1 p.2).symm)

/-- Exact coordinatewise versions of the orthogonal blocks are mutually independent. -/
theorem finiteMarkovVersion_iIndepFun {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : TestFn → Lp ℝ 2 P)
    (D : Fin n → TestFn → Lp ℝ 2 P) (U : Option (Fin n) → TestFn → Ω → ℝ)
    (hG : IsGaussianProcess (fun p : (_j : Option (Fin n)) × TestFn =>
      ⇑(finiteMarkovTestL2Family P Y D p.1 p.2)) P)
    (hU : ∀ j f, U j f =ᵐ[P] ⇑(finiteMarkovTestL2Family P Y D j f))
    (hself : ∀ i f g, covariance (D i f) (Y g) P = covariance (D i f) (D i g) P)
    (hcross : ∀ i j, i ≠ j → ∀ f g, covariance (D i f) (D j g) P = 0) :
    iIndepFun (fun j ω f => U j f ω) P := by
  apply (finiteMarkovVersion_isGaussianProcess P Y D U hG hU).iIndepFun_of_covariance_eq_zero
    (fun j f => ((Lp.memLp (finiteMarkovTestL2Family P Y D j f)).ae_eq (hU j f).symm).aemeasurable)
  intro j k hjk f g
  rw [covariance_congr_ae (hU j f) (hU k g)]
  cases j with
  | none =>
    cases k with
    | none => exact (hjk rfl).elim
    | some i =>
      rw [covariance_comm]
      exact finiteMarkovTestL2Family_covariance_complement_zero P Y D hself hcross i g f
  | some i =>
    cases k with
    | none => exact finiteMarkovTestL2Family_covariance_complement_zero P Y D hself hcross i f g
    | some j => exact hcross i j (fun he => hjk (congrArg some he)) f g

/-- The literal finite complementary distribution represents its finite random L² residual. -/
theorem finiteMarkovComplement_apply_ae_eq {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R)
    (D : Fin n → Ω → Distr) (T : Fin n → TestFn → Lp ℝ 2 P)
    (hD : ∀ i (f : TestFn), (fun ω => D i ω f) =ᵐ[P] ⇑(T i f)) (f : TestFn) :
    (fun ω => finiteMarkovComplement X Xc R hR D ω f) =ᵐ[P]
      ⇑(exteriorPinnedTestL2 P X Xc hX hc R hR f-∑ i, T i f) := by
  have hDa : ∀ᵐ ω ∂P, ∀ i, D i ω f = T i f ω := ae_all_iff.mpr (fun i => hD i f)
  filter_upwards [hDa,exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f,
    Lp.coeFn_fun_finsetSum Finset.univ (fun i => T i f),
    Lp.coeFn_sub (exteriorPinnedTestL2 P X Xc hX hc R hR f) (∑ i, T i f)] with ω hd hy hs hsub
  rw [finiteMarkovComplement_apply,hsub,Pi.sub_apply,hs]
  simp only [hd,hy]

/-- A test supported off the open union is zero on each component disk. -/
theorem exterior_union_test_eqOn_zero {n : ℕ} (c : Fin n → ℂ) (ρ : ℝ)
    (f : TestFn) (hf : tsupport f ⊆ (⋃ i, ball (c i) ρ)ᶜ) (i : Fin n) :
    EqOn f 0 (ball (c i) ρ) := by
  intro z hz
  change f z = 0
  by_contra hne
  exact hf (subset_closure hne) (mem_iUnion.mpr ⟨i,hz⟩)

/-- Open-union exterior tests have zero disk Green pairing, including boundary contact. -/
theorem diskGreenCovariance_eq_zero_of_exterior_union {n : ℕ} (c : Fin n → ℂ)
    (ρ : ℝ) (hρ : 0 < ρ) (i : Fin n) (f g : TestFn)
    (hg : tsupport g ⊆ (⋃ j, ball (c j) ρ)ᶜ) : diskGreenCovariance (c i) ρ hρ f g = 0 := by
  rw [diskGreenCovariance_symm]
  exact diskGreenCovariance_eq_zero_of_eqOn_zero (c i) ρ hρ g f
    (exterior_union_test_eqOn_zero c ρ g hg i)

/-- Each coordinate block of the finite joint Gaussian process is itself Gaussian. -/
theorem finiteMarkovVersion_block_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (Y : TestFn → Lp ℝ 2 P) (D : Fin n → TestFn → Lp ℝ 2 P)
    (U : Option (Fin n) → TestFn → Ω → ℝ)
    (hG : IsGaussianProcess (fun p : (_j : Option (Fin n)) × TestFn =>
      ⇑(finiteMarkovTestL2Family P Y D p.1 p.2)) P)
    (hU : ∀ j f, U j f =ᵐ[P] ⇑(finiteMarkovTestL2Family P Y D j f))
    (j : Option (Fin n)) : IsGaussianProcess (U j) P :=
  (finiteMarkovVersion_isGaussianProcess P Y D U hG hU).comp_right (fun f => ⟨j,f⟩)

/-- A finite family of Dirichlet versions is independent of any orthogonal original test family. -/
theorem finiteDirichletVersion_indep_pinned {Ω I J : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : I → Lp ℝ 2 P)
    (hZ : IsGaussianProcess (fun i => ⇑(Z i)) P)
    (D : Fin n → TestFn → Lp ℝ 2 P) (Y : J → Lp ℝ 2 P)
    (hD : ∀ i f, D i f ∈ gaussianHilbertSpan Z) (hY : ∀ j, Y j ∈ gaussianHilbertSpan Z)
    (U : Fin n → TestFn → Ω → ℝ) (V : J → Ω → ℝ)
    (hU : ∀ i f, U i f =ᵐ[P] ⇑(D i f)) (hV : ∀ j, V j =ᵐ[P] ⇑(Y j))
    (hzero : ∀ i f j, covariance (D i f) (Y j) P = 0) :
    IndepFun (fun ω (p : Fin n × TestFn) => U p.1 p.2 ω) (fun ω j => V j ω) P := by
  let W : (Fin n × TestFn) ⊕ J → Lp ℝ 2 P := Sum.elim (fun p => D p.1 p.2) Y
  have hW : IsGaussianProcess (fun t => ⇑(W t)) P := by
    apply isGaussianProcess_of_mem_gaussianHilbertSpan hZ
    intro t
    cases t with
    | inl p => exact hD p.1 p.2
    | inr j => exact hY j
  have hraw : IsGaussianProcess (Sum.elim (fun p : Fin n × TestFn => U p.1 p.2) V) P := by
    apply hW.congr
    intro t
    cases t with
    | inl p => exact (hU p.1 p.2).symm
    | inr j => exact (hV j).symm
  apply hraw.indepFun_of_covariance_eq_zero
    (fun p => ((Lp.memLp (D p.1 p.2)).ae_eq (hU p.1 p.2).symm).aemeasurable)
    (fun j => ((Lp.memLp (Y j)).ae_eq (hV j).symm).aemeasurable)
  intro p j
  rw [covariance_congr_ae (hU p.1 p.2) (hV j)]
  exact hzero p.1 p.2 j

end DOZZ.Proofs
