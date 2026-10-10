/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonMixed
/-!
# Interior Dirichlet residuals

Compact interior tests can be integrated against the original harmonic family in L². These
Bochner integrals retain their samplewise formulas, centering and joint Gaussian carrier.
Subtracting them from the original pinned tests gives the actual interior Dirichlet residual,
with exact global mixed Green covariance, exact residual Green covariance, orthogonality to
interior harmonic averages and a bounded disk L² estimate. Global restriction completion and
supported samplewise distribution versions remain separate constructions.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs

/-- A compact interior test localizes any continuous disk-valued family. -/
theorem continuous_testFn_smul_on_disk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (ρ : ℝ) (U : ℂ → E) (hU : ContinuousOn U (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) : Continuous (fun z => f z • U z) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ ball c ρ
  · exact f.continuous.continuousAt.smul (hU.continuousAt (isOpen_ball.mem_nhds hz))
  · have hzs : z ∉ tsupport f := fun h => hz (hf h)
    apply (show ContinuousAt (fun _ : ℂ => (0 : E)) z from continuousAt_const).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzs] with w hw
    change f w = 0 at hw
    rw [hw,zero_smul]

/-- Compact interior weights make the disk L² family Bochner integrable. -/
theorem integrable_testFn_smul_on_disk {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℂ) (ρ : ℝ) (U : ℂ → E) (hU : ContinuousOn U (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) : Integrable (fun z => f z • U z) :=
  (continuous_testFn_smul_on_disk c ρ U hU f hf).integrable_of_hasCompactSupport f.hasCompactSupport.smul_right

/-- Zero extension of the original harmonic coordinates into their probability-space L². -/
noncomputable def poissonFamilyL2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℂ) (ρ : ℝ) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (z : ℂ) : Lp ℝ 2 P := by
  classical
  exact if hz : z ∈ ball c ρ then (hV z hz).toLp (fun ω => V ω z) else 0

/-- Interior L² representatives retain the literal harmonic coordinates. -/
theorem poissonFamilyL2_ae_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℂ) (ρ : ℝ) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (z : ℂ) (hz : z ∈ ball c ρ) : poissonFamilyL2 P c ρ V hV z =ᵐ[P] fun ω => V ω z := by
  simp only [poissonFamilyL2,dite_eq_left hz]
  exact MemLp.coeFn_toLp _


/-- The centered harmonic test average is defined in the original L² carrier. -/
noncomputable def poissonTestIntegralL2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℂ) (ρ : ℝ) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (f : TestFn) : Lp ℝ 2 P := ∫ z, f z • poissonFamilyL2 P c ρ V hV z

/-- Samplewise Fubini retains the literal harmonic test integral. -/
theorem poissonTestIntegralL2_ae_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ)
    (V : Ω → ℂ → ℝ) (hm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    poissonTestIntegralL2 P c ρ V hV f =ᵐ[P] fun ω => ∫ z, f z*V ω z := by
  apply L2_integral_ae_eq_integral volume (fun z => f z • poissonFamilyL2 P c ρ V hV z)
    (integrable_testFn_smul_on_disk c ρ _ hU f hf) (fun z ω => f z*V ω z)
  · exact ((f.continuous.measurable.comp measurable_fst).mul
      (hm.comp measurable_swap)).aestronglyMeasurable
  · intro z
    by_cases hz : z ∈ ball c ρ
    · filter_upwards [Lp.coeFn_smul (f z) (poissonFamilyL2 P c ρ V hV z),
        poissonFamilyL2_ae_eq P c ρ V hV z hz] with ω hs he
      rw [hs,Pi.smul_apply,smul_eq_mul,he]
    · have hf0 : f z = 0 := by
        by_contra h
        exact hz (hf (subset_closure h))
      simp only [hf0, zero_smul, zero_mul]
      exact Lp.coeFn_zero ℝ 2 P

/-- All zero-extended harmonic L² coordinates are centered. -/
theorem poissonFamilyL2_integral_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (c : ℂ) (ρ : ℝ) (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0) (z : ℂ) :
    (∫ ω, poissonFamilyL2 P c ρ V hV z ω ∂P) = 0 := by
  by_cases hz : z ∈ ball c ρ
  · rw [integral_congr_ae (poissonFamilyL2_ae_eq P c ρ V hV z hz)]
    exact hmean z hz
  · simp only [poissonFamilyL2,dite_eq_right hz]
    rw [integral_congr_ae (Lp.coeFn_zero ℝ 2 P)]
    simp only [Pi.zero_apply, integral_zero]

/-- The harmonic test averages are centered. -/
theorem poissonTestIntegralL2_integral_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    (∫ ω, poissonTestIntegralL2 P c ρ V hV f ω ∂P) = 0 := by
  apply integral_mean_L2_integral_eq_zero volume _ (integrable_testFn_smul_on_disk c ρ _ hU f hf)
  apply ae_of_all
  intro z
  rw [integral_mean_L2_smul,poissonFamilyL2_integral_zero P c ρ V hV hmean z,mul_zero]

/-- Covariance of harmonic test averages is a genuine Bochner integral of coordinate covariances. -/
theorem poissonTestIntegralL2_covariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (c : ℂ) (ρ : ℝ)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) (W : Lp ℝ 2 P) :
    covariance (poissonTestIntegralL2 P c ρ V hV f) W P =
      ∫ z, f z*covariance (poissonFamilyL2 P c ρ V hV z) W P := by
  rw [poissonTestIntegralL2,covariance_L2_integral_left volume _
    (integrable_testFn_smul_on_disk c ρ _ hU f hf) W]
  · apply integral_congr_ae
    apply ae_of_all
    intro z
    exact covariance_L2_smul_left (f z) _ W
  · intro z
    rw [integral_mean_L2_smul,poissonFamilyL2_integral_zero P c ρ V hV hmean z,mul_zero]

/-- The zero-extended Green section needs no area restriction in its inner integral. -/
theorem integral_diskGreen_test_restrict_eq (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f : TestFn) :
    (∫ w in ball c ρ, diskGreenKernel c ρ hρ z w*f w) =
      ∫ w, diskGreenKernel c ρ hρ z w*f w := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro w hw
  simp only [diskGreenKernel,hw,and_false,false_and,ite_false,zero_mul]

/-- The outer Green test potential is zero away from its disk. -/
theorem diskGreen_testPotential_eq_zero_of_notMem (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∉ ball c ρ) (f g : TestFn) :
    f z*(∫ w, diskGreenKernel c ρ hρ z w*g w) = 0 := by
  simp only [diskGreenKernel,hz,false_and,ite_false,zero_mul,integral_zero,mul_zero]

/-- Global tests paired against the zero-extended Green potential are integrable. -/
theorem integrable_diskGreen_testPotential_global (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    Integrable (fun z => f z*(∫ w, diskGreenKernel c ρ hρ z w*g w)) := by
  have hs : Function.support (fun z => f z*(∫ w, diskGreenKernel c ρ hρ z w*g w)) ⊆ ball c ρ := by
    intro z hz
    by_contra he
    exact hz (diskGreen_testPotential_eq_zero_of_notMem c z ρ hρ he f g)
  apply (integrableOn_iff_integrable_of_support_subset hs).mp
  change Integrable (fun z => f z*(∫ w, diskGreenKernel c ρ hρ z w*g w)) (volume.restrict (ball c ρ))
  simpa only [integral_diskGreen_test_restrict_eq] using integrable_diskGreenPotential_test c ρ hρ f g

/-- The restricted Green covariance `DOZZ.diskGreenCovariance` equals the literal globally
zero-extended pairing. -/
theorem diskGreenCovariance_eq_global_pair (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (f g : TestFn) :
    diskGreenCovariance c ρ hρ f g = ∫ z, f z*(∫ w, diskGreenKernel c ρ hρ z w*g w) := by
  simp only [diskGreenCovariance,integral_diskGreen_test_restrict_eq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  exact diskGreen_testPotential_eq_zero_of_notMem c z ρ hρ hz f g

/-- Covariance is additive under subtraction in the L² carrier. -/
theorem covariance_L2_sub_left {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U V W : Lp ℝ 2 P) :
    covariance (⇑(U-V)) W P = covariance U W P-covariance V W P := by
  rw [covariance_congr_ae (Lp.coeFn_sub U V) (ae_eq_refl _)]
  exact covariance_sub_left (Lp.memLp U) (Lp.memLp V) (Lp.memLp W)

/-- Every compact interior harmonic test average has the exact global mixed Green correction. -/
theorem poissonTestIntegralL2_test_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (f g : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    covariance (poissonTestIntegralL2 P c ρ V hV f)
      (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P =
    covariance (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) f)
      (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P-diskGreenCovariance c ρ hρ f g := by
  let _ := hX.1
  rw [poissonTestIntegralL2_covariance P c ρ V hV hmean hU f hf]
  have he : (fun z => f z*covariance (poissonFamilyL2 P c ρ V hV z)
      (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P) =
      fun z => f z*(∫ w, exteriorPinnedKernel R (by linarith) z w*g w)-
        f z*(∫ w, diskGreenKernel c ρ hρ z w*g w) := by
    funext z
    by_cases h0 : f z = 0
    · simp only [h0,zero_mul,sub_zero]
    · have hz := hf (subset_closure h0)
      rw [covariance_congr_ae (poissonFamilyL2_ae_eq P c ρ V hV z hz)
        (exteriorPinnedTestL2_ae_eq P X Xc hX hc R (by linarith) g),
        exteriorPinned_poisson_rawLimit_test_covariance_sub_Green P X Xc hX hc c z R ρ ε
          hR hρ hε hpin hz (fun ω => V ω z) (hV z hz) (hlim z hz) g]
      ring
  rw [he]
  have hi : Integrable (fun z => f z*(∫ w, exteriorPinnedKernel R (by linarith) z w*g w)) :=
    (f.continuous.mul (continuous_exteriorPinned_testKernelPotential R (by linarith) g)).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  rw [integral_sub hi (integrable_diskGreen_testPotential_global c ρ hρ f g),
    ← diskGreenCovariance_eq_global_pair c ρ hρ f g,
    covariance_congr_ae (exteriorPinnedTestL2_ae_eq P X Xc hX hc R (by linarith) f)
      (exteriorPinnedTestL2_ae_eq P X Xc hX hc R (by linarith) g),
    (exteriorPinnedEvaluation_covariance P X Xc hX hc R hR f g).2]

/-- The interior Dirichlet test residual, still on the given probability space. -/
noncomputable def dirichletResidualL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) (f : TestFn) : Lp ℝ 2 P :=
    exteriorPinnedTestL2 P X Xc hX hc R hR f-poissonTestIntegralL2 P c ρ V hV f

/-- Interior residuals have the exact Green covariance with every global original test. -/
theorem dirichletResidualL2_test_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (f g : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    covariance (dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f)
      (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P = diskGreenCovariance c ρ hρ f g := by
  let _ := hX.1
  rw [dirichletResidualL2,covariance_L2_sub_left,
    poissonTestIntegralL2_test_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hlim f g hf]
  ring

/-- The closed harmonic covariance is the pinned kernel with its Green part removed. -/
theorem poisson_covariance_eq_exteriorPinnedKernel_sub_Green (c z w : ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hpin : ‖c‖+ρ ≤ R)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (hzw : z ≠ w) :
    Real.log R+Real.log ρ-Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ =
      exteriorPinnedKernel R hR z w-diskGreenKernel c ρ hρ z w := by
  have hn (v : ℂ) (hv : v ∈ ball c ρ) : ‖v‖ ≤ R := by
    have h := norm_add_le (v-c) c
    rw [sub_add_cancel] at h
    linarith [mem_ball_iff_norm.mp hv]
  rw [exteriorPinnedKernel_eq_log_sub hR (hn z hz) (hn w hw),
    diskGreenKernel_eq_log_parts c z w ρ hρ hz hw hzw]
  ring

/-- Against an interior test, each harmonic coordinate pairs equally with the original
field and with its harmonic test integral. -/
theorem poissonFamilyL2_covariance_test_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε) (hpin : ‖c‖+ρ ≤ R)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (hcov : ∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
      covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0))
    (hz : z ∈ ball c ρ) (g : TestFn) (hg : tsupport g ⊆ ball c ρ) :
    covariance (poissonFamilyL2 P c ρ V hV z) (poissonTestIntegralL2 P c ρ V hV g) P =
      covariance (poissonFamilyL2 P c ρ V hV z)
        (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P := by
  let _ := hX.1
  rw [covariance_congr_ae (poissonFamilyL2_ae_eq P c ρ V hV z hz)
      (exteriorPinnedTestL2_ae_eq P X Xc hX hc R (by linarith) g),
    exteriorPinned_poisson_rawLimit_test_covariance_sub_Green P X Xc hX hc c z R ρ ε
      hR hρ hε hpin hz (fun ω => V ω z) (hV z hz) (hlim z hz) g]
  rw [covariance_comm,poissonTestIntegralL2_covariance P c ρ V hV hmean hU g hg]
  calc
    _ = ∫ w, exteriorPinnedKernel R (by linarith) z w*g w-diskGreenKernel c ρ hρ z w*g w := by
      apply integral_congr_ae
      filter_upwards [(volume : Measure ℂ).ae_ne z] with w hwz
      by_cases h0 : g w = 0
      · simp only [h0,mul_zero,zero_mul,sub_zero]
      · have hw := hg (subset_closure h0)
        rw [covariance_comm, covariance_congr_ae (poissonFamilyL2_ae_eq P c ρ V hV z hz)
          (poissonFamilyL2_ae_eq P c ρ V hV w hw),hcov z w hz hw,
          poisson_covariance_eq_exteriorPinnedKernel_sub_Green c z w R ρ (by linarith) hρ hpin hz hw hwz.symm]
        ring
    _ = _ := integral_sub (integrable_exteriorPinned_testKernel_section R (by linarith) g z)
      (integrable_diskGreen_test_section c z R ρ (by linarith) hρ hpin hz g)

/-- Harmonic test integrals pair equally with original interior tests and their harmonic parts. -/
theorem poissonTestIntegralL2_covariance_integral_eq_test {Ω : Type*} [MeasurableSpace Ω]
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
    (f g : TestFn) (hf : tsupport f ⊆ ball c ρ) (hg : tsupport g ⊆ ball c ρ) :
    covariance (poissonTestIntegralL2 P c ρ V hV f) (poissonTestIntegralL2 P c ρ V hV g) P =
      covariance (poissonTestIntegralL2 P c ρ V hV f)
        (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g) P := by
  let _ := hX.1
  rw [poissonTestIntegralL2_covariance P c ρ V hV hmean hU f hf,
    poissonTestIntegralL2_covariance P c ρ V hV hmean hU f hf]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  by_cases h0 : f z = 0
  · simp only [h0,zero_mul]
  · have hz := hf (subset_closure h0)
    dsimp only
    rw [poissonFamilyL2_covariance_test_eq_integral P X Xc hX hc c z R ρ ε hR hρ hε hpin
      V hV hmean hU hcov hlim hz g hg]

/-- Subtracting a second L² argument commutes with covariance. -/
theorem covariance_L2_sub_right {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (U V W : Lp ℝ 2 P) :
    covariance U (⇑(V-W)) P = covariance U V P-covariance U W P := by
  rw [covariance_comm,covariance_L2_sub_left,covariance_comm V U,covariance_comm W U]

/-- The interior Dirichlet residual retains the literal samplewise test-minus-harmonic formula. -/
theorem dirichletResidualL2_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hm : Measurable (fun p : Ω × ℂ => V p.1 p.2))
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    dirichletResidualL2 P X Xc hX hc c R ρ hR V hV f =ᵐ[P]
      fun ω => exteriorPinnedEvaluation X Xc R hR ω f-(∫ z, f z*V ω z) := by
  let _ := hX.1
  filter_upwards [Lp.coeFn_sub (exteriorPinnedTestL2 P X Xc hX hc R hR f)
    (poissonTestIntegralL2 P c ρ V hV f),exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f,
    poissonTestIntegralL2_ae_eq P c ρ V hm hV hU f hf] with ω hs hy hh
  rw [dirichletResidualL2,hs,Pi.sub_apply,hy,hh]

/-- Interior residuals are orthogonal to all interior harmonic test averages. -/
theorem dirichletResidualL2_harmonic_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
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
    (f g : TestFn) (hf : tsupport f ⊆ ball c ρ) (hg : tsupport g ⊆ ball c ρ) :
    covariance (dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f)
      (poissonTestIntegralL2 P c ρ V hV g) P = 0 := by
  let _ := hX.1
  rw [dirichletResidualL2,covariance_L2_sub_left,
    covariance_comm (exteriorPinnedTestL2 P X Xc hX hc R (by linarith) f),
    covariance_comm (poissonTestIntegralL2 P c ρ V hV f),
    poissonTestIntegralL2_covariance_integral_eq_test P X Xc hX hc c R ρ ε hR hρ hε hpin
      V hV hmean hU hcov hlim g f hg hf,sub_self]

/-- The literal interior residual has exactly the disk Green test covariance
`DOZZ.diskGreenCovariance`. -/
theorem dirichletResidualL2_covariance {Ω : Type*} [MeasurableSpace Ω]
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
    (f g : TestFn) (hf : tsupport f ⊆ ball c ρ) (hg : tsupport g ⊆ ball c ρ) :
    covariance (dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f)
      (dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV g) P = diskGreenCovariance c ρ hρ f g := by
  let _ := hX.1
  change covariance (dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f)
    (⇑(exteriorPinnedTestL2 P X Xc hX hc R (by linarith) g-poissonTestIntegralL2 P c ρ V hV g)) P = _
  rw [covariance_L2_sub_right,
    dirichletResidualL2_test_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hlim f g hf,
    dirichletResidualL2_harmonic_covariance_zero P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f g hf hg,
    sub_zero]

/-- The residual test evaluations are centered. -/
theorem dirichletResidualL2_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, V ω z ∂P) = 0)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    (∫ ω, dirichletResidualL2 P X Xc hX hc c R ρ hR V hV f ω ∂P) = 0 := by
  let _ := hX.1
  rw [dirichletResidualL2,integral_eq_inner_one,inner_sub_left,← integral_eq_inner_one,
    ← integral_eq_inner_one, integral_congr_ae (exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f),
    exteriorPinnedEvaluation_integral_zero P X Xc hX hc R hR f,
    poissonTestIntegralL2_integral_zero P c ρ V hV hmean hU f hf,sub_self]

/-- A single Gaussian L² carrier containing both the harmonic and original test coordinates. -/
noncomputable def poissonTestFamilyL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P) :
    ({z : ℂ // z ∈ ball c ρ} ⊕ TestFn) → Lp ℝ 2 P :=
  Sum.elim (fun z => poissonFamilyL2 P c ρ V hV z.1)
    (exteriorPinnedTestL2 P X Xc hX hc R hR)

/-- The actual raw collar limits and all test representatives retain joint Gaussianity in L². -/
theorem poissonTestFamilyL2_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R hR ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) :
    IsGaussianProcess (fun t => ⇑(poissonTestFamilyL2 P X Xc hX hc c R ρ hR V hV t)) P := by
  apply (exteriorPinned_poisson_tests_isGaussianProcess P X Xc hX hc c R ρ ε hR hρ hε V hV hlim).congr
  intro t
  cases t with
  | inl z => exact (poissonFamilyL2_ae_eq P c ρ V hV z.1 z.2).symm
  | inr f => exact (exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f).symm

/-- The harmonic integral of an interior test stays inside the original Gaussian Hilbert span. -/
theorem poissonTestIntegralL2_mem_gaussianHilbertSpan {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    poissonTestIntegralL2 P c ρ V hV f ∈ gaussianHilbertSpan
      (poissonTestFamilyL2 P X Xc hX hc c R ρ hR V hV) := by
  let _ := hX.1
  apply integral_mem_closedHilbertSubmodule volume _ (Submodule.isClosed_topologicalClosure _) _
    (integrable_testFn_smul_on_disk c ρ _ hU f hf)
  apply ae_of_all
  intro z
  apply Submodule.smul_mem
  by_cases hz : z ∈ ball c ρ
  · exact mem_gaussianHilbertSpan (poissonTestFamilyL2 P X Xc hX hc c R ρ hR V hV) (Sum.inl ⟨z,hz⟩)
  · simp only [poissonFamilyL2,dite_eq_right hz]
    exact Submodule.zero_mem _

/-- Interior Dirichlet residuals stay in the same Gaussian Hilbert space as the original field. -/
theorem dirichletResidualL2_mem_gaussianHilbertSpan {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ : ℝ) (hR : 0 < R) (V : Ω → ℂ → ℝ)
    (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hU : ContinuousOn (poissonFamilyL2 P c ρ V hV) (ball c ρ))
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    dirichletResidualL2 P X Xc hX hc c R ρ hR V hV f ∈ gaussianHilbertSpan
      (poissonTestFamilyL2 P X Xc hX hc c R ρ hR V hV) := by
  exact Submodule.sub_mem _ (mem_gaussianHilbertSpan _ (Sum.inr f))
    (poissonTestIntegralL2_mem_gaussianHilbertSpan P X Xc hX hc c R ρ hR V hV hU f hf)


/-- The actual centered residual has the Green norm squared. -/
theorem dirichletResidualL2_norm_sq {Ω : Type*} [MeasurableSpace Ω]
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
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    ‖dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f‖^2 = diskGreenCovariance c ρ hρ f f := by
  let _ := hX.1
  have h := dirichletResidualL2_covariance P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f f hf hf
  rw [covariance_L2_eq,dirichletResidualL2_integral_zero P X Xc hX hc c R ρ (by linarith) V hV hmean hU f hf,
    zero_mul,sub_zero,real_inner_self_eq_norm_sq] at h
  exact h

/-- The interior residual has the actual bounded Green L² estimate required for completion. -/
theorem dirichletResidualL2_norm_sq_le {Ω : Type*} [MeasurableSpace Ω]
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
    (f : TestFn) (hf : tsupport f ⊆ ball c ρ) :
    ‖dirichletResidualL2 P X Xc hX hc c R ρ (by linarith) V hV f‖^2 ≤
      (∫ p : ℂ × ℂ, ‖diskGreenKernel c ρ hρ p.1 p.2‖^2
        ∂((volume.restrict (ball c ρ)).prod (volume.restrict (ball c ρ))))^(1/2 : ℝ)*
      (∫ z in ball c ρ, ‖f z‖^2) := by
  rw [dirichletResidualL2_norm_sq P X Xc hX hc c R ρ ε hR hρ hε hpin V hV hmean hU hcov hlim f hf]
  exact (le_abs_self _).trans (abs_diskGreenCovariance_self_le_diskL2 c ρ hρ f)

end DOZZ.Proofs
