/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonHarmonic
/-!
# Poisson/test covariance and Green cancellation

Weak convergence of literal collars holds for every continuous test potential. The original raw L²
limits therefore have their mixed covariance with all exterior-pinned test evaluations. Absolute
planar/circle Fubini and the interior, exterior and boundary Poisson logarithm formulas identify
that covariance as the pinned test potential minus the actual zero-extended Green potential. The
diagonal convention of `DOZZ.diskGreenKernel` is handled by the area-null singleton. Joint
Gaussianity of the harmonic family and all pinned tests is retained on the given realization.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs

/-- Collar weak convergence against any continuous potential. -/
theorem tendsto_integral_canonicalPoissonCollarTest_mul (c z : ℂ) (ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (hz : z ∈ ball c ρ) (h : ℂ → ℝ) (hh : Continuous h) :
    Tendsto (fun k => ∫ w, canonicalPoissonCollarTest c z ρ ε hρ hε hz k w*h w)
      atTop (𝓝 (∫ v, unitPoissonWeight c ρ z v*h (c+ρ • v) ∂circleMeasure 0 0)) := by
  let d := ρ+ε
  have hd : 0 < d := add_pos hρ hε
  let g : ℂ → ℝ := fun w => h (poissonDiskClamp c d w)
  have hg : Continuous g := hh.comp (continuous_poissonDiskClamp c d hd)
  obtain ⟨M,hM⟩ := (isCompact_closedBall c d).exists_bound_of_continuousOn hh.continuousOn
  have hb (w : ℂ) : ‖g w‖ ≤ M := hM _ (poissonDiskClamp_mem_closedBall c w d hd)
  have hl := tendsto_integral_poissonCollarTest_mul_bounded c z ρ ε hρ hε hz g hg M hb
  have he k : (fun w => canonicalPoissonCollarTest c z ρ ε hρ hε hz k w*g w) =
      fun w => canonicalPoissonCollarTest c z ρ ε hρ hε hz k w*h w := by
    funext w
    by_cases hw : canonicalPoissonCollarTest c z ρ ε hρ hε hz k w = 0
    · simp only [hw, zero_mul]
    · have hs : w ∈ tsupport (canonicalPoissonCollarTest c z ρ ε hρ hε hz k) := subset_closure hw
      have ha := tsupport_poissonCollarValue_annulus c z ρ (ε/((k : ℝ)+1)) hρ hz
        (poissonCollarDensity ε hε k) (tsupport_poissonCollarDensity_subset ε hε k) hs
      have hn : ‖w-c‖ ≤ d := le_trans ha.2.le (add_le_add_right (poissonCollarWidth_le ε hε k) ρ)
      rw [show g w = h w from congrArg h (poissonDiskClamp_eq_self c w d hd hn)]
  have hea : (fun v => unitPoissonWeight c ρ z v*g (c+ρ • v)) =ᵐ[circleMeasure 0 0]
      fun v => unitPoissonWeight c ρ z v*h (c+ρ • v) := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with v hv
    have hv' : ‖v‖ = 1 := by simpa only [sub_zero, neg_zero, Real.exp_zero] using hv
    have hn : ‖(c+ρ • v)-c‖ ≤ d := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hρ, hv', mul_one]
      exact le_add_of_nonneg_right hε.le
    rw [show g (c+ρ • v) = h (c+ρ • v) from congrArg h (poissonDiskClamp_eq_self c _ d hd hn)]
  change Tendsto (fun k => ∫ w, canonicalPoissonCollarTest c z ρ ε hρ hε hz k w*g w)
    atTop (𝓝 (∫ v, unitPoissonWeight c ρ z v*g (c+ρ • v) ∂circleMeasure 0 0)) at hl
  simpa only [he, integral_congr_ae hea] using hl

/-- The difference of exterior and equator pinning potentials is continuous. -/
theorem continuous_exteriorPinDifference (R : ℝ) (hR : 0 < R) :
    Continuous (fun z : ℂ => Real.log (max ‖z‖ R)-Real.log (normPlus z)) := by
  apply Continuous.sub _ continuous_log_normPlus
  exact (continuous_norm.max continuous_const).log (fun z => ne_of_gt (hR.trans_le (le_max_right _ _)))

/-- The literal exterior-pinned kernel is the equator kernel plus continuous separable terms. -/
theorem exteriorPinnedKernel_eq_gffKernel_add (R : ℝ) (hR : 0 < R) (z w : ℂ) :
    exteriorPinnedKernel R hR z w = gffKernel z w+
      (Real.log (max ‖z‖ R)-Real.log (normPlus z))+
      (Real.log (max ‖w‖ R)-Real.log (normPlus w))-Real.log R := by
  unfold exteriorPinnedKernel gffKernel
  ring

/-- Exterior-pinned kernel sections against compact tests are integrable. -/
theorem integrable_exteriorPinned_testKernel_section (R : ℝ) (hR : 0 < R) (f : TestFn) (z : ℂ) :
    Integrable (fun w : ℂ => exteriorPinnedKernel R hR z w*f w) := by
  let p : ℂ → ℝ := fun w => Real.log (max ‖w‖ R)-Real.log (normPlus w)
  have hfi : Integrable (f : ℂ → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hp : Integrable (fun w => p w*f w) :=
    ((continuous_exteriorPinDifference R hR).mul f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
  have hi := (((integrable_testKernel_section f z).add (hfi.const_mul (p z))).add hp).sub
    (hfi.const_mul (Real.log R))
  convert hi using 1
  funext w
  simp only [Pi.sub_apply, Pi.add_apply, exteriorPinnedKernel_eq_gffKernel_add, p]
  ring

/-- Continuous test potentials for the literal exterior-pinned kernel. -/
theorem continuous_exteriorPinned_testKernelPotential (R : ℝ) (hR : 0 < R) (f : TestFn) :
    Continuous (fun z : ℂ => ∫ w, exteriorPinnedKernel R hR z w*f w) := by
  let p : ℂ → ℝ := fun w => Real.log (max ‖w‖ R)-Real.log (normPlus w)
  have hfi : Integrable (f : ℂ → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hp : Integrable (fun w => p w*f w) :=
    ((continuous_exteriorPinDifference R hR).mul f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
  have he z : (∫ w, exteriorPinnedKernel R hR z w*f w) =
      (∫ w, gffKernel z w*f w)+p z*(∫ w, f w)+(∫ w, p w*f w)-Real.log R*(∫ w, f w) := by
    have he' w : exteriorPinnedKernel R hR z w*f w =
      (gffKernel z w*f w+p z*f w)+p w*f w-Real.log R*f w := by
      rw [exteriorPinnedKernel_eq_gffKernel_add]
      dsimp only [p]
      ring
    simp_rw [he']
    have h₁ := integral_sub (((integrable_testKernel_section f z).add (hfi.const_mul (p z))).add hp)
      (hfi.const_mul (Real.log R))
    have h₂ := integral_add ((integrable_testKernel_section f z).add (hfi.const_mul (p z))) hp
    have h₃ := integral_add (integrable_testKernel_section f z) (hfi.const_mul (p z))
    simp only [Pi.add_apply] at h₁ h₂ h₃
    rw [h₁,h₂,h₃,integral_const_mul,integral_const_mul]
  simp_rw [he]
  exact (((continuous_testKernelPotential f).add ((continuous_exteriorPinDifference R hR).mul
    continuous_const)).add continuous_const).sub continuous_const

/-- A literal Poisson collar limit has the mixed covariance with every original test. -/
theorem exteriorPinned_poisson_rawLimit_test_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hz : z ∈ ball c ρ) (H : Ω → ℝ) (hH : MemLp H 2 P)
    (hlim : Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-H ω) 2 P) atTop (𝓝 0))
    (f : TestFn) :
    covariance H (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f) P =
      ∫ v, unitPoissonWeight c ρ z v*
        (∫ w, exteriorPinnedKernel R (by linarith) (c+ρ • v) w*f w) ∂circleMeasure 0 0 := by
  let _ := hX.1
  let p k := canonicalPoissonCollarTest c z ρ ε hρ hε hz k
  have hY f := exteriorPinnedEvaluation_memLp X Xc hX hc R (zero_lt_one.trans hR) f
  have hconst : Tendsto (fun k : ℕ => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f-
        exteriorPinnedEvaluation X Xc R (by linarith) ω f) 2 P) atTop (𝓝 0) := by
    simpa only [sub_self, ← Pi.zero_def, eLpNorm_zero] using (tendsto_const_nhds (x := (0 : ℝ≥0∞)))
  have hl := tendsto_covariance_of_eLpNorm_sub (fun k => hY (p k)) (fun _ => hY f) hH (hY f) hlim hconst
  have hw := tendsto_integral_canonicalPoissonCollarTest_mul c z ρ ε hρ hε hz
    (fun v => ∫ w, exteriorPinnedKernel R (zero_lt_one.trans hR) v w*f w)
    (continuous_exteriorPinned_testKernelPotential R (zero_lt_one.trans hR) f)
  apply tendsto_nhds_unique hl
  simpa only [(exteriorPinnedEvaluation_covariance P X Xc hX hc R hR (p _) f).2, p] using hw

/-- The full physical Poisson kernel is Borel measurable. -/
theorem measurable_poissonKernel (c z : ℂ) : Measurable (poissonKernel c z) := by
  have he : poissonKernel c z = fun v : ℂ => (‖v-c‖^2-‖z-c‖^2)/‖(v-c)-(z-c)‖^2 :=
    funext (poissonKernel_def c z)
  rw [he]
  fun_prop

/-- Poisson weights preserve integrability on their physical boundary circle. -/
theorem integrable_poissonKernel_mul_circle (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (f : ℂ → ℝ) (hf : Integrable f (circleMeasure c (-Real.log ρ))) :
    Integrable (fun v => poissonKernel c z v*f v) (circleMeasure c (-Real.log ρ)) := by
  obtain ⟨M,hM⟩ := (isCompact_sphere c ρ).exists_bound_of_continuousOn
    (continuousOn_poissonKernel_sphere c z ρ hρ hz)
  apply hf.bdd_mul (measurable_poissonKernel c z).aestronglyMeasurable
  filter_upwards [ae_mem_sphere_circleMeasure c (-Real.log ρ)] with v hv
  apply hM
  simpa only [neg_neg, Real.exp_log hρ] using hv

/-- Boundary logarithms at exterior poles are reproduced by the Poisson kernel. -/
theorem circleAverage_poisson_exterior_log (c z w : ℂ) (ρ : ℝ) (_hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∉ closedBall c ρ) :
    Real.circleAverage (poissonKernel c z*(fun v : ℂ => Real.log ‖v-w‖)) c ρ =
      Real.log ‖z-w‖ := by
  have hh : InnerProductSpace.HarmonicOnNhd (fun v : ℂ => Real.log ‖v-w‖) (closedBall c ρ) := by
    intro v hv
    apply AnalyticAt.harmonicAt_log_norm (by fun_prop)
    exact sub_ne_zero.mpr (fun h => hw (h ▸ hv))
  exact hh.circleAverage_poissonKernel_smul hz

/-- The first argument of the exterior kernel simplifies throughout its pinning disk. -/
theorem exteriorPinnedKernel_of_first_inside (R : ℝ) (hR : 0 < R) (v w : ℂ) (hv : ‖v‖ ≤ R) :
    exteriorPinnedKernel R hR v w = Real.log (max ‖w‖ R)-Real.log ‖v-w‖ := by
  rw [exteriorPinnedKernel, max_eq_right hv]
  ring

/-- The Poisson average of the pinned kernel removes exactly the disk Green kernel. The diagonal is
omitted here because `DOZZ.diskGreenKernel` is zero on it. -/
theorem integral_poisson_exteriorPinnedKernel_eq_sub_Green (c z w : ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hpin : ‖c‖+ρ ≤ R) (hz : z ∈ ball c ρ) (hzw : z ≠ w) :
    (∫ v, poissonKernel c z v*exteriorPinnedKernel R hR v w ∂circleMeasure c (-Real.log ρ)) =
      exteriorPinnedKernel R hR z w-diskGreenKernel c ρ hρ z w := by
  let μ := circleMeasure c (-Real.log ρ)
  let _ := circleMeasure_isProbability c (-Real.log ρ)
  have hzi : ‖z‖ ≤ R := by
    calc
      _ ≤ ‖z-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (z-c) c
      _ ≤ ρ+‖c‖ := add_le_add_left (mem_ball_iff_norm.mp hz).le _
      _ ≤ R := by linarith
  have hl : Integrable (fun v => Real.log ‖v-w‖) μ :=
    integrable_log_norm_sub_circleMeasure c w (-Real.log ρ)
  have hk := integrable_poissonKernel_mul_circle c z ρ hρ hz _ hl
  have hkc := integrable_poissonKernel_mul_circle c z ρ hρ hz (fun _ => Real.log (max ‖w‖ R))
    (integrable_const _)
  have he : (fun v => poissonKernel c z v*exteriorPinnedKernel R hR v w) =ᵐ[μ]
      (fun v => poissonKernel c z v*Real.log (max ‖w‖ R)-poissonKernel c z v*Real.log ‖v-w‖) := by
    filter_upwards [ae_norm_sub_center_circleMeasure c (-Real.log ρ)] with v hv
    have hv' : ‖v-c‖ = ρ := by simpa only [neg_neg, Real.exp_log hρ] using hv
    have hvR : ‖v‖ ≤ R := by
      calc
        _ ≤ ‖v-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (v-c) c
        _ ≤ R := by rw [hv']; linarith
    rw [exteriorPinnedKernel_of_first_inside R hR v w hvR]
    ring
  rw [integral_congr_ae he]
  have hsub := integral_sub hkc hk
  rw [hsub, integral_mul_const]
  have hmass : (∫ v, poissonKernel c z v ∂μ) = 1 := by
    rw [integral_circleMeasure_eq_circleAverage c (-Real.log ρ) _ (measurable_poissonKernel c z)]
    simp only [neg_neg, Real.exp_log hρ]
    exact circleAverage_poissonKernel_eq_one c z ρ hz
  rw [hmass, one_mul, exteriorPinnedKernel_of_first_inside R hR z w hzi]
  have hlog : (∫ v, poissonKernel c z v*Real.log ‖v-w‖ ∂μ) =
      Real.circleAverage (poissonKernel c z*(fun v : ℂ => Real.log ‖v-w‖)) c ρ := by
    rw [integral_circleMeasure_eq_circleAverage c (-Real.log ρ) (fun v : ℂ => poissonKernel c z v*Real.log ‖v-w‖)
      ((measurable_poissonKernel c z).mul (show Measurable (fun v : ℂ => Real.log ‖v-w‖) by fun_prop))]
    simp only [neg_neg, Real.exp_log hρ]
    rfl
  rw [hlog]
  by_cases hw : w ∈ ball c ρ
  · have hwR : ‖w‖ ≤ R := by
      calc
        _ ≤ ‖w-c‖+‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (w-c) c
        _ ≤ R := by linarith [mem_ball_iff_norm.mp hw]
    rw [max_eq_right hwR, diskGreenKernel_eq_log_parts c z w ρ hρ hz hw hzw]
    have hi := integral_unitPoissonWeight_interior_log c z w ρ hρ hz hw
    rw [integral_unitPoissonWeight_mul_eq_circleAverage c z ρ hρ (fun v : ℂ => Real.log ‖v-w‖) (by fun_prop)] at hi
    rw [hi]
    ring
  · have hg : diskGreenKernel c ρ hρ z w = 0 := by simp only [diskGreenKernel, hw, and_false, false_and, ite_false]
    rw [hg, sub_zero]
    by_cases hws : w ∈ closedBall c ρ
    · have hboundary : w ∈ sphere c ρ := by
        rw [mem_sphere_iff_norm]
        exact le_antisymm (mem_closedBall_iff_norm.mp hws) (not_lt.mp (fun h => hw (mem_ball_iff_norm.mpr h)))
      have hi := circleAverage_re_herglotzRieszKernel_mul_log hboundary hz
      simp only [← poissonKernel_eq_re_herglotzRieszKernel] at hi
      rw [hi]
    · rw [circleAverage_poisson_exterior_log c z w ρ hρ hz hws]

/-- An exterior-pinned compact test can be paired absolutely with a circle. -/
theorem integrable_exteriorPinned_test_circleKernel (R : ℝ) (hR : 0 < R)
    (c : ℂ) (r : ℝ) (f : TestFn) :
    Integrable (fun p : ℂ × ℂ => exteriorPinnedKernel R hR p.2 p.1*f p.1)
      (volume.prod (circleMeasure c r)) := by
  let μ := circleMeasure c r
  let _ := circleMeasure_isProbability c r
  let p : ℂ → ℝ := fun w => Real.log (max ‖w‖ R)-Real.log (normPlus w)
  have hp := continuous_exteriorPinDifference R hR
  have hfi : Integrable (f : ℂ → ℝ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hpf : Integrable (fun w => p w*f w) :=
    (hp.mul f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
  have hpc : Integrable p μ := integrable_circleMeasure_of_circleIntegrable c r hp.measurable
    hp.continuousOn.circleIntegrable'
  have hc : Integrable (fun _ : ℂ => (1 : ℝ)) μ := integrable_const _
  have hi := (((integrable_test_circleKernel c r f).add (hfi.mul_prod hpc)).add
    (hpf.mul_prod hc)).sub ((hfi.const_mul (Real.log R)).mul_prod hc)
  convert hi using 1
  funext a
  simp only [Pi.sub_apply, Pi.add_apply, mul_one, exteriorPinnedKernel_eq_gffKernel_add, gffKernel_comm, p]
  ring

/-- Physical Poisson weights retain the absolute planar/circle test pairing. -/
theorem integrable_poisson_exteriorPinned_test_circleKernel (R : ℝ) (hR : 0 < R)
    (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hz : z ∈ ball c ρ) (f : TestFn) :
    Integrable (fun p : ℂ × ℂ => poissonKernel c z p.2*exteriorPinnedKernel R hR p.2 p.1*f p.1)
      (volume.prod (circleMeasure c (-Real.log ρ))) := by
  let _ := circleMeasure_isProbability c (-Real.log ρ)
  obtain ⟨M,hM⟩ := (isCompact_sphere c ρ).exists_bound_of_continuousOn
    (continuousOn_poissonKernel_sphere c z ρ hρ hz)
  have hb : ∀ᵐ p : ℂ × ℂ ∂volume.prod (circleMeasure c (-Real.log ρ)),
      ‖poissonKernel c z p.2‖ ≤ M := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le ((measurable_poissonKernel c z).comp measurable_snd).norm measurable_const)).mpr
    apply ae_of_all
    intro w
    filter_upwards [ae_mem_sphere_circleMeasure c (-Real.log ρ)] with v hv
    apply hM
    simpa only [neg_neg, Real.exp_log hρ] using hv
  have hi := (integrable_exteriorPinned_test_circleKernel R hR c (-Real.log ρ) f).bdd_mul
    ((measurable_poissonKernel c z).comp measurable_snd).aestronglyMeasurable hb
  convert hi using 1
  funext p
  simp only [Function.comp_def]
  ring

/-- Singular planar/circle Fubini identifies the Poisson-averaged test potential. -/
theorem integral_poisson_exteriorPinned_testPotential (R : ℝ) (hR : 0 < R)
    (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hz : z ∈ ball c ρ) (f : TestFn) :
    (∫ v, unitPoissonWeight c ρ z v*
      (∫ w, exteriorPinnedKernel R hR (c+ρ • v) w*f w) ∂circleMeasure 0 0) =
      ∫ w, (∫ v, poissonKernel c z v*exteriorPinnedKernel R hR v w
        ∂circleMeasure c (-Real.log ρ))*f w := by
  let _ := circleMeasure_isProbability c (-Real.log ρ)
  have hp := continuous_exteriorPinned_testKernelPotential R hR f
  rw [integral_unitPoissonWeight_mul_eq_circleAverage c z ρ hρ _ hp.measurable]
  have he : Real.circleAverage (poissonKernel c z*(fun v => ∫ w, exteriorPinnedKernel R hR v w*f w)) c ρ =
      ∫ v, poissonKernel c z v*(∫ w, exteriorPinnedKernel R hR v w*f w)
        ∂circleMeasure c (-Real.log ρ) := by
    rw [integral_circleMeasure_eq_circleAverage c (-Real.log ρ) (fun v => poissonKernel c z v*(∫ w, exteriorPinnedKernel R hR v w*f w)) ((measurable_poissonKernel c z).mul hp.measurable)]
    simp only [neg_neg, Real.exp_log hρ]
    rfl
  rw [he]
  have hi := integrable_poisson_exteriorPinned_test_circleKernel R hR c z ρ hρ hz f
  calc
    _ = ∫ v, ∫ w, poissonKernel c z v*exteriorPinnedKernel R hR v w*f w
        ∂volume ∂circleMeasure c (-Real.log ρ) := by
      apply integral_congr_ae
      filter_upwards with v
      rw [← integral_const_mul]
      congr 1
      funext w
      ring
    _ = ∫ w, ∫ v, poissonKernel c z v*exteriorPinnedKernel R hR v w*f w
        ∂circleMeasure c (-Real.log ρ) := (integral_integral_swap hi).symm
    _ = _ := by simp_rw [integral_mul_const]

/-- The Green correction to any global test is genuinely integrable. -/
theorem integrable_diskGreen_test_section (c z : ℂ) (R ρ : ℝ) (hR : 0 < R)
    (hρ : 0 < ρ) (hpin : ‖c‖+ρ ≤ R) (hz : z ∈ ball c ρ) (f : TestFn) :
    Integrable (fun w => diskGreenKernel c ρ hρ z w*f w) := by
  let _ := circleMeasure_isProbability c (-Real.log ρ)
  have hi := (integrable_poisson_exteriorPinned_test_circleKernel R hR c z ρ hρ hz f).integral_prod_left
  have he : (fun w => ∫ v, poissonKernel c z v*exteriorPinnedKernel R hR v w*f w
      ∂circleMeasure c (-Real.log ρ)) =ᵐ[volume]
      fun w => (exteriorPinnedKernel R hR z w-diskGreenKernel c ρ hρ z w)*f w := by
    filter_upwards [(volume : Measure ℂ).ae_ne z] with w hw
    rw [integral_mul_const, integral_poisson_exteriorPinnedKernel_eq_sub_Green c z w R ρ hR hρ hpin hz hw.symm]
  have hd := hi.congr he
  convert (integrable_exteriorPinned_testKernel_section R hR f z).sub hd using 1
  funext w
  simp only [Pi.sub_apply]
  ring

/-- The first Poisson/test covariance equals the pinned kernel minus the Green correction. -/
theorem integral_poisson_exteriorPinned_testPotential_eq_sub_Green (c z : ℂ) (R ρ : ℝ)
    (hR : 0 < R) (hρ : 0 < ρ) (hpin : ‖c‖+ρ ≤ R) (hz : z ∈ ball c ρ) (f : TestFn) :
    (∫ v, unitPoissonWeight c ρ z v*
      (∫ w, exteriorPinnedKernel R hR (c+ρ • v) w*f w) ∂circleMeasure 0 0) =
      (∫ w, exteriorPinnedKernel R hR z w*f w)-(∫ w, diskGreenKernel c ρ hρ z w*f w) := by
  rw [integral_poisson_exteriorPinned_testPotential R hR c z ρ hρ hz f]
  calc
    _ = ∫ w, exteriorPinnedKernel R hR z w*f w-diskGreenKernel c ρ hρ z w*f w := by
      apply integral_congr_ae
      filter_upwards [(volume : Measure ℂ).ae_ne z] with w hw
      rw [integral_poisson_exteriorPinnedKernel_eq_sub_Green c z w R ρ hR hρ hpin hz hw.symm]
      ring
    _ = _ := integral_sub (integrable_exteriorPinned_testKernel_section R hR f z)
      (integrable_diskGreen_test_section c z R ρ hR hρ hpin hz f)

/-- Raw harmonic collar limits have the exact Green-subtraction covariance with global tests. -/
theorem exteriorPinned_poisson_rawLimit_test_covariance_sub_Green {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z : ℂ) (R ρ ε : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hpin : ‖c‖+ρ ≤ R) (hz : z ∈ ball c ρ) (H : Ω → ℝ) (hH : MemLp H 2 P)
    (hlim : Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-H ω) 2 P) atTop (𝓝 0))
    (f : TestFn) :
    covariance H (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f) P =
      (∫ w, exteriorPinnedKernel R (by linarith) z w*f w)-
        (∫ w, diskGreenKernel c ρ hρ z w*f w) := by
  rw [exteriorPinned_poisson_rawLimit_test_covariance P X Xc hX hc c z R ρ ε hR hρ hε hz H hH hlim f]
  exact integral_poisson_exteriorPinned_testPotential_eq_sub_Green c z R ρ
    (zero_lt_one.trans hR) hρ hpin hz f

/-- All harmonic collar limits and pinned test evaluations are jointly Gaussian. -/
theorem exteriorPinned_poisson_tests_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε : ℝ) (hR : 0 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (V : Ω → ℂ → ℝ) (hV : ∀ z ∈ ball c ρ, MemLp (fun ω => V ω z) 2 P)
    (hlim : ∀ z (hz : z ∈ ball c ρ), Tendsto (fun k => eLpNorm
      (fun ω => exteriorPinnedEvaluation X Xc R hR ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) :
    IsGaussianProcess (fun t : {z : ℂ // z ∈ ball c ρ} ⊕ TestFn =>
      Sum.elim (fun z => fun ω => V ω z.1)
        (fun f => fun ω => exteriorPinnedEvaluation X Xc R hR ω f) t) P := by
  let _ := hX.1
  let F : ℕ → ({z : ℂ // z ∈ ball c ρ} ⊕ TestFn) → TestFn :=
    fun k => Sum.elim (fun z => canonicalPoissonCollarTest c z.1 ρ ε hρ hε z.2 k) id
  apply isGaussianProcess_of_eLpNorm_sub (fun k t ω => exteriorPinnedEvaluation X Xc R hR ω (F k t))
    (fun t => Sum.elim (fun z => fun ω => V ω z.1)
      (fun f => fun ω => exteriorPinnedEvaluation X Xc R hR ω f) t)
  · intro k
    simpa only [Function.comp_def] using
      (exteriorPinnedEvaluation_isGaussianProcess P X Xc hX hc R hR).comp_right (F k)
  · intro t
    cases t with
    | inl z => exact hV z.1 z.2
    | inr f => exact exteriorPinnedEvaluation_memLp X Xc hX hc R hR f
  · intro t
    cases t with
    | inl z => exact hlim z.1 z.2
    | inr f =>
      simpa only [F, Sum.elim_inr, id_eq, sub_self, ← Pi.zero_def, eLpNorm_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))

/-- Green section pairings vanish on tests exterior to the closed disk. -/
theorem integral_diskGreen_test_eq_zero_of_exterior (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (f : TestFn) (hf : tsupport f ⊆ (closedBall c ρ)ᶜ) :
    (∫ w, diskGreenKernel c ρ hρ z w*f w) = 0 := by
  apply integral_eq_zero_of_ae
  apply ae_of_all
  intro w
  change diskGreenKernel c ρ hρ z w*f w = 0
  by_cases hw : f w = 0
  · rw [hw,mul_zero]
  · have he : w ∉ closedBall c ρ := hf (subset_closure hw)
    have hb : w ∉ ball c ρ := fun h => he (ball_subset_closedBall h)
    simp only [diskGreenKernel, hb, and_false, false_and, ite_false, zero_mul]


end DOZZ.Proofs
