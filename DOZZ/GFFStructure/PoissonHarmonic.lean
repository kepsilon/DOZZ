/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonFormula
public import DOZZ.GFFStructure.GaussianIntegration
/-!
# Harmonic Poisson limits on the original realization

The exact covariance reproduces the collar-limit L² family under every inner-circle Poisson average.
Samplewise Fubini identifies these averages with the jointly measurable continuous boundary
representatives. Analytic Herglotz integrals give local smooth harmonic modifications. Continuous
radial clamps and the countable open-cover modification theorem glue them throughout the disk;
indistinguishability gives one common smooth harmonic event. The resulting Gaussian family retains
the literal exterior collar limits and the harmonic covariance formula of
`DOZZ.exists_exteriorPinned_markov_uniform`.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal InnerProductSpace
namespace DOZZ.Proofs

/-- The closed harmonic covariance is harmonic in its first variable. -/
theorem harmonicOnNhd_poisson_covariance (c w : ℂ) (R ρ : ℝ) (hρ : 0 < ρ)
    (hw : w ∈ ball c ρ) :
    InnerProductSpace.HarmonicOnNhd (fun z : ℂ => Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) (closedBall c ρ) := by
  exact (show InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => Real.log R+Real.log ρ)
    (closedBall c ρ) from InnerProductSpace.harmonicOnNhd_const (Real.log R+Real.log ρ)).sub
      (harmonicOnNhd_diskGreen_regular c w ρ hρ hw)


/-- A centered raw L² family's increment norm equals its variance. -/
theorem toLp_norm_sub_sq_eq_variance {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : T → Ω → ℝ)
    (hmem : ∀ z, MemLp (H z) 2 P) (hmean : ∀ z, (∫ ω, H z ω ∂P) = 0) (z w : T) :
    ‖(hmem z).toLp (H z)-(hmem w).toLp (H w)‖^2 =
      variance (fun ω => H z ω-H w ω) P := by
  let D := (hmem z).toLp (H z)-(hmem w).toLp (H w)
  have hae : D =ᵐ[P] fun ω => H z ω-H w ω := by
    filter_upwards [Lp.coeFn_sub ((hmem z).toLp (H z)) ((hmem w).toLp (H w)),
      (hmem z).coeFn_toLp, (hmem w).coeFn_toLp] with ω hD hz hw
    rw [hD, Pi.sub_apply, hz, hw]
  have hm : AEMeasurable (fun ω => H z ω-H w ω) P :=
    ((hmem z).sub (hmem w)).aestronglyMeasurable.aemeasurable
  have hzero : (∫ ω, D ω ∂P) = 0 := by
    rw [integral_congr_ae hae, integral_sub ((hmem z).integrable (by norm_num))
      ((hmem w).integrable (by norm_num)), hmean, hmean, sub_self]
  have hcov := covariance_L2_eq D D
  rw [hzero, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hcov
  rw [← covariance_self hm, ← covariance_congr_ae hae hae, hcov]

/-- The exact harmonic covariance makes the original Poisson family continuous in L²
throughout the open disk. -/
theorem continuous_poisson_gaussian_toLp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (R ρ : ℝ) (hρ : 0 < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ)
    (hmem : ∀ z, MemLp (H z) 2 P) (hmean : ∀ z, (∫ ω, H z ω ∂P) = 0)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖) :
    Continuous (fun z => (hmem z).toLp (H z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have hz := poissonNumerator_pos c z.1 ρ hρ z.2
  have hlim : Tendsto (fun w : {z : ℂ // z ∈ ball c ρ} =>
      Real.log (1+ρ^2*‖w.1-z.1‖^2/((ρ^2-‖w.1-c‖^2)*(ρ^2-‖z.1-c‖^2))))
      (𝓝 z) (𝓝 0) := by
    have hn : ContinuousAt (fun w : {z : ℂ // z ∈ ball c ρ} =>
        1+ρ^2*‖w.1-z.1‖^2/((ρ^2-‖w.1-c‖^2)*(ρ^2-‖z.1-c‖^2))) z := by
      apply continuousAt_const.add
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      exact mul_ne_zero hz.ne' hz.ne'
    have hl := hn.log (by simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_div, add_zero]; norm_num)
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_div, add_zero, Real.log_one] using hl.tendsto
  have hs : Tendsto (fun w => ‖(hmem w).toLp (H w)-(hmem z).toLp (H z)‖^2) (𝓝 z) (𝓝 0) := by
    simp_rw [toLp_norm_sub_sq_eq_variance P H hmem hmean,
      poisson_gaussian_increment_variance P c R ρ hρ H hmem hcov]
    exact hlim
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

/-- The Poisson kernel is continuous on a boundary circle containing its pole strictly inside. -/
theorem continuousOn_poissonKernel_sphere (c z : ℂ) (b : ℝ) (_hb : 0 < b)
    (hz : z ∈ ball c b) : ContinuousOn (poissonKernel c z) (sphere c b) := by
  rw [show poissonKernel c z = (fun v : ℂ =>
    (‖v-c‖^2-‖z-c‖^2)/‖(v-c)-(z-c)‖^2) from funext (poissonKernel_def c z)]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro v hv
  apply pow_ne_zero 2
  apply norm_ne_zero_iff.mpr
  apply sub_ne_zero.mpr
  intro h
  have hcz : v = z := by exact sub_left_injective h
  subst v
  exact (mem_ball_iff_norm.mp hz).ne (mem_sphere_iff_norm.mp hv)

/-- Boundary values inside a larger disk remain interior. -/
theorem sphere_subset_larger_ball (c : ℂ) (b ρ : ℝ) (hbρ : b < ρ) :
    sphere c b ⊆ ball c ρ := fun _z hz => mem_ball_iff_norm.mpr
      ((mem_sphere_iff_norm.mp hz).trans_lt hbρ)

/-- Centering and covariance identify a centered L² pairing with the regular covariance. -/
theorem inner_poisson_gaussian_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (R ρ : ℝ)
    (U : ℂ → Lp ℝ 2 P) (hmean : ∀ z ∈ ball c ρ, (∫ ω, U z ω ∂P) = 0)
    (hcov : ∀ z ∈ ball c ρ, ∀ w ∈ ball c ρ,
      covariance (U z) (U w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖)
    (z w : ℂ) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) :
    inner ℝ (U z) (U w) = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ := by
  have he := covariance_L2_eq (U z) (U w)
  rw [hmean z hz, zero_mul, sub_zero] at he
  rw [← he]
  exact hcov z hz w hw

/-- The weighted L² boundary integral pairs with every interior coordinate exactly as its pole. -/
theorem inner_poisson_circleAverage_L2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c z w : ℂ) (R ρ b : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b < ρ) (hz : z ∈ ball c b) (hw : w ∈ ball c ρ)
    (U : ℂ → Lp ℝ 2 P) (hU : ContinuousOn U (ball c ρ))
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, U z ω ∂P) = 0)
    (hcov : ∀ z ∈ ball c ρ, ∀ w ∈ ball c ρ,
      covariance (U z) (U w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) :
    inner ℝ (Real.circleAverage (poissonKernel c z • U) c b) (U w) = inner ℝ (U z) (U w) := by
  have hc : CircleIntegrable (poissonKernel c z • U) c b :=
    ((continuousOn_poissonKernel_sphere c z b hb hz).smul
      (hU.mono (sphere_subset_larger_ball c b ρ hbρ))).circleIntegrable hb.le
  have hcomm := (innerSL ℝ (U w)).circleAverage_comp_comm hc
  change Real.circleAverage (fun v => inner ℝ (U w) ((poissonKernel c z • U) v)) c b =
    inner ℝ (U w) (Real.circleAverage (poissonKernel c z • U) c b) at hcomm
  rw [real_inner_comm, ← hcomm]
  have he : Set.EqOn (fun v => inner ℝ (U w) ((poissonKernel c z • U) v))
      (poissonKernel c z • (fun v : ℂ => Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(v-c)*star (w-c)‖)) (sphere c |b|) := by
    intro v hv
    rw [abs_of_pos hb] at hv
    change inner ℝ (U w) (poissonKernel c z v • U v) =
      poissonKernel c z v*(Real.log R+Real.log ρ-Real.log ‖(ρ : ℂ)^2-(v-c)*star (w-c)‖)
    rw [real_inner_smul_right, real_inner_comm, inner_poisson_gaussian_L2 P c R ρ U hmean hcov v w
      (sphere_subset_larger_ball c b ρ hbρ hv) hw]
  rw [Real.circleAverage_congr_sphere he]
  have hreg := (harmonicOnNhd_poisson_covariance c w R ρ hρ hw).mono
    (closedBall_subset_closedBall hbρ.le)
  rw [hreg.circleAverage_poissonKernel_smul hz,
    inner_poisson_gaussian_L2 P c R ρ U hmean hcov z w
      (ball_subset_ball hbρ.le hz) hw]

/-- The Poisson boundary Bochner average reproduces the actual L² harmonic coordinate. -/
theorem poisson_circleAverage_L2_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c z : ℂ) (R ρ b : ℝ)
    (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b < ρ) (hz : z ∈ ball c b)
    (U : ℂ → Lp ℝ 2 P) (hU : ContinuousOn U (ball c ρ))
    (hmean : ∀ z ∈ ball c ρ, (∫ ω, U z ω ∂P) = 0)
    (hcov : ∀ z ∈ ball c ρ, ∀ w ∈ ball c ρ,
      covariance (U z) (U w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) :
    Real.circleAverage (poissonKernel c z • U) c b = U z := by
  let J := Real.circleAverage (poissonKernel c z • U) c b
  have hc : CircleIntegrable (poissonKernel c z • U) c b :=
    ((continuousOn_poissonKernel_sphere c z b hb hz).smul
      (hU.mono (sphere_subset_larger_ball c b ρ hbρ))).circleIntegrable hb.le
  have hJw w hw := inner_poisson_circleAverage_L2 P c z w R ρ b hρ hb hbρ hz hw U hU hmean hcov
  have hJz : inner ℝ J (U z) = inner ℝ (U z) (U z) :=
    hJw z (ball_subset_ball hbρ.le hz)
  have hJJ : inner ℝ J J = inner ℝ (U z) J := by
    have hleft := (innerSL ℝ J).circleAverage_comp_comm hc
    have hright := (innerSL ℝ (U z)).circleAverage_comp_comm hc
    change Real.circleAverage (fun v => inner ℝ J ((poissonKernel c z • U) v)) c b =
      inner ℝ J (Real.circleAverage (poissonKernel c z • U) c b) at hleft
    change Real.circleAverage (fun v => inner ℝ (U z) ((poissonKernel c z • U) v)) c b =
      inner ℝ (U z) (Real.circleAverage (poissonKernel c z • U) c b) at hright
    change inner ℝ J (Real.circleAverage (poissonKernel c z • U) c b) =
      inner ℝ (U z) (Real.circleAverage (poissonKernel c z • U) c b)
    rw [← hleft, ← hright]
    apply Real.circleAverage_congr_sphere
    intro v hv
    rw [abs_of_pos hb] at hv
    change inner ℝ J (poissonKernel c z v • U v) =
      inner ℝ (U z) (poissonKernel c z v • U v)
    rw [real_inner_smul_right, real_inner_smul_right]
    exact congrArg (fun t : ℝ => poissonKernel c z v*t)
      (hJw v (sphere_subset_larger_ball c b ρ hbρ hv))
  have hs : ‖J-U z‖^2 = 0 := by
    rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hJJ, ← real_inner_comm (U z) J, hJz]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp ((sq_eq_zero_iff).mp hs))

/-- Circle averages of L²-valued maps have the literal samplewise representatives. -/
theorem circleAverage_L2_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (c : ℂ) (b : ℝ) (hb : 0 ≤ b)
    (F : ℂ → Lp ℝ 2 P) (hF : CircleIntegrable F c b)
    (f : ℂ → Ω → ℝ) (hf : Measurable (Function.uncurry f))
    (heq : ∀ v ∈ sphere c b, (⇑(F v)) =ᵐ[P] f v) :
    (⇑(Real.circleAverage F c b)) =ᵐ[P] fun ω => Real.circleAverage (fun v => f v ω) c b := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))
  have hI : Integrable (fun θ => F (circleMap c b θ)) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hF
  have hm : Measurable (fun p : ℝ × Ω => f (circleMap c b p.1) p.2) :=
    hf.comp (((measurable_circleMap c b).comp measurable_fst).prodMk measurable_snd)
  have he θ : (⇑(F (circleMap c b θ))) =ᵐ[P] f (circleMap c b θ) :=
    heq _ (circleMap_mem_sphere c hb θ)
  have hraw := L2_integral_ae_eq_integral μ _ hI (fun θ ω => f (circleMap c b θ) ω) hm.aestronglyMeasurable he
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  filter_upwards [Lp.coeFn_smul (2*Real.pi)⁻¹ (∫ θ, F (circleMap c b θ) ∂μ),hraw] with ω hs hr
  rw [hs, Pi.smul_apply, smul_eq_mul, hr, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, smul_eq_mul]

/-- Parameter-dependent real Poisson circle averages are jointly measurable. -/
theorem measurable_poissonExtension {Ω : Type*} [MeasurableSpace Ω]
    (c : ℂ) (b : ℝ) (f : Ω → ℂ → ℝ)
    (hf : Measurable (fun p : Ω × ℂ => f p.1 p.2)) :
    Measurable (fun p : Ω × ℂ => Real.circleAverage (poissonKernel c p.2 • f p.1) c b) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))
  have hm : Measurable (fun p : (Ω × ℂ) × ℝ =>
      poissonKernel c p.1.2 (circleMap c b p.2)*f p.1.1 (circleMap c b p.2)) := by
    have hraw : Measurable (fun p : (Ω × ℂ) × ℝ =>
        (‖circleMap c b p.2-c‖^2-‖p.1.2-c‖^2)/
          ‖(circleMap c b p.2-c)-(p.1.2-c)‖^2) := by fun_prop
    have hk : Measurable (fun p : (Ω × ℂ) × ℝ => poissonKernel c p.1.2 (circleMap c b p.2)) := by
      convert hraw using 1
      funext p
      exact poissonKernel_def _ _ _
    exact hk.mul (hf.comp ((measurable_fst.fst).prodMk
      ((measurable_circleMap c b).comp measurable_snd)))
  have hi : Measurable (fun p : Ω × ℂ => ∫ θ,
      poissonKernel c p.2 (circleMap c b θ)*f p.1 (circleMap c b θ) ∂μ) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : (fun p : Ω × ℂ => Real.circleAverage (poissonKernel c p.2 • f p.1) c b) =
      (fun p => (2*Real.pi)⁻¹*(∫ θ,
        poissonKernel c p.2 (circleMap c b θ)*f p.1 (circleMap c b θ) ∂μ)) := by
    funext p
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rfl
  rw [he]
  exact measurable_const.mul hi

/-- Smooth harmonic Poisson extension at an arbitrary disk center. -/
theorem harmonicOnNhd_poissonExtension (c : ℂ) (b : ℝ) (hb : 0 < b)
    (f : ℂ → ℝ) (hf : CircleIntegrable f c b) :
    InnerProductSpace.HarmonicOnNhd
      (fun z => Real.circleAverage (poissonKernel c z • f) c b) (ball c b) ∧
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => Real.circleAverage (poissonKernel c z • f) c b) (ball c b) := by
  let g (u : ℂ) := f (u+c)
  have hmap θ : circleMap 0 b θ+c = circleMap c b θ := by
    simp only [circleMap, zero_add]
    ring
  have hg : CircleIntegrable g 0 b := by
    change IntervalIntegrable (fun θ => f (circleMap 0 b θ+c)) volume 0 (2*Real.pi)
    simpa only [hmap] using (show IntervalIntegrable (fun θ => f (circleMap c b θ)) volume 0 (2*Real.pi) from hf)
  have hgC : CircleIntegrable (fun u : ℂ => (g u : ℂ)) 0 b := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hg ⊢
    exact Complex.ofRealCLM.integrable_comp hg
  let F (z : ℂ) := Real.circleAverage
    (fun u => herglotzRieszKernel 0 (z-c) u • (g u : ℂ)) 0 b
  have hbase := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hgC
  have hnot z (hz : z ∈ ball c b) : z-c ∉ sphere 0 |b| := by
    rw [abs_of_pos hb]
    intro hs
    have hn := mem_sphere_iff_norm.mp hs
    rw [sub_zero] at hn
    exact (mem_ball_iff_norm.mp hz).ne hn
  have hFa z (hz : z ∈ ball c b) : AnalyticAt ℂ F z :=
    (hbase (z-c) (hnot z hz)).comp (f := fun v : ℂ => v-c)
      (show AnalyticAt ℂ (fun v : ℂ => v-c) z by fun_prop)
  have he z (hz : z ∈ ball c b) : (F z).re =
      Real.circleAverage (poissonKernel c z • f) c b := by
    rw [re_circleAverage_herglotzRieszKernel_smul hg (hnot z hz)]
    rw [← Real.circleAverage_map_add_const (c := c) (f := poissonKernel c z • f)]
    apply Real.circleAverage_congr_sphere
    intro u _
    change (herglotzRieszKernel 0 (z-c) u).re*g u = poissonKernel c z (u+c)*f (u+c)
    rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_add_const]
  have heN z (hz : z ∈ ball c b) :
      (fun z => (F z).re) =ᶠ[𝓝 z] fun z => Real.circleAverage (poissonKernel c z • f) c b :=
    (show ∀ᶠ y in 𝓝 z, y ∈ ball c b from isOpen_ball.mem_nhds hz).mono (fun y hy => he y hy)
  refine ⟨fun z hz => ?_,fun z hz => ?_⟩
  · exact (InnerProductSpace.harmonicAt_congr_nhds (heN z hz)).mp ((hFa z hz).harmonicAt_re)
  · have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => (F z).re) z :=
      Complex.reCLM.contDiff.comp_contDiffAt z ((hFa z hz).restrictScalars (𝕜 := ℝ)).contDiffAt
    exact (hr.congr_of_eventuallyEq (heN z hz).symm).contDiffWithinAt

/-- Extend jointly measurable random data from a closed disk by zero, retaining relative
sample continuity and every interior coordinate. -/
theorem exists_measurable_closedBall_extension {Ω : Type*} [MeasurableSpace Ω]
    (c : ℂ) (a : ℝ) (Z : {z : ℂ // z ∈ closedBall c a} → Ω → ℝ)
    (hZm : Measurable (fun p : Ω × {z : ℂ // z ∈ closedBall c a} => Z p.2 p.1))
    (hZc : ∀ ω, Continuous (fun z => Z z ω)) :
    ∃ B : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => B p.1 p.2) ∧
      (∀ ω, ContinuousOn (B ω) (closedBall c a)) ∧
      (∀ ω (z : {z : ℂ // z ∈ closedBall c a}), B ω z.1 = Z z ω) := by
  classical
  let A : Set (Ω × ℂ) := {p | p.2 ∈ closedBall c a}
  let B (ω : Ω) (z : ℂ) := if hz : z ∈ closedBall c a then Z ⟨z,hz⟩ ω else 0
  have hA : MeasurableSet A := isClosed_closedBall.measurableSet.preimage measurable_snd
  have hbranch : Measurable (fun p : A => Z ⟨p.1.2,p.2⟩ p.1.1) :=
    hZm.comp (measurable_subtype_coe.fst.prodMk
      (measurable_subtype_coe.snd.subtype_mk))
  refine ⟨B,?_,?_,fun ω z => by simp only [B, dite_eq_left z.2]⟩
  · exact Measurable.dite hbranch measurable_const hA
  · intro ω
    rw [continuousOn_iff_continuous_domRestrict]
    convert hZc ω using 1
    funext z
    change (if hz : z.1 ∈ closedBall c a then Z ⟨z.1,hz⟩ ω else 0) = Z z ω
    simp only [dite_eq_left z.2]

/-- A real Gaussian Poisson family with its exact covariance admits a jointly measurable
smooth harmonic modification on every smaller disk in the same probability space. -/
theorem exists_local_harmonic_poisson_modification
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℂ) (R ρ b : ℝ) (hρ : 0 < ρ) (hb : 0 < b) (hbρ : b < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ) (hG : IsGaussianProcess H P)
    (hmeas : ∀ z, Measurable (H z)) (hmem : ∀ z, MemLp (H z) 2 P)
    (hmean : ∀ z, (∫ ω, H z ω ∂P) = 0)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖) :
    ∃ V : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => V p.1 p.2) ∧
      (∀ ω, InnerProductSpace.HarmonicOnNhd (V ω) (ball c b) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (V ω) (ball c b)) ∧
      (∀ z (hz : z ∈ ball c b), (fun ω => V ω z) =ᵐ[P]
        H ⟨z,ball_subset_ball hbρ.le hz⟩) := by
  classical
  let a := (b+ρ)/2
  have ha : 0 < a := by dsimp only [a]; linarith
  have hba : b < a := by dsimp only [a]; linarith
  have haρ : a < ρ := by dsimp only [a]; linarith
  obtain ⟨Z,hZm,hZc,hZe⟩ := exists_continuous_poisson_gaussian_on_closedBall
    P c R ρ a hρ ha haρ H hG hmeas hmem hmean hcov
  have hZj : Measurable (fun p : Ω × {z : ℂ // z ∈ closedBall c a} => Z p.2 p.1) :=
    (measurable_uncurry_of_continuous_of_measurable hZc hZm).comp measurable_swap
  obtain ⟨B,hBm,hBc,hB⟩ := exists_measurable_closedBall_extension c a Z hZj hZc
  let U (v : ℂ) : Lp ℝ 2 P := if hv : v ∈ ball c ρ then (hmem ⟨v,hv⟩).toLp (H ⟨v,hv⟩) else 0
  have hUc : ContinuousOn U (ball c ρ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert continuous_poisson_gaussian_toLp P c R ρ hρ H hmem hmean hcov using 1
    funext v
    change (if hv : v.1 ∈ ball c ρ then (hmem ⟨v.1,hv⟩).toLp (H ⟨v.1,hv⟩) else 0) = _
    simp only [dite_eq_left v.2]
  have hUm z (hz : z ∈ ball c ρ) : (∫ ω, U z ω ∂P) = 0 := by
    simp only [U, dite_eq_left hz]
    rw [integral_congr_ae (hmem ⟨z,hz⟩).coeFn_toLp]
    exact hmean ⟨z,hz⟩
  have hUcov z (hz : z ∈ ball c ρ) w (hw : w ∈ ball c ρ) :
      covariance (U z) (U w) P = Real.log R+Real.log ρ-
        Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖ := by
    simp only [U, dite_eq_left hz, dite_eq_left hw]
    rw [covariance_congr_ae (hmem ⟨z,hz⟩).coeFn_toLp (hmem ⟨w,hw⟩).coeFn_toLp]
    exact hcov ⟨z,hz⟩ ⟨w,hw⟩
  let V (ω : Ω) (z : ℂ) := Real.circleAverage (poissonKernel c z • B ω) c b
  have hBs ω : CircleIntegrable (B ω) c b :=
    ((hBc ω).mono (sphere_subset_closedBall.trans (closedBall_subset_closedBall hba.le))).circleIntegrable hb.le
  refine ⟨V,measurable_poissonExtension c b B hBm,
    fun ω => harmonicOnNhd_poissonExtension c b hb (B ω) (hBs ω),?_⟩
  intro z hz
  have hc : CircleIntegrable (poissonKernel c z • U) c b :=
    ((continuousOn_poissonKernel_sphere c z b hb hz).smul
      (hUc.mono (sphere_subset_larger_ball c b ρ hbρ))).circleIntegrable hb.le
  have hf : Measurable (fun p : ℂ × Ω => poissonKernel c z p.1*B p.2 p.1) := by
    have hk : Measurable (fun v : ℂ => poissonKernel c z v) := by
      rw [show poissonKernel c z = (fun v : ℂ =>
        (‖v-c‖^2-‖z-c‖^2)/‖(v-c)-(z-c)‖^2) from funext (poissonKernel_def c z)]
      fun_prop
    exact (hk.comp measurable_fst).mul (hBm.comp measurable_swap)
  have he v (hv : v ∈ sphere c b) :
      (⇑((poissonKernel c z • U) v)) =ᵐ[P] fun ω => poissonKernel c z v*B ω v := by
    have hva : v ∈ closedBall c a :=
      mem_closedBall_iff_norm.mpr ((mem_sphere_iff_norm.mp hv).le.trans hba.le)
    have hvρ := sphere_subset_larger_ball c b ρ hbρ hv
    change (⇑(poissonKernel c z v • U v)) =ᵐ[P] _
    filter_upwards [Lp.coeFn_smul (poissonKernel c z v) (U v),
      (hmem ⟨v,hvρ⟩).coeFn_toLp, hZe ⟨v,hva⟩] with ω hs hu hz
    have hUv : U v = (hmem ⟨v,hvρ⟩).toLp (H ⟨v,hvρ⟩) := by
      simp only [U, dite_eq_left hvρ]
    rw [hs, Pi.smul_apply, smul_eq_mul, hUv, hu, ← hz, ← hB ω ⟨v,hva⟩]
  have hraw := circleAverage_L2_ae_eq P c b hb.le _ hc
    (fun v ω => poissonKernel c z v*B ω v) hf he
  rw [poisson_circleAverage_L2_eq P c z R ρ b hρ hb hbρ hz U hUc hUm hUcov] at hraw
  have hzρ : z ∈ ball c ρ := mem_ball_iff_norm.mpr ((mem_ball_iff_norm.mp hz).trans hbρ)
  have hUz : (⇑(U z)) =ᵐ[P] H ⟨z,hzρ⟩ := by
    simp only [U, dite_eq_left hzρ]
    exact (hmem _).coeFn_toLp
  exact hraw.symm.trans hUz

/-- A continuous radial clamp into a closed disk; it fixes every point of that disk. -/
noncomputable def poissonDiskClamp (c : ℂ) (d : ℝ) (z : ℂ) : ℂ :=
  c+(d/max d ‖z-c‖) • (z-c)

/-- Positive-radius radial clamps are continuous everywhere. -/
theorem continuous_poissonDiskClamp (c : ℂ) (d : ℝ) (hd : 0 < d) :
    Continuous (poissonDiskClamp c d) := by
  unfold poissonDiskClamp
  apply continuous_const.add
  change Continuous ((fun z : ℂ => d/max d ‖z-c‖) • (fun z : ℂ => z-c))
  apply Continuous.smul
  · exact continuous_const.div (continuous_const.max (continuous_id.sub continuous_const).norm)
      (fun z => ne_of_gt (hd.trans_le (le_max_left _ _)))
  · fun_prop

/-- The radial clamp takes values in its stated closed disk. -/
theorem poissonDiskClamp_mem_closedBall (c z : ℂ) (d : ℝ) (hd : 0 < d) :
    poissonDiskClamp c d z ∈ closedBall c d := by
  rw [mem_closedBall_iff_norm, poissonDiskClamp, add_sub_cancel_left, norm_smul,
    Real.norm_eq_abs, abs_of_pos (div_pos hd (hd.trans_le (le_max_left _ _)))]
  rw [div_mul_eq_mul_div, div_le_iff₀ (hd.trans_le (le_max_left _ _))]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hd.le

/-- The clamp agrees exactly with the identity on its closed target disk. -/
theorem poissonDiskClamp_eq_self (c z : ℂ) (d : ℝ) (hd : 0 < d) (hz : ‖z-c‖ ≤ d) :
    poissonDiskClamp c d z = z := by
  rw [poissonDiskClamp, max_eq_left hz, div_self hd.ne', one_smul, add_sub_cancel]

/-- Every open disk has a positive-radius concentric exhaustion with a larger smoothing disk. -/
theorem exists_poisson_inner_disk_exhaustion (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ d b : ℕ → ℝ, (∀ j, 0 < d j ∧ d j < b j ∧ b j < ρ) ∧
      (∀ r : ℝ, r < ρ → ∃ j, r < d j) := by
  let d (j : ℕ) := ρ-ρ/(j+2)
  let b (j : ℕ) := (d j+ρ)/2
  have hd j : 0 < d j ∧ d j < b j ∧ b j < ρ := by
    have hj : 1 < (j : ℝ)+2 := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    have hp : 0 < ρ/((j : ℝ)+2) := div_pos hρ (by positivity)
    have hq : ρ/((j : ℝ)+2) < ρ := (div_lt_self hρ hj)
    dsimp only [d,b]
    constructor
    · linarith
    · constructor <;> linarith
  have hlim : Tendsto d atTop (𝓝 ρ) := by
    have hr : Tendsto (fun j : ℕ => ρ/((j : ℝ)+2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    simpa only [d,sub_zero] using (tendsto_const_nhds.sub hr :
      Tendsto (fun j : ℕ => ρ-ρ/((j : ℝ)+2)) atTop (𝓝 (ρ-0)))
  refine ⟨d,b,hd,fun r hr => ?_⟩
  exact (hlim.eventually (Ioi_mem_nhds hr)).exists

/-- Gluing the original family's local Poisson extensions gives a jointly measurable
harmonic modification throughout the disk, with one common smoothness event. -/
theorem exists_harmonic_poisson_modification
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℂ) (R ρ : ℝ) (hρ : 0 < ρ)
    (H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ) (hG : IsGaussianProcess H P)
    (hmeas : ∀ z, Measurable (H z)) (hmem : ∀ z, MemLp (H z) 2 P)
    (hmean : ∀ z, (∫ ω, H z ω ∂P) = 0)
    (hcov : ∀ z w, covariance (H z) (H w) P = Real.log R+Real.log ρ-
      Real.log ‖(ρ : ℂ)^2-(z.1-c)*star (w.1-c)‖) :
    ∃ V : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => V p.1 p.2) ∧
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (V ω) (ball c ρ)) ∧
      (∀ z (hz : z ∈ ball c ρ), (fun ω => V ω z) =ᵐ[P] H ⟨z,hz⟩) := by
  classical
  obtain ⟨d,b,hdb,hcover⟩ := exists_poisson_inner_disk_exhaustion ρ hρ
  have hloc j := exists_local_harmonic_poisson_modification P c R ρ (b j) hρ
    ((hdb j).1.trans (hdb j).2.1) (hdb j).2.2 H hG hmeas hmem hmean hcov
  choose W hWm hWh hWe using hloc
  let Z (j : ℕ) (z : ℂ) (ω : Ω) := W j ω (poissonDiskClamp c (d j) z)
  have hZc j ω : Continuous (fun z => Z j z ω) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have hz : poissonDiskClamp c (d j) z ∈ ball c (b j) :=
      mem_ball_iff_norm.mpr ((mem_closedBall_iff_norm.mp
        (poissonDiskClamp_mem_closedBall c z (d j) (hdb j).1)).trans_lt (hdb j).2.1)
    exact ((hWh j ω).1.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).comp
      (continuous_poissonDiskClamp c (d j) (hdb j).1).continuousAt
  have hZm j z : Measurable (Z j z) :=
    (hWm j).comp (measurable_id.prodMk measurable_const)
  let A (j : ℕ) : Set {z : ℂ // z ∈ ball c ρ} := {z | z.1 ∈ ball c (d j)}
  have hAo j : IsOpen (A j) := isOpen_ball.preimage continuous_subtype_val
  have hAc z : ∃ j, z ∈ A j := by
    obtain ⟨j,hj⟩ := hcover ‖z.1-c‖ (mem_ball_iff_norm.mp z.2)
    exact ⟨j,mem_ball_iff_norm.mpr hj⟩
  have hZe j z (hz : z ∈ A j) : Z j z.1 =ᵐ[P] H z := by
    have hz' : ‖z.1-c‖ ≤ d j := (mem_ball_iff_norm.mp hz).le
    simp only [Z,poissonDiskClamp_eq_self c z.1 (d j) (hdb j).1 hz']
    exact hWe j z.1 (mem_ball_iff_norm.mpr ((mem_ball_iff_norm.mp hz).trans (hdb j).2.1))
  obtain ⟨Y,hYm,hYc,hYe,hYj⟩ := exists_continuous_modification_of_open_cover
    P H A hAo hAc (fun j z => Z j z.1) (fun j z => hZm j z.1)
    (fun j ω => (hZc j ω).comp continuous_subtype_val) hZe
  let V (ω : Ω) (z : ℂ) := if hz : z ∈ ball c ρ then Y ⟨z,hz⟩ ω else 0
  have hVm : Measurable (fun p : Ω × ℂ => V p.1 p.2) := by
    let S : Set (Ω × ℂ) := {p | p.2 ∈ ball c ρ}
    have hS : MeasurableSet S := isOpen_ball.measurableSet.preimage measurable_snd
    have hbranch : Measurable (fun p : S => Y ⟨p.1.2,p.2⟩ p.1.1) :=
      hYj.comp (measurable_subtype_coe.fst.prodMk measurable_subtype_coe.snd.subtype_mk)
    exact Measurable.dite hbranch measurable_const hS
  have hVc ω : ContinuousOn (V ω) (ball c ρ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert hYc ω using 1
    funext z
    change (if hz : z.1 ∈ ball c ρ then Y ⟨z.1,hz⟩ ω else 0) = Y z ω
    simp only [dite_eq_left z.2]
  have hVe z (hz : z ∈ ball c ρ) : (fun ω => V ω z) =ᵐ[P] H ⟨z,hz⟩ := by
    simpa only [V,dite_eq_left hz] using hYe ⟨z,hz⟩
  have hsim j : ∀ᵐ ω ∂P, ∀ z ∈ ball c (d j), V ω z = Z j z ω := by
    have h := indistinguishable_of_edist_modification_on (T := ℂ) (E := ℝ) isOpen_ball
      (ae_of_all P (fun ω => (hVc ω).mono (ball_subset_ball ((hdb j).2.1.trans (hdb j).2.2).le)))
      (ae_of_all P (fun ω => (hZc j ω).continuousOn)) (fun z hz => ?_)
    · simpa only [edist_eq_zero] using h
    · have hzρ : z ∈ ball c ρ := mem_ball_iff_norm.mpr
        ((mem_ball_iff_norm.mp hz).trans ((hdb j).2.1.trans (hdb j).2.2))
      have hzZ : Z j z =ᵐ[P] H ⟨z,hzρ⟩ := hZe j ⟨z,hzρ⟩ hz
      filter_upwards [hVe z hzρ,hzZ] with ω hv hz'
      have hzero : edist (V ω z) (Z j z ω) = 0 := by rw [hv,hz',edist_self]
      exact hzero
  have hcommon : ∀ᵐ ω ∂P, ∀ j z, z ∈ ball c (d j) → V ω z = W j ω z := by
    rw [ae_all_iff]
    intro j
    filter_upwards [hsim j] with ω hω
    intro z hz
    have hn := (mem_ball_iff_norm.mp hz).le
    simpa only [Z,poissonDiskClamp_eq_self c z (d j) (hdb j).1 hn] using hω z hz
  refine ⟨V,hVm,?_,hVe⟩
  filter_upwards [hcommon] with ω hω
  have hpoint z (hz : z ∈ ball c ρ) :
      InnerProductSpace.HarmonicAt (V ω) z ∧ ContDiffAt ℝ (⊤ : ℕ∞) (V ω) z := by
    obtain ⟨j,hj⟩ := hcover ‖z-c‖ (mem_ball_iff_norm.mp hz)
    have hzd : z ∈ ball c (d j) := mem_ball_iff_norm.mpr hj
    have hzb : z ∈ ball c (b j) := mem_ball_iff_norm.mpr (hj.trans (hdb j).2.1)
    have heq : V ω =ᶠ[𝓝 z] W j ω :=
      (show ∀ᶠ x in 𝓝 z, x ∈ ball c (d j) from isOpen_ball.mem_nhds hzd).mono
        (fun x hx => hω j x hx)
    refine ⟨(InnerProductSpace.harmonicAt_congr_nhds heq).mpr ((hWh j ω).1 z hzb),?_⟩
    exact (((hWh j ω).2 z hzb).contDiffAt (isOpen_ball.mem_nhds hzb)).congr_of_eventuallyEq heq
  exact ⟨fun z hz => (hpoint z hz).1,fun z hz => (hpoint z hz).2.contDiffWithinAt⟩

/-- The literal exterior collars admit a jointly measurable smooth harmonic Gaussian limit with
exactly the harmonic covariance formula of `DOZZ.exists_exteriorPinned_markov_uniform`, on the
original given probability space. -/
theorem exists_exteriorPinned_harmonic_poisson_family
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) :
    ∃ V : Ω → ℂ → ℝ, Measurable (fun p : Ω × ℂ => V p.1 p.2) ∧
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (V ω) (ball c ρ) ∧
        ContDiffOn ℝ (⊤ : ℕ∞) (V ω) (ball c ρ)) ∧
      IsGaussianProcess (fun z : {z : ℂ // z ∈ ball c ρ} => fun ω => V ω z.1) P ∧
      (∀ z (hz : z ∈ ball c ρ), MemLp (fun ω => V ω z) 2 P ∧ (∫ ω, V ω z ∂P) = 0 ∧
        Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
          (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P) atTop (𝓝 0)) ∧
      (∀ z w, z ∈ ball c ρ → w ∈ ball c ρ →
        covariance (fun ω => V ω z) (fun ω => V ω w) P = Real.log R+Real.log ρ-
          Real.log ‖(ρ : ℂ)^2-(z-c)*star (w-c)‖) := by
  let _ := hX.1
  obtain ⟨H,hG,hH,hcov⟩ := exists_exteriorPinned_poisson_gaussian_family_closed
    P X Xc hX hc c R ρ ε δ hR hρ hε hεδ hpin
  obtain ⟨V,hVm,hVh,hVe⟩ := exists_harmonic_poisson_modification P c R ρ hρ H hG
    (fun z => (hH z).1) (fun z => (hH z).2.1) (fun z => (hH z).2.2.1) hcov
  refine ⟨V,hVm,hVh,hG.congr (fun z => (hVe z.1 z.2).symm),?_,?_⟩
  · intro z hz
    refine ⟨MemLp.ae_eq (hVe z hz).symm (hH ⟨z,hz⟩).2.1,?_,?_⟩
    · rw [integral_congr_ae (hVe z hz)]
      exact (hH ⟨z,hz⟩).2.2.1
    · have he k : eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
          (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-V ω z) 2 P =
        eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
          (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-H ⟨z,hz⟩ ω) 2 P :=
        eLpNorm_congr_ae ((ae_eq_refl _).sub (hVe z hz))
      simp_rw [he]
      exact (hH ⟨z,hz⟩).2.2.2
  · intro z w hz hw
    rw [covariance_congr_ae (hVe z hz) (hVe w hw)]
    exact hcov ⟨z,hz⟩ ⟨w,hw⟩

end DOZZ.Proofs
