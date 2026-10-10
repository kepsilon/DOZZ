/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.HarmonicMoments
public import Mathlib.MeasureTheory.Function.FactorsThrough
public import Mathlib.Analysis.Normed.Module.Dual
/-!
# Raw circle versions and interior Banach limits

Raw evaluation L² limits have measurable coordinate versions. Continuous candidates
and countably many finite-valued parameter approximations give a jointly measurable
version in the same raw sigma algebra, with a common agreement event. Smooth annular
tests retain the original cubic energy contract and eventually lie inside the disk.
The scalar annular transport extends to Banach observables by separating duals;
radial concentration and uniform smoothing give norm convergence of circle averages.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped Topology ENNReal NNReal
namespace DOZZ.Proofs
/-- Continuous sample fields with coordinate versions in a raw sigma algebra have a joint raw version. -/
theorem exists_raw_joint_continuous_modification {Ω T : Type*} [MeasurableSpace Ω]
    [MetricSpace T] [MeasurableSpace T] [BorelSpace T] [SecondCountableTopology T]
    (P : Measure Ω) (m0 : MeasurableSpace Ω) (F : Ω → T → ℝ)
    (hF : ∀ᵐ ω ∂P, Continuous (F ω))
    (hversion : ∀ t, ∃ g : Ω → ℝ, Measurable[m0] g ∧ g =ᵐ[P] fun ω => F ω t) :
    ∃ G : Ω → T → ℝ, Measurable[m0.prod inferInstance] (fun p : Ω × T => G p.1 p.2) ∧
      (∀ᵐ ω ∂P, ∀ t, G ω t = F ω t) := by
  choose g hgm hge using hversion
  let s : ℕ → SimpleFunc T T := stronglyMeasurable_id.approx
  let U (n : ℕ) (p : Ω × T) : ℝ := g (s n p.2) p.1
  have hUm (n : ℕ) : Measurable[m0.prod inferInstance] (U n) := by
    let : MeasurableSpace Ω := m0
    have hfin : Measurable (fun p : Ω × (s n).range => g p.2.1 p.1) :=
      measurable_from_prod_countable_left (fun t => hgm t.1)
    have hm : Measurable (fun p : Ω × T =>
        (⟨s n p.2,SimpleFunc.mem_range_self _ _⟩ : (s n).range)) :=
      ((s n).measurable.comp measurable_snd).subtype_mk
    exact hfin.comp (measurable_fst.prodMk hm)
  let G : Ω → T → ℝ := fun ω t => limUnder atTop (fun n => U n (ω,t))
  refine ⟨G,?_,?_⟩
  · exact (StronglyMeasurable.limUnder (fun n => (hUm n).stronglyMeasurable)).measurable
  · have hmatch : ∀ᵐ ω ∂P, ∀ j : (n : ℕ) × (s n).range, g j.2.1 ω = F ω j.2.1 :=
      ae_all_iff.mpr (fun j => hge j.2.1)
    filter_upwards [hF,hmatch] with ω hc hm
    intro t
    apply Tendsto.limUnder_eq
    have he : (fun n => U n (ω,t)) = fun n => F ω (s n t) := by
      funext n
      exact hm ⟨n,⟨s n t,SimpleFunc.mem_range_self _ _⟩⟩
    rw [he]
    exact (hc.tendsto t).comp (stronglyMeasurable_id.tendsto_approx t)
/-- A literal random L² limit of raw-sigma-measurable variables has a raw measurable coordinate version. -/
theorem exists_raw_measurable_version_of_L2_limit {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m0 : MeasurableSpace Ω) (U : ℕ → Ω → ℝ) (V : Ω → ℝ)
    (hUm : ∀ n, Measurable[m0] (U n)) (hU : ∀ n, MemLp (U n) 2 P) (hV : MemLp V 2 P)
    (hlim : Tendsto (fun n => eLpNorm (fun ω => U n ω-V ω) 2 P) atTop (𝓝 0)) :
    ∃ g : Ω → ℝ, Measurable[m0] g ∧ g =ᵐ[P] V := by
  let : MeasurableSpace Ω := mΩ
  have ht := tendsto_toLp_of_eLpNorm_sub hU hV hlim
  obtain ⟨s,_hs,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae'
  let g : Ω → ℝ := fun ω => limUnder atTop (fun n => U (s n) ω)
  have hgm : Measurable[m0] g := by
    let : MeasurableSpace Ω := m0
    exact (StronglyMeasurable.limUnder (fun n => (hUm (s n)).stronglyMeasurable)).measurable
  refine ⟨g,hgm,?_⟩
  have hcoords : ∀ᵐ ω ∂P, ∀ n, (hU (s n)).toLp (U (s n)) ω = U (s n) ω :=
    ae_all_iff.mpr (fun n => (hU (s n)).coeFn_toLp)
  filter_upwards [hAE,hcoords,hV.coeFn_toLp] with ω htω hu hv
  apply Tendsto.limUnder_eq
  rw [hv] at htω
  exact htω.congr (fun n => hu n)

/-- Every distribution test evaluation is measurable for its literal raw evaluation sigma algebra. -/
theorem measurable_raw_distribution_eval {Ω : Type*} (D : Ω → Distr) (f : TestFn) :
    Measurable[MeasurableSpace.comap (fun ω => fun g : TestFn => D ω g) MeasurableSpace.pi]
      (fun ω => D ω f) :=
  (measurable_pi_apply f).comp (comap_measurable _)

/-- Raw evaluation approximants produce a raw coordinate version of their literal L² limit. -/
theorem exists_raw_distribution_limit_version {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : Ω → Distr) (f : ℕ → TestFn) (V : Ω → ℝ)
    (hD : ∀ n, MemLp (fun ω => D ω (f n)) 2 P) (hV : MemLp V 2 P)
    (hlim : Tendsto (fun n => eLpNorm (fun ω => D ω (f n)-V ω) 2 P) atTop (𝓝 0)) :
    ∃ g : Ω → ℝ,
      Measurable[MeasurableSpace.comap (fun ω => fun t : TestFn => D ω t) MeasurableSpace.pi] g ∧
      g =ᵐ[P] V :=
  exists_raw_measurable_version_of_L2_limit P _ _ V
    (fun n => measurable_raw_distribution_eval D (f n)) hD hV hlim

/-- A translated annular probability stays within its explicit shrinking outer radius. -/
theorem circleAnnularDensity_radius_le (x : ℂ) (r : ℝ) (n : ℕ) (z : ℂ)
    (hz : circleAnnularDensity x r n z ≠ 0) :
    ‖z-x‖ ≤ Real.exp (-r)+Real.exp (-r)/((n : ℝ)+2) := by
  have hne : DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • (z-x)) ≠ 0 := by
    intro h
    exact hz (by rw [circleAnnularDensity,h,mul_zero])
  have hnear := DOZZ.annularProbabilityDensity_radius_bound n _ hne
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (Real.exp_pos _))] at hnear
  have hup : (Real.exp (-r))⁻¹*‖z-x‖ ≤ 1+1/((n : ℝ)+2) := by
    linarith only [le_abs_self ((Real.exp (-r))⁻¹*‖z-x‖-1),hnear]
  have hm := mul_le_mul_of_nonneg_left hup (Real.exp_pos (-r)).le
  rw [← mul_assoc,mul_inv_cancel₀ (Real.exp_ne_zero _),one_mul] at hm
  simpa only [mul_add,mul_one,mul_one_div] using hm

/-- The closed support of each annular density obeys the shrinking radius bound. -/
theorem tsupport_circleAnnularDensity_radius_subset (x : ℂ) (r : ℝ) (n : ℕ) :
    tsupport (circleAnnularDensity x r n) ⊆
      closedBall x (Real.exp (-r)+Real.exp (-r)/((n : ℝ)+2)) := by
  apply closure_minimal
  · intro z hz
    exact mem_closedBall_iff_norm.mpr (circleAnnularDensity_radius_le x r n z hz)
  · exact isClosed_closedBall

/-- Every interior circle has annular approximants eventually supported in any larger interior subdisk. -/
theorem eventually_circleAnnularDensity_support_inner (c x : ℂ) (r b : ℝ)
    (hb : ‖x-c‖+Real.exp (-r) < b) :
    ∀ᶠ n : ℕ in atTop, tsupport (circleAnnularDensity x r n) ⊆ closedBall c b := by
  have ht : Tendsto (fun n : ℕ => Real.exp (-r)/((n : ℝ)+2)) atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (Real.exp (-r))).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat]
  filter_upwards [ht.eventually_lt_const (by linarith : 0 < b-(‖x-c‖+Real.exp (-r)))] with n hn
  intro z hz
  have hz' := mem_closedBall_iff_norm.mp (tsupport_circleAnnularDensity_radius_subset x r n hz)
  have htri : ‖z-c‖ ≤ ‖z-x‖+‖x-c‖ := by simpa only [sub_add_sub_cancel] using norm_add_le (z-x) (x-c)
  exact mem_closedBall_iff_norm.mpr (by linarith only [hz',htri,hn])

/-- Smooth circle approximants can retain the exact cubic energy contract and eventually lie inside their disk. -/
theorem exists_circleAnnular_testFn_eventually_interior (c x : ℂ) (ρ r : ℝ)
    (hx : ‖x-c‖+Real.exp (-r) < ρ) :
    ∃ f : ℕ → TestFn,
      (∀ n, tsupport (f n) ⊆ closedBall (0 : ℂ) (‖x‖+2*Real.exp (-r)+1)) ∧
      (∀ n z, |f n z-circleAnnularDensity x r n z| < 1/((n : ℝ)+2)^3) ∧
      (∀ᶠ n in atTop, tsupport (f n) ⊆ ball c ρ) := by
  classical
  obtain ⟨b,hxb,hbρ⟩ := exists_between hx
  obtain ⟨d,hbd,hdρ⟩ := exists_between hbρ
  have hb : 0 < b := (add_pos_of_nonneg_of_pos (norm_nonneg _) (Real.exp_pos _)).trans hxb
  let φ : ContDiffBump c := ⟨b,d,hb,hbd⟩
  obtain ⟨g,hg⟩ := exists_testFn_circleAnnular_approx x r (fun n => 1/((n : ℝ)+2)^3)
    (fun n => by positivity)
  let A : TestFn →L[ℝ] TestFn := TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff
  let f (n : ℕ) : TestFn := if tsupport (circleAnnularDensity x r n) ⊆ closedBall c b then A (g n) else g n
  have hsupport n : tsupport (A (g n)) ⊆ tsupport (g n) := by
    change tsupport (fun z => g n z*φ z) ⊆ tsupport (g n)
    exact tsupport_mul_subset_left
  have hcut n : tsupport (A (g n)) ⊆ ball c ρ := by
    change tsupport (fun z => g n z*φ z) ⊆ ball c ρ
    exact tsupport_mul_subset_right.trans (φ.tsupport_eq.subset.trans (closedBall_subset_ball hdρ))
  refine ⟨f,fun n => ?_,fun n z => ?_,?_⟩
  · by_cases hn : tsupport (circleAnnularDensity x r n) ⊆ closedBall c b
    · simp only [f,ite_eq_left hn]
      exact (hsupport n).trans (hg n).1
    · simp only [f,ite_eq_right hn]
      exact (hg n).1
  · by_cases hn : tsupport (circleAnnularDensity x r n) ⊆ closedBall c b
    · simp only [f,ite_eq_left hn]
      have hφ : circleAnnularDensity x r n z*φ z = circleAnnularDensity x r n z := by
        by_cases hz : circleAnnularDensity x r n z = 0
        · rw [hz,zero_mul]
        · rw [φ.one_of_mem_closedBall (hn (subset_closure hz)),mul_one]
      change |g n z*φ z-circleAnnularDensity x r n z| < _
      rw [← hφ,← sub_mul,abs_mul,abs_of_nonneg φ.nonneg]
      exact (mul_le_of_le_one_right (abs_nonneg _) φ.le_one).trans_lt ((hg n).2 z)
    · simp only [f,ite_eq_right hn]
      exact (hg n).2 z
  · filter_upwards [eventually_circleAnnularDensity_support_inner c x r b hxb] with n hn
    simp only [f,ite_eq_left hn]
    exact hcut n


/-- A jointly measurable field on interior circle parameters extends measurably by zero elsewhere. -/
theorem measurable_extend_interior_circle_field {Ω : Type*} [MeasurableSpace Ω]
    (c : ℂ) (ρ : ℝ) (G : Ω → {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} → ℝ)
    (hG : Measurable (fun p : Ω × {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} => G p.1 p.2)) :
    Measurable (fun p : Ω × (ℂ × ℝ) =>
      if hp : ‖p.2.1-c‖+Real.exp (-p.2.2) < ρ then G p.1 ⟨p.2,hp⟩ else 0) := by
  classical
  let S : Set (Ω × (ℂ × ℝ)) := {p | ‖p.2.1-c‖+Real.exp (-p.2.2) < ρ}
  have hS : MeasurableSet S := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hbranch : Measurable (fun p : S => G p.1.1 ⟨p.1.2,p.2⟩) := by
    have hm : Measurable (fun p : S =>
        (⟨p.1.2,p.2⟩ : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ})) :=
      (measurable_snd.comp measurable_subtype_coe).subtype_mk
    exact hG.comp ((measurable_fst.comp measurable_subtype_coe).prodMk hm)
  exact Measurable.dite hbranch measurable_const hS

/-- Coordinate raw-sigma versions and a continuous candidate yield a literal raw joint circle version. -/
theorem exists_raw_joint_circle_modification {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (m0 : MeasurableSpace Ω) (c : ℂ) (ρ : ℝ) (F : Ω → ℂ → ℝ → ℝ)
    (hF : ∀ᵐ ω ∂P, Continuous (fun p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ} => F ω p.1.1 p.1.2))
    (hcoord : ∀ p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ},
      ∃ g : Ω → ℝ, Measurable[m0] g ∧ g =ᵐ[P] fun ω => F ω p.1.1 p.1.2) :
    ∃ Dc : Ω → ℂ → ℝ → ℝ, Measurable[m0.prod inferInstance]
      (fun p : Ω × (ℂ × ℝ) => Dc p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, ∀ x r, ‖x-c‖+Real.exp (-r) < ρ → Dc ω x r = F ω x r) := by
  classical
  let : MeasurableSpace Ω := mΩ
  obtain ⟨G,hG,hGe⟩ := exists_raw_joint_continuous_modification P m0
    (fun ω (p : {p : ℂ × ℝ // ‖p.1-c‖+Real.exp (-p.2) < ρ}) => F ω p.1.1 p.1.2) hF hcoord
  let Dc (ω : Ω) (x : ℂ) (r : ℝ) := if h : ‖x-c‖+Real.exp (-r) < ρ then G ω ⟨(x,r),h⟩ else 0
  refine ⟨Dc,?_,?_⟩
  · let : MeasurableSpace Ω := m0
    exact measurable_extend_interior_circle_field c ρ G hG
  · filter_upwards [hGe] with ω hω
    intro x r hx
    simp only [Dc,dite_eq_left hx]
    exact hω ⟨(x,r),hx⟩

section Vector
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
omit [CompleteSpace E] in
/-- Bounded continuous Banach observables have circle averages continuous in radius. -/
theorem continuous_circleAverage_radius_vector (h : ℂ → E) (hh : Continuous h)
    {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) : Continuous (fun t : ℝ => Real.circleAverage h 0 t) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2*Real.pi))
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    exact isFiniteMeasure_restrict.mpr (by simp only [Real.volume_Ioc]; finiteness)
  let _ := hμ
  have hc : Continuous (fun t : ℝ => ∫ θ, h (circleMap 0 t θ) ∂μ) := by
    apply continuous_of_dominated
      (fun t => (hh.stronglyMeasurable.comp_measurable (measurable_circleMap 0 t)).aestronglyMeasurable)
      (fun t => Eventually.of_forall (fun θ => hb (circleMap 0 t θ))) (integrable_const M)
    filter_upwards with θ
    apply hh.comp
    simp only [circleMap]
    fun_prop
  have he t : Real.circleAverage h 0 t = (2*Real.pi)⁻¹ • (∫ θ, h (circleMap 0 t θ) ∂μ) := by
    rw [Real.circleAverage_def,intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp_rw [he]
  exact hc.const_smul _

/-- Banach annular averages have the same literal radial mixture as scalar averages. -/
theorem integral_annular_smul_eq_radial_average (n : ℕ) (h : ℂ → E) (hh : Continuous h)
    {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) :
    (∫ z, DOZZ.annularProbabilityDensity n z • h z) =
      ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • Real.circleAverage h 0 t := by
  have hi : Integrable (fun z => DOZZ.annularProbabilityDensity n z • h z) :=
    ((DOZZ.continuous_annularProbabilityDensity n).smul hh).integrable_of_hasCompactSupport
      (DOZZ.hasCompactSupport_annularProbabilityDensity n).smul_right
  have ha := continuous_circleAverage_radius_vector h hh hb
  have hj : Integrable (fun t => DOZZ.annularRadiusLaw n t • Real.circleAverage h 0 t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((DOZZ.continuous_annularRadiusLaw n).smul ha).integrable_of_hasCompactSupport
      (DOZZ.hasCompactSupport_annularRadiusLaw n).smul_right).restrict
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  rw [← L.integral_comp_comm hi,← L.integral_comp_comm hj]
  simp only [map_smul,smul_eq_mul]
  have hc t : L (Real.circleAverage h 0 t) = Real.circleAverage (L ∘ h) 0 t := by
    exact (L.circleAverage_comp_comm hh.continuousOn.circleIntegrable').symm
  simp_rw [hc]
  exact integral_annular_mul_eq_radial_average n (L ∘ h) (L.continuous.comp hh)

/-- Radial annular probabilities concentrate in norm for continuous Banach observables. -/
theorem tendsto_integral_annularRadiusLaw_smul (a : ℝ → E) (ha : Continuous a) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • a t)
      atTop (𝓝 (a 1)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := tendsto_integral_annularRadiusLaw_mul (fun t => ‖a t-a 1‖) (by fun_prop)
  simp only [sub_self,norm_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
  · intro n
    exact norm_nonneg _
  · intro n
    have hi : Integrable (fun t => DOZZ.annularRadiusLaw n t • a t)
        (volume.restrict (Ioi (0 : ℝ))) :=
      (((DOZZ.continuous_annularRadiusLaw n).smul ha).integrable_of_hasCompactSupport
        (DOZZ.hasCompactSupport_annularRadiusLaw n).smul_right).restrict
    have hconst : (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • a 1) = a 1 := by
      rw [integral_smul_const,DOZZ.integral_annularRadiusLaw,one_smul]
    have hsub : (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • a t)-a 1 =
        ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • (a t-a 1) := by
      calc
        _ = (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • a t)-
            (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • a 1) := by rw [hconst]
        _ = ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t • a t-DOZZ.annularRadiusLaw n t • a 1 :=
          (integral_sub hi ((DOZZ.integrable_annularRadiusLawOn n).smul_const (a 1))).symm
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ (fun t => (smul_sub (DOZZ.annularRadiusLaw n t) (a t) (a 1)).symm)
    dsimp only
    rw [hsub]
    apply (norm_integral_le_integral_norm _).trans_eq
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (DOZZ.annularRadiusLaw_nonneg n ht)]

/-- Unit annular averages converge in Banach norm to their circle average. -/
theorem tendsto_integral_annular_smul (h : ℂ → E) (hh : Continuous h)
    {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) :
    Tendsto (fun n => ∫ z, DOZZ.annularProbabilityDensity n z • h z)
      atTop (𝓝 (Real.circleAverage h 0 1)) := by
  simp_rw [integral_annular_smul_eq_radial_average _ h hh hb]
  exact tendsto_integral_annularRadiusLaw_smul _ (continuous_circleAverage_radius_vector h hh hb)
/-- Translated annular Banach integrals obey the literal scalar transport formula. -/
theorem integral_circleAnnularDensity_smul (x : ℂ) (r : ℝ) (n : ℕ)
    (h : ℂ → E) (hh : Continuous h) :
    (∫ z, circleAnnularDensity x r n z • h z) =
      ∫ z, DOZZ.annularProbabilityDensity n z • h (Real.exp (-r) • z+x) := by
  have hi : Integrable (fun z => circleAnnularDensity x r n z • h z) :=
    ((continuous_circleAnnularDensity x r n).smul hh).integrable_of_hasCompactSupport
      (hasCompactSupport_circleAnnularDensity x r n).smul_right
  have hj : Integrable (fun z => DOZZ.annularProbabilityDensity n z • h (Real.exp (-r) • z+x)) :=
    ((DOZZ.continuous_annularProbabilityDensity n).smul (by fun_prop)).integrable_of_hasCompactSupport
      (DOZZ.hasCompactSupport_annularProbabilityDensity n).smul_right
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  rw [← L.integral_comp_comm hi,← L.integral_comp_comm hj]
  simp only [map_smul,smul_eq_mul]
  exact integral_circleAnnularDensity_mul x r n (L ∘ h)

omit [CompleteSpace E] in
/-- Affine transport of a unit-circle Banach average gives the literal translated circle average. -/
theorem circleAverage_affine_unit_vector (x : ℂ) (r : ℝ) (h : ℂ → E) :
    Real.circleAverage (fun z => h (Real.exp (-r) • z+x)) 0 1 = Real.circleAverage h x (Real.exp (-r)) := by
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [circleMap,zero_add,Complex.ofReal_one,one_mul,Complex.real_smul]
  congr 1
  ring

/-- Translated annuli converge in Banach norm for bounded continuous observables. -/
theorem tendsto_integral_circleAnnular_smul (x : ℂ) (r : ℝ)
    (h : ℂ → E) (hh : Continuous h) {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) :
    Tendsto (fun n => ∫ z, circleAnnularDensity x r n z • h z) atTop
      (𝓝 (Real.circleAverage h x (Real.exp (-r)))) := by
  simp_rw [integral_circleAnnularDensity_smul x r _ h hh]
  have ht := tendsto_integral_annular_smul (fun z => h (Real.exp (-r) • z+x)) (by fun_prop) (fun z => hb _)
  rw [circleAverage_affine_unit_vector] at ht
  exact ht

/-- Common-support scalar smoothing preserves Banach-norm circle convergence. -/
theorem tendsto_integral_testFn_smul_of_circleAnnular_approx
    (x : ℂ) (r : ℝ) (f : ℕ → TestFn) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R) (hs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hρs : ∀ n, Function.support (circleAnnularDensity x r n) ⊆ closedBall (0 : ℂ) R)
    (he : ∀ n z, |f n z-circleAnnularDensity x r n z| ≤ ε n)
    (h : ℂ → E) (hh : Continuous h) {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) :
    Tendsto (fun n => ∫ z, f n z • h z) atTop (𝓝 (Real.circleAverage h x (Real.exp (-r)))) := by
  let b : ContDiffBump (0 : ℂ) := ⟨R,R+1,hR,lt_add_one R⟩
  let B := ∫ z, b z*‖h z‖
  have hbi : Integrable (fun z => b z*‖h z‖) :=
    (b.continuous.mul hh.norm).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  have hi n : Integrable (fun z => f n z • h z) :=
    ((f n).continuous.smul hh).integrable_of_hasCompactSupport (f n).hasCompactSupport.smul_right
  have hj n : Integrable (fun z => circleAnnularDensity x r n z • h z) :=
    ((continuous_circleAnnularDensity x r n).smul hh).integrable_of_hasCompactSupport
      (hasCompactSupport_circleAnnularDensity x r n).smul_right
  have hbound n : ‖(∫ z, f n z • h z)-(∫ z, circleAnnularDensity x r n z • h z)‖ ≤ ε n*B := by
    let e : ℂ → ℝ := fun z => f n z-circleAnnularDensity x r n z
    have hes : Function.support e ⊆ closedBall (0 : ℂ) R := by
      intro z hz
      by_contra hnot
      have hf0 : f n z = 0 := by
        by_contra hne
        exact hnot (hs n hne)
      have hρ0 : circleAnnularDensity x r n z = 0 := by
        by_contra hne
        exact hnot (hρs n hne)
      exact hz (by change f n z-circleAnnularDensity x r n z = 0; rw [hf0,hρ0,sub_self])
    have hsub : (∫ z, f n z • h z)-(∫ z, circleAnnularDensity x r n z • h z) = ∫ z, e z • h z := by
      rw [← integral_sub (hi n) (hj n)]
      congr 1
      funext z
      exact (sub_smul (f n z) (circleAnnularDensity x r n z) (h z)).symm
    have hei : Integrable (fun z => e z • h z) := by
      convert (hi n).sub (hj n) using 1
      funext z
      exact sub_smul (f n z) (circleAnnularDensity x r n z) (h z)
    rw [hsub]
    calc
      _ ≤ ∫ z, ‖e z • h z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z, ε n*(b z*‖h z‖) := by
        apply integral_mono_ae hei.norm (hbi.const_mul (ε n))
        apply ae_of_all
        intro z
        dsimp only
        rw [norm_smul,Real.norm_eq_abs,← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (abs_le_bump_of_support hR (hε n) e hes (he n) z) (norm_nonneg _)
      _ = _ := integral_const_mul _ _
  have hzero : Tendsto (fun n => (∫ z, f n z • h z)-(∫ z, circleAnnularDensity x r n z • h z)) atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [sub_zero]
    have ht : Tendsto (fun n => ε n*B) atTop (𝓝 0) := by simpa only [zero_mul] using hεlim.mul_const B
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
      (fun n => norm_nonneg _) hbound
  have ht := hzero.add (tendsto_integral_circleAnnular_smul x r h hh hb)
  simpa only [sub_add_cancel,zero_add] using ht

end Vector
end DOZZ.Proofs
