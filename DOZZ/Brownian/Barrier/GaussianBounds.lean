/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.ZeroDrift
public import DOZZ.Statements.Brownian.BrownianPiecewiseDrift

/-!
# Gaussian endpoint estimates and drifted maximum upper bounds

Independent Gaussian increments give the exponential moment of any weighted
pair of ordered Brownian values. Applying this moment to the kink and terminal
constraints proves both piecewise-drift bounds directly.

A capped hit of a drifted continuous path is a genuine stopping time of the raw
Brownian history. Bounded optional stopping then bounds its crossing probability;
countable horizon exhaustion gives the sharp all-time exponential upper bound.
That bound is also valid at level zero and on arbitrary Brownian sample spaces.
The matching lower bound required by the maximum-tail estimate remains separate.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs
/-- A Brownian increment after a deterministic time is independent of the value at that time. -/
theorem brownian_increment_indep_value {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) (s d : ℝ≥0) :
    IndepFun (fun ω => B (s+d) ω-B s ω) (B s) P := by
  exact (hB.indepFun_shift s).comp (measurable_pi_apply d)
    (measurable_pi_apply (⟨s,le_rfl⟩ : Iic s))

/-- Every linear combination of a Brownian value and a later independent increment has its Gaussian law. -/
theorem brownian_twoTime_linear_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s d : ℝ≥0) (a b : ℝ) :
    HasLaw (fun ω => a*B s ω+b*(B (s+d) ω-B s ω))
      (gaussianReal 0 (NNReal.mk (a^2) (sq_nonneg _)*s+NNReal.mk (b^2) (sq_nonneg _)*d)) P := by
  have hi : IndepFun (fun ω => a*B s ω) (fun ω => b*(B (s+d) ω-B s ω)) P := by
    simpa only [Function.comp_def] using
      (brownian_increment_indep_value hB s d).symm.comp
        (φ := fun x : ℝ => a*x) (ψ := fun x : ℝ => b*x) (by fun_prop) (by fun_prop)
  have hx := gaussianReal_const_mul (hB.hasLaw_eval s) a
  have hy := gaussianReal_const_mul ((hB.shift s).hasLaw_eval d) b
  simp only [mul_zero] at hx hy
  refine ⟨hx.aemeasurable.add hy.aemeasurable,?_⟩
  have he := gaussianReal_add_gaussianReal_of_indepFun hi hx hy
  simpa only [Pi.add_def,Pi.add_apply,zero_add] using he

/-- The two-time Gaussian exponential has a literal quadratic variance. -/
theorem brownian_twoTime_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s d : ℝ≥0) (a b : ℝ) :
    (∫ ω, Real.exp (a*B s ω+b*(B (s+d) ω-B s ω)) ∂P) =
      Real.exp ((a^2*(s : ℝ)+b^2*(d : ℝ))/2) := by
  have he := mgf_gaussianReal (brownian_twoTime_linear_hasLaw hB s d a b) 1
  simpa only [mgf,one_mul,one_pow,mul_one,zero_mul,zero_add,
    NNReal.coe_add,NNReal.coe_mul,NNReal.coe_mk] using he

/-- Two-time exponential tests of a Brownian motion are genuinely integrable. -/
theorem brownian_twoTime_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s d : ℝ≥0) (a b : ℝ) :
    Integrable (fun ω => Real.exp (a*B s ω+b*(B (s+d) ω-B s ω))) P := by
  have hi := (brownian_twoTime_linear_hasLaw hB s d a b).integrable_comp
    (integrable_exp_mul_gaussianReal (μ := 0)
      (v := NNReal.mk (a^2) (sq_nonneg _)*s+NNReal.mk (b^2) (sq_nonneg _)*d) 1)
  simpa only [one_mul,Function.comp_def] using hi

/-- A measurable exponential test bounds any event on which its exponent has a lower bound. -/
theorem brownian_exp_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X : Ω → ℝ} (hX : Integrable (fun ω => Real.exp (X ω)) P)
    (A : Set Ω) (c : ℝ) (hA : ∀ ω ∈ A, c ≤ X ω) :
    P A ≤ ENNReal.ofReal (Real.exp (-c)*(∫ ω, Real.exp (X ω) ∂P)) := by
  have hs : A ⊆ {ω | c ≤ X ω} := hA
  have htail := measure_ge_le_exp_mul_mgf (μ := P) (X := X) (t := 1) c (by norm_num)
    (by simpa only [one_mul] using hX)
  calc
    P A ≤ P {ω | c ≤ X ω} := measure_mono hs
    _ = ENNReal.ofReal (P.real {ω | c ≤ X ω}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [mgf,one_mul,neg_mul] using htail
/-- The exponential moment of a weighted value at two ordered times. -/
theorem brownian_weighted_twoTime_exp_integral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s r : ℝ≥0) (hsr : s ≤ r) (a b : ℝ) :
    (∫ ω, Real.exp (a*B s ω+b*B r ω) ∂P) =
      Real.exp (((a+b)^2*(s : ℝ)+b^2*((r : ℝ)-(s : ℝ)))/2) := by
  have he (ω : Ω) : a*B s ω+b*B r ω =
      (a+b)*B s ω+b*(B (s+(r-s)) ω-B s ω) := by
    rw [add_tsub_cancel_of_le hsr]
    ring
  simp_rw [he]
  rw [brownian_twoTime_exp_integral hB s (r-s) (a+b) b,NNReal.coe_sub hsr]

/-- Integrability of the weighted two-time exponential. -/
theorem brownian_weighted_twoTime_exp_integrable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s r : ℝ≥0) (hsr : s ≤ r) (a b : ℝ) :
    Integrable (fun ω => Real.exp (a*B s ω+b*B r ω)) P := by
  have he : (fun ω => Real.exp (a*B s ω+b*B r ω)) =
      (fun ω => Real.exp ((a+b)*B s ω+b*(B (s+(r-s)) ω-B s ω))) := by
    funext ω
    rw [add_tsub_cancel_of_le hsr]
    congr 1
    ring
  rw [he]
  exact brownian_twoTime_exp_integrable hB s (r-s) (a+b) b

/-- Endpoint Chernoff bound for any event with a weighted two-time upper constraint. -/
theorem brownian_weighted_twoTime_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (s r : ℝ≥0) (hsr : s ≤ r) (a b c : ℝ) (A : Set Ω)
    (hA : ∀ ω ∈ A, a*B s ω+b*B r ω ≤ c) :
    P A ≤ ENNReal.ofReal (Real.exp (c+((a+b)^2*(s : ℝ)+b^2*((r : ℝ)-(s : ℝ)))/2)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have he := brownian_exp_event_bound
    (brownian_weighted_twoTime_exp_integrable hB s r hsr (-a) (-b)) A (-c)
    (fun ω hω => by have h := hA ω hω; linarith)
  rw [brownian_weighted_twoTime_exp_integral hB s r hsr (-a) (-b),← Real.exp_add] at he
  convert he using 1
  congr 2
  ring

/-- An endpoint alone gives the constant-drift Gaussian Chernoff estimate. -/
theorem brownian_terminal_event_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (r : ℝ≥0) (a c : ℝ) (A : Set Ω) (hA : ∀ ω ∈ A, a*B r ω ≤ c) :
    P A ≤ ENNReal.ofReal (Real.exp (c+a^2*(r : ℝ)/2)) := by
  have he := brownian_weighted_twoTime_event_bound hB 0 r (zero_le) 0 a c A
    (by simpa only [zero_mul,zero_add] using hA)
  simpa only [zero_add,NNReal.coe_zero,mul_zero,sub_zero,zero_div] using he
/-- Proof of `DOZZ.brownian_piecewiseDrift_barrier_bound`. -/
theorem brownian_piecewiseDrift_barrier_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (α αtilde β s r : ℝ)
    (hβ : 0 ≤ β) (hs : 0 ≤ s) (hsr : s ≤ r) (hα : 0 ≤ α) :
    ((0 ≤ αtilde) →
      P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ r →
        B u ω + brownianPiecewiseDrift α αtilde s (u : ℝ) ≤ β} ≤
        ENNReal.ofReal (Real.exp
          (-((α + αtilde) ^ 2) * s / 2 - α ^ 2 * (r - s) / 2 +
            (α + αtilde) * β))) ∧
    ((αtilde ≤ 0) →
      P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ r →
        B u ω + brownianPiecewiseDrift α αtilde s (u : ℝ) ≤ β} ≤
        ENNReal.ofReal (Real.exp
          (-(((α + αtilde) ^ 2 - α ^ 2 - αtilde ^ 2) * s) / 2 -
            α ^ 2 * r / 2 + α * β))) := by
  let βnn : ℝ≥0 := NNReal.mk β hβ
  let S : ℝ≥0 := NNReal.mk s hs
  let R : ℝ≥0 := NNReal.mk r (hs.trans hsr)
  have hSR : S ≤ R := hsr
  let A : Set Ω := {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ r →
    B u ω+brownianPiecewiseDrift α αtilde s (u : ℝ) ≤ β}
  have hS (ω : Ω) (hω : ω ∈ A) : B S ω+(α+αtilde)*s ≤ β := by
    have he := hω S hsr
    simpa only [S,NNReal.coe_mk,brownianPiecewiseDrift,min_self,add_mul] using he
  have hR (ω : Ω) (hω : ω ∈ A) : B R ω+α*r+αtilde*s ≤ β := by
    have he := hω R le_rfl
    simpa only [R,NNReal.coe_mk,brownianPiecewiseDrift,min_eq_right hsr,add_assoc] using he
  constructor
  · intro htilde
    let V : ℝ := (α+αtilde)^2*s+α^2*(r-s)
    have he := brownian_weighted_twoTime_event_bound hB.toIsPreBrownianReal S R hSR
      αtilde α ((α+αtilde)*(βnn : ℝ)-V) A (fun ω hω => by
        have hx := mul_le_mul_of_nonneg_left (hS ω hω) htilde
        have hy := mul_le_mul_of_nonneg_left (hR ω hω) hα
        simp only [βnn,NNReal.coe_mk,V]
        nlinarith)
    convert he using 1
    congr 2
    simp only [V,S,R,βnn,NNReal.coe_mk]
    ring
  · intro _htilde
    have he := brownian_terminal_event_bound hB.toIsPreBrownianReal R α
      (α*(βnn : ℝ)-α^2*r-α*αtilde*s) A (fun ω hω => by
        have hx := mul_le_mul_of_nonneg_left (hR ω hω) hα
        simp only [βnn,NNReal.coe_mk]
        nlinarith)
    convert he using 1
    congr 2
    simp only [R,βnn,NNReal.coe_mk]
    ring
/-! ## Drift translation and capped stopping times -/

/-- Add a deterministic linear drift to a literal continuous Brownian path. -/
noncomputable def brownianDriftPath (δ : ℝ) (p : BrownianPath) : BrownianPath :=
  ⟨fun t => p t+δ*(t : ℝ),p.continuous.add (continuous_const.mul NNReal.continuous_coe)⟩

/-- Drift translation is jointly continuous in the path and in its scalar drift. -/
theorem continuous_brownianDriftPath :
    Continuous (fun z : ℝ × BrownianPath => brownianDriftPath z.1 z.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ × BrownianPath) × ℝ≥0 => z.1.2 z.2+z.1.1*(z.2 : ℝ))
  exact (continuous_eval.comp (continuous_fst.snd.prodMk continuous_snd)).add
    (continuous_fst.fst.mul (NNReal.continuous_coe.comp continuous_snd))

/-- Deterministic drift translation preserves measurability in each raw history sigma algebra. -/
theorem measurable_brownianDriftPath_history (δ : ℝ) (s : ℝ≥0) :
    Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s,
      brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s] (brownianDriftPath δ) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (brownianDriftPath δ)
    (⨆ t : ℝ≥0, ⨆ (_ : t ≤ s), MeasurableSpace.comap (fun p : BrownianPath => p t) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro t
  rw [MeasurableSpace.comap_iSup]
  apply iSup_le
  intro ht
  rw [MeasurableSpace.comap_comp]
  have hm : Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s] (fun p : BrownianPath => p t) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
  exact (hm.add_const (δ*(t : ℝ))).comap_le

/-- The capped hit of a linearly drifted path is a genuine raw Brownian stopping time. -/
theorem cappedBrownianDriftFirstPassage_isStoppingTime (δ β : ℝ) (T : ℝ≥0) :
    IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t))
      (fun p => (cappedBrownianFirstPassage β T (brownianDriftPath δ p) : WithTop ℝ≥0)) := by
  intro s
  exact (cappedBrownianFirstPassage_isStoppingTime β T s).preimage
    (measurable_brownianDriftPath_history δ s)

/-- A bounded hit by the negative-drift path has the exponential-martingale upper tail bound. -/
theorem brownianPath_negativeDrift_cappedHit_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) :
    P {p | cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p) < T} ≤
      ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let τ : BrownianPath → ℝ≥0 :=
    fun p => cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p)
  have hτ := cappedBrownianDriftFirstPassage_isStoppingTime (-ν) x T
  have hτT : ∀ p, τ p ≤ T := fun p => cappedBrownianFirstPassage_le x T _
  have he := brownian_exponential_bounded_optional_stopping hB
    (fun t => ContinuousMap.measurable_eval t) (2*ν) T τ hτ hτT
  have hi := integrable_of_integral_eq_one he
  let A : Set BrownianPath := {p | τ p < T ∧ p 0 = 0}
  have hc : ∀ p ∈ A, 2*ν*x ≤ (2*ν)*p (τ p)-(2*ν)^2*((τ p : ℝ))/2 := by
    intro p hp
    have h0 : brownianDriftPath (-ν) p 0 < x := by
      change p 0+(-ν)*(0 : ℝ) < x
      simpa only [mul_zero,add_zero,hp.2] using hx
    have hv := cappedBrownianFirstPassage_value x T (brownianDriftPath (-ν) p) h0 hp.1
    change p (τ p)+(-ν)*(τ p : ℝ) = x at hv
    have hval : (2*ν)*p (τ p)-(2*ν)^2*(τ p : ℝ)/2 = 2*ν*x := by
      rw [← hv]
      ring
    exact hval.ge
  have hb := brownian_exp_event_bound hi A (2*ν*x) hc
  rw [he,mul_one] at hb
  have hA : {p : BrownianPath | τ p < T} =ᵐ[P] A := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    apply propext
    simp only [A,mem_ofPred_eq,hp,and_true]
  rw [measure_congr hA]
  convert hb using 1
  congr 2
  ring
/-! ## Exhaustion to the entire-time maximum -/

/-- A strict crossing at any earlier time forces the capped first hit before the terminal horizon. -/
theorem cappedBrownianFirstPassage_lt_of_strict_crossing (x : ℝ) (T : ℝ≥0)
    (p : BrownianPath) (h0 : p 0 < x) (u : ℝ≥0) (hu : u ≤ T) (hx : x < p u) :
    cappedBrownianFirstPassage x T p < T := by
  obtain ⟨v,hv,hpv⟩ := intermediate_value_Icc (a := (0 : ℝ≥0)) (b := u)
    (f := fun t : ℝ≥0 => p t) zero_le p.continuous.continuousOn ⟨h0.le,hx.le⟩
  have hvu : v < u := lt_of_le_of_ne hv.2 (by intro he; exact hx.ne (he ▸ hpv).symm)
  have hτv : cappedBrownianFirstPassage x T p ≤ v :=
    csInf_le (s := {t : ℝ≥0 | t ≤ T ∧ x ≤ p t} ∪ {T}) (OrderBot.bddBelow _)
      (Or.inl ⟨hv.2.trans hu,hpv ▸ le_rfl⟩)
  exact (hτv.trans_lt hvu).trans_le hu

/-- Every finite-horizon strict crossing of a negative-drift path obeys the exponential upper bound. -/
theorem brownianPath_negativeDrift_finiteMaximum_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hx : 0 < x)
    (T : ℝ≥0) :
    P {p | ∃ u ≤ T, x < p u-ν*(u : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  have hsub : {p : BrownianPath | ∃ u ≤ T, x < p u-ν*(u : ℝ)} ≤ᵐ[P]
      {p | cappedBrownianFirstPassage x T (brownianDriftPath (-ν) p) < T} := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    rintro ⟨u,hu,hxu⟩
    have h0 : brownianDriftPath (-ν) p 0 < x := by
      change p 0+(-ν)*(0 : ℝ) < x
      simpa only [mul_zero,add_zero,hp] using hx
    apply cappedBrownianFirstPassage_lt_of_strict_crossing x T (brownianDriftPath (-ν) p) h0 u hu
    change x < p u+(-ν)*(u : ℝ)
    simpa only [sub_eq_add_neg,neg_mul] using hxu
  exact (measure_mono_ae hsub).trans
    (brownianPath_negativeDrift_cappedHit_le P hB ν x hx T)

/-- Finite-horizon crossing events for a drifted continuous path are measurable. -/
theorem measurableSet_brownianPath_drift_strict_crossing (δ x : ℝ) (T : ℝ≥0) :
    MeasurableSet {p : BrownianPath | ∃ u ≤ T, x < p u+δ*(u : ℝ)} := by
  have hm : Measurable (brownianDriftPath δ) :=
    continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hS := (brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
    (measurableSet_brownianPath_strict_crossing T x)
  exact hS.preimage hm

/-- The entire-time crossing event is a countable increasing union of finite-horizon crossings. -/
theorem brownianPath_drift_crossing_eq_iUnion (δ x : ℝ) :
    {p : BrownianPath | ∃ t : ℝ≥0, x < p t+δ*(t : ℝ)} =
      ⋃ n : ℕ, {p | ∃ t ≤ (n : ℝ≥0), x < p t+δ*(t : ℝ)} := by
  ext p
  simp only [mem_ofPred_eq,mem_iUnion]
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨n,hn⟩ := exists_nat_ge (t : ℝ)
    exact ⟨n,t,by exact_mod_cast hn,ht⟩
  · rintro ⟨n,t,_,ht⟩
    exact ⟨t,ht⟩

/-- Infinite-horizon drift crossing events are measurable on the continuous-path carrier. -/
theorem measurableSet_brownianPath_drift_crossing (δ x : ℝ) :
    MeasurableSet {p : BrownianPath | ∃ t : ℝ≥0, x < p t+δ*(t : ℝ)} := by
  rw [brownianPath_drift_crossing_eq_iUnion]
  exact MeasurableSet.iUnion (fun n => measurableSet_brownianPath_drift_strict_crossing δ x n)

/-- The all-time maximum of a negative-drift continuous Brownian path satisfies the sharp exponential upper bound. -/
theorem brownianPath_negativeDrift_maximum_le (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P)
    (ν x : ℝ) (hx : 0 < x) :
    P {p | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  have hset : {p : BrownianPath | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} =
      ⋃ n : ℕ, {p | ∃ t ≤ (n : ℝ≥0), x < p t-ν*(t : ℝ)} := by
    simpa only [sub_eq_add_neg,neg_mul] using brownianPath_drift_crossing_eq_iUnion (-ν) x
  have hmono : Monotone (fun n : ℕ => {p : BrownianPath | ∃ t ≤ (n : ℝ≥0), x < p t-ν*(t : ℝ)}) := by
    intro n m hnm p
    rintro ⟨t,ht,hx⟩
    exact ⟨t,ht.trans (Nat.cast_le.mpr hnm),hx⟩
  rw [hset,hmono.measure_iUnion]
  exact iSup_le (fun n => brownianPath_negativeDrift_finiteMaximum_le P hB ν x hx n)

/-- The sharp negative-drift maximum upper bound on an arbitrary Brownian sample space. -/
theorem negativeDriftBrownian_maximum_tail_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (ν x : ℝ) (hx : 0 < x) :
    P {ω | ∃ t : ℝ≥0, x < B t ω-ν*(t : ℝ)} ≤ ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  let X := brownianContinuousPath B
  have hm : AEMeasurable X P := aemeasurable_brownianContinuousPath hB
  have hS : MeasurableSet {p : BrownianPath | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} := by
    simpa only [sub_eq_add_neg,neg_mul] using measurableSet_brownianPath_drift_crossing (-ν) x
  have he : P {ω | ∃ t : ℝ≥0, x < B t ω-ν*(t : ℝ)} =
      (P.map X) {p | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} := by
    rw [Measure.map_apply_of_aemeasurable hm hS]
    apply measure_congr
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    apply propext
    simp only [mem_ofPred_eq,mem_preimage,X,hω]
  rw [he]
  exact brownianPath_negativeDrift_maximum_le _ (brownianContinuousPath_isBrownian hB) ν x hx
/-- Zero drift translation is the identity on the literal continuous-path carrier. -/
theorem brownianDriftPath_zero (p : BrownianPath) : brownianDriftPath 0 p = p := by
  apply ContinuousMap.ext
  intro t
  change p t+0*(t : ℝ) = p t
  simp only [zero_mul,add_zero]

/-- Deterministic drifts add under composition on actual paths. -/
theorem brownianDriftPath_add (a b : ℝ) (p : BrownianPath) :
    brownianDriftPath a (brownianDriftPath b p) = brownianDriftPath (a+b) p := by
  apply ContinuousMap.ext
  intro t
  change (p t+b*(t : ℝ))+a*(t : ℝ) = p t+(a+b)*(t : ℝ)
  ring




end DOZZ.Proofs
