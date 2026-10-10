/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.FirstPassage
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Reflection and the zero-drift barrier probability

The dyadic restart and capped first-hit reflection are supplied by `FirstPassage`.
This module transports their continuous-path identities to the arbitrary sample
space of `DOZZ.brownian_zeroDrift_barrier_bound`. A countable dense evaluation
embedding supplies almost-everywhere measurability without strengthening the
Brownian hypotheses.

Positive running-maximum levels have no atoms. The reflected endpoint interval is
then evaluated with the centered Gaussian density, scaled by its standard
deviation, in the literal half-normal normalization of the statement.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs
/-- Countably many dense evaluations detect almost-everywhere measurability of continuous paths. -/
theorem aemeasurable_brownianPath_of_eval {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → BrownianPath}
    (hX : ∀ t, AEMeasurable (fun ω => X ω t) P) : AEMeasurable X P := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense (ℝ≥0)
  let _ := hDc.to_subtype
  let E : BrownianPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval (fun t => ContinuousMap.measurable_eval t.1)
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    have he : (fun t : ℝ≥0 => p t) = (fun t : ℝ≥0 => q t) :=
      hDd.denseRange_val.equalizer p.continuous q.continuous hpq
    exact congrFun he
  have hE := hmE.measurableEmbedding hinj
  apply hE.aemeasurable_comp_iff.mp
  exact AEMeasurable.of_eval (fun t => hX t.1)

/-- Pack a sample path into `BrownianPath`, using the zero path off the continuous samples. -/
noncomputable def brownianContinuousPath {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (ω : Ω) : BrownianPath := ContinuousMap.mkD (fun t => B t ω) 0

/-- The packed continuous path agrees at every time on one common almost-everywhere event. -/
theorem brownianContinuousPath_eval_ae {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t, brownianContinuousPath B ω t = B t ω := by
  filter_upwards [hB.cont] with ω hω t
  exact ContinuousMap.mkD_apply_of_continuous hω

/-- No pointwise measurability premise is needed to push an arbitrary Brownian motion onto paths. -/
theorem aemeasurable_brownianContinuousPath {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    AEMeasurable (brownianContinuousPath B) P := by
  apply aemeasurable_brownianPath_of_eval
  intro t
  exact (hB.hasLaw_eval t).aemeasurable.congr
    ((brownianContinuousPath_eval_ae hB).mono (fun ω hω => (hω t).symm))

/-- The actual continuous-path pushforward of an arbitrary Brownian motion is Brownian. -/
theorem brownianContinuousPath_isBrownian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianReal (fun t p => p t) (P.map (brownianContinuousPath B)) := by
  have hm := aemeasurable_brownianContinuousPath hB
  refine ⟨⟨?_⟩,ae_of_all _ (fun p => p.continuous)⟩
  intro I
  have he : (fun ω => I.restrict (fun t => brownianContinuousPath B ω t)) =ᵐ[P]
      (fun ω => I.restrict (fun t => B t ω)) := by
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    exact funext (fun t => hω t.1)
  refine ⟨((Finset.measurable_restrict I).comp
    (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t))).aemeasurable,?_⟩
  have houter : Measurable (fun p : BrownianPath => I.restrict (fun t => p t)) :=
    (Finset.measurable_restrict I).comp
      (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t))
  have hmap := AEMeasurable.map_map_of_aemeasurable (μ := P) houter.aemeasurable hm
  simpa only [Function.comp_def] using hmap.trans ((Measure.map_congr he).trans (hB.hasLaw I).map_eq)
/-- The running-maximum reflection principle on an arbitrary sample space. -/
theorem brownian_runningMaximum_reflection {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (β : ℝ) (hβ : 0 < β) (T : ℝ≥0) (hT : T ≠ 0) :
    P {ω | ∃ u ≤ T, β ≤ B u ω} = 2*P {ω | β < B T ω} := by
  let X := brownianContinuousPath B
  have hm : AEMeasurable X P := aemeasurable_brownianContinuousPath hB
  have hcross : P {ω | ∃ u ≤ T, β ≤ B u ω} = (P.map X) {p | ∃ u ≤ T, β ≤ p u} := by
    rw [Measure.map_apply_of_aemeasurable hm
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
        (measurableSet_brownianPath_crossing T β))]
    apply measure_congr
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    apply propext
    simp only [mem_ofPred_eq,mem_preimage,X,hω]
  have hterm : (P.map X) {p | β < p T} = P {ω | β < B T ω} := by
    rw [Measure.map_apply_of_aemeasurable hm
      (measurableSet_lt measurable_const (ContinuousMap.measurable_eval T))]
    apply measure_congr
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    simp only [mem_ofPred_eq,mem_preimage,X,hω]
  rw [hcross,brownianPath_runningMaximum_reflection _ (brownianContinuousPath_isBrownian hB) β hβ T hT,hterm]
/-- Positive reciprocal offsets exhaust a strict real inequality. -/
theorem lt_iff_exists_reciprocal_offset (a b : ℝ) :
    a < b ↔ ∃ n : ℕ, a+1/((n : ℝ)+1) ≤ b := by
  constructor
  · intro h
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
    exact ⟨n,by linarith⟩
  · rintro ⟨n,hn⟩
    have hp : 0 < 1/((n : ℝ)+1) := by positivity
    linarith

/-- Reciprocal positive offsets decrease with their integer index. -/
theorem antitone_reciprocal_offset : Antitone (fun n : ℕ => (1 : ℝ)/((n : ℝ)+1)) := by
  intro n m hnm
  apply one_div_le_one_div_of_le
  · positivity
  · exact_mod_cast Nat.add_le_add_right hnm 1

/-- The strict crossing version of the continuous-path running-maximum reflection principle. -/
theorem brownianPath_strict_runningMaximum_reflection (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∃ u ≤ T, β < p u} = 2*P {p | β < p T} := by
  let b : ℕ → ℝ := fun n => β+1/((n : ℝ)+1)
  have hcross : {p : BrownianPath | ∃ u ≤ T, β < p u} =
      ⋃ n, {p | ∃ u ≤ T, b n ≤ p u} := by
    ext p
    simp only [mem_ofPred_eq,mem_iUnion]
    constructor
    · rintro ⟨u,hu,hβu⟩
      obtain ⟨n,hn⟩ := (lt_iff_exists_reciprocal_offset β (p u)).mp hβu
      exact ⟨n,u,hu,hn⟩
    · rintro ⟨n,u,hu,hn⟩
      exact ⟨u,hu,(lt_iff_exists_reciprocal_offset β (p u)).mpr ⟨n,hn⟩⟩
  have htail : {p : BrownianPath | β < p T} = ⋃ n, {p | b n < p T} := by
    ext p
    simp only [mem_ofPred_eq,mem_iUnion]
    constructor
    · intro h
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
      exact ⟨n,by dsimp [b]; linarith⟩
    · rintro ⟨n,hn⟩
      have hp : 0 < 1/((n : ℝ)+1) := by positivity
      dsimp [b] at hn
      linarith
  have hb : Antitone b := antitone_const.add antitone_reciprocal_offset
  have hc : Monotone (fun n : ℕ => {p : BrownianPath | ∃ u ≤ T, b n ≤ p u}) := by
    intro n m hnm p
    rintro ⟨u,hu,h⟩
    exact ⟨u,hu,(hb hnm).trans h⟩
  have ht : Monotone (fun n : ℕ => {p : BrownianPath | b n < p T}) := by
    intro n m hnm p h
    exact (hb hnm).trans_lt h
  rw [hcross,hc.measure_iUnion,htail,ht.measure_iUnion,ENNReal.mul_iSup]
  apply iSup_congr
  intro n
  exact brownianPath_runningMaximum_reflection P hB (b n) (by dsimp [b]; positivity) T hT

/-- The continuous-path barrier probability is the complement of twice a Gaussian upper tail. -/
theorem brownianPath_barrier_probability_tail (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} = 1-2*P {p | β < p T} := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have he : {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} =
      {p : BrownianPath | ∃ u ≤ T, β < p u}ᶜ := by
    ext p
    simp only [mem_ofPred_eq,mem_compl_iff,not_exists,not_and,not_lt]
  rw [he,measure_compl
    ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
      (measurableSet_brownianPath_strict_crossing T β)) (measure_ne_top _ _),
    measure_univ,brownianPath_strict_runningMaximum_reflection P hB β hβ T hT]
/-- Centered continuous-path Brownian laws exchange the two terminal outer tails. -/
theorem brownianPath_terminal_tail_symmetry (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (T : ℝ≥0) :
    P {p | p T < -β} = P {p | β < p T} := by
  have hs := measurableSet_lt (ContinuousMap.measurable_eval T) (measurable_const (a := -β))
  have he := Measure.map_apply (μ := P) measurable_neg hs
  rw [brownianPath_neg_map P hB] at he
  simpa only [preimage,mem_ofPred_eq,ContinuousMap.neg_apply,neg_lt_neg_iff] using he

/-- The barrier probability equals the probability that the terminal normal lies in a symmetric interval. -/
theorem brownianPath_barrier_probability_interval (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} = P {p | p T ∈ Icc (-β) β} := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hc : {p : BrownianPath | p T ∈ Icc (-β) β} =
      ({p | p T < -β} ∪ {p | β < p T})ᶜ := by
    ext p
    simp only [mem_ofPred_eq,mem_Icc,mem_compl_iff,mem_union,not_or,not_lt]
  have hd : Disjoint {p : BrownianPath | p T < -β} {p | β < p T} := by
    apply disjoint_left.mpr
    intro p hl hu
    have hh : β < -β := hu.trans hl
    linarith
  rw [hc,measure_compl
    ((measurableSet_lt (ContinuousMap.measurable_eval T) measurable_const).union
      (measurableSet_lt measurable_const (ContinuousMap.measurable_eval T))) (measure_ne_top _ _),
    measure_univ,measure_union hd (measurableSet_lt measurable_const (ContinuousMap.measurable_eval T)),
    brownianPath_terminal_tail_symmetry P hB β T,← two_mul]
  exact brownianPath_barrier_probability_tail P hB β hβ T hT

/-- Transport the barrier probability to the centered Gaussian endpoint law without extra hypotheses. -/
theorem brownian_barrier_probability_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (β : ℝ) (hβ : 0 < β) (T : ℝ≥0) (hT : T ≠ 0) :
    P {ω | ∀ u : ℝ≥0, u ≤ T → B u ω ≤ β} = gaussianReal 0 T (Icc (-β) β) := by
  let X := brownianContinuousPath B
  have hm : AEMeasurable X P := aemeasurable_brownianContinuousPath hB
  have hcross : P {ω | ∀ u : ℝ≥0, u ≤ T → B u ω ≤ β} =
      (P.map X) {p | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} := by
    rw [Measure.map_apply_of_aemeasurable hm
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
        (measurableSet_brownianPath_barrier T β))]
    apply measure_congr
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    apply propext
    simp only [mem_ofPred_eq,mem_preimage,X,hω]
  rw [hcross,brownianPath_barrier_probability_interval _ (brownianContinuousPath_isBrownian hB) β hβ T hT]
  exact ((brownianContinuousPath_isBrownian hB).hasLaw_eval T).measure_eq measurableSet_Icc
/-- The normalization from the two half-normal integrals equals the coefficient of
`DOZZ.brownian_zeroDrift_barrier_bound`. -/
theorem brownian_gaussian_normalization :
    2*(Real.sqrt (2*Real.pi))⁻¹ = Real.sqrt (2/Real.pi) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2),Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  have hp : Real.sqrt Real.pi ≠ 0 := by positivity
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The centered standard Gaussian mass of a symmetric interval is the half-normal integral. -/
theorem gaussianReal_symmetric_interval (a : ℝ) (ha : 0 ≤ a) :
    gaussianReal 0 1 (Icc (-a) a) =
      ENNReal.ofReal (Real.sqrt (2/Real.pi)*∫ x in Icc (0 : ℝ) a, Real.exp (-x^2/2)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-x^2/2)
  have hf : Continuous f := by fun_prop
  have heven : (∫ x in (-a)..0, f x) = ∫ x in (0 : ℝ)..a, f x := by
    have he := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := a)
    simpa only [f,neg_sq,neg_zero] using he.symm
  have hi : (∫ x in Icc (-a) a, f x) = 2*∫ x in Icc (0 : ℝ) a, f x := by
    rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith : -a ≤ a),
      ← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable (-a) 0)
        (hf.intervalIntegrable 0 a),heven,two_mul,
      integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le ha]
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he : gaussianPDFReal 0 1 = fun x => (Real.sqrt (2*Real.pi))⁻¹*f x := by
    funext x
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,f]
  rw [he,integral_const_mul,hi]
  congr 1
  rw [← mul_assoc,mul_comm _ 2,brownian_gaussian_normalization]

/-- Scaling by the standard deviation converts a centered Gaussian interval to variance one. -/
theorem gaussianReal_interval_scale (T : ℝ≥0) (hT : T ≠ 0) (β : ℝ) :
    gaussianReal 0 T (Icc (-β) β) =
      gaussianReal 0 1 (Icc (-(β/Real.sqrt T)) (β/Real.sqrt T)) := by
  have hTp : 0 < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hs : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hTp
  have hv : (NNReal.mk ((Real.sqrt (T : ℝ))^2) (sq_nonneg _) : ℝ≥0) = T := by
    apply NNReal.eq_iff.mpr
    exact Real.sq_sqrt T.coe_nonneg
  have he := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt (T : ℝ))
  simp only [mul_zero,mul_one,hv] at he
  rw [← he,Measure.map_apply (show Measurable (fun x : ℝ => Real.sqrt (T : ℝ)*x) from measurable_const.mul measurable_id) measurableSet_Icc]
  congr 1
  ext x
  simp only [mem_preimage,mem_Icc]
  rw [mul_comm (Real.sqrt (T : ℝ)) x,← div_le_iff₀ hs,← le_div_iff₀ hs,neg_div]

/-- The normal interval probability in the integral normalization of
`DOZZ.brownian_zeroDrift_barrier_bound`. -/
theorem gaussianReal_barrier_integral (T : ℝ≥0) (hT : T ≠ 0) (β : ℝ) (hβ : 0 ≤ β) :
    gaussianReal 0 T (Icc (-β) β) =
      ENNReal.ofReal (Real.sqrt (2/Real.pi)*
        ∫ x in Icc (0 : ℝ) (β/Real.sqrt T), Real.exp (-x^2/2)) := by
  rw [gaussianReal_interval_scale T hT β]
  exact gaussianReal_symmetric_interval _ (div_nonneg hβ (Real.sqrt_nonneg _))

/-- The standard half-normal integral is bounded by the interval length. -/
theorem integral_halfGaussian_le (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in Icc (0 : ℝ) a, Real.exp (-x^2/2)) ≤ a := by
  have hf : Continuous (fun x : ℝ => Real.exp (-x^2/2)) := by fun_prop
  calc
    _ ≤ ∫ x in Icc (0 : ℝ) a, (1 : ℝ) := by
      apply setIntegral_mono_on (hf.integrableOn_Icc) (integrableOn_const (measure_Icc_lt_top (μ := volume) (a := (0 : ℝ)) (b := a)).ne) measurableSet_Icc
      intro x hx
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg x)) (by norm_num)
    _ = a := by simp [ha]
/-- The running maximum has no positive atom; the closed and open reflection tails agree. -/
theorem brownianPath_runningMaximum_atom_zero (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | (⨆ u : Iic T, p u) = β} = 0 := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let M : BrownianPath → ℝ := fun p => ⨆ u : Iic T, p u
  have hm : Measurable M :=
    (measurable_brownianPath_runningMaximum T).mono
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T) le_rfl
  have hge : {p : BrownianPath | β ≤ M p} = {p | ∃ u ≤ T, β ≤ p u} := by
    ext p
    constructor
    · intro h
      obtain ⟨u,hu⟩ := brownianPath_runningMaximum_attained p T
      exact ⟨u.1,u.2,hu ▸ h⟩
    · rintro ⟨u,hu,h⟩
      exact h.trans (le_ciSup (brownianPath_Iic_bddAbove p T) ⟨u,hu⟩)
  have hgt : {p : BrownianPath | β < M p} = {p | ∃ u ≤ T, β < p u} := by
    ext p
    exact brownianPath_runningMaximum_gt_iff p T β
  have he : P {p | β ≤ M p} = P {p | β < M p} := by
    rw [hge,hgt,brownianPath_runningMaximum_reflection P hB β hβ T hT,
      brownianPath_strict_runningMaximum_reflection P hB β hβ T hT]
  have hd : {p : BrownianPath | M p = β} = {p | β ≤ M p} \ {p | β < M p} := by
    ext p
    simp only [Set.mem_sdiff,mem_ofPred_eq,not_lt]
    exact ⟨fun h => ⟨h.ge,h.le⟩,fun h => le_antisymm h.2 h.1⟩
  have hsub : {p : BrownianPath | β < M p} ⊆ {p | β ≤ M p} := by
    intro p h
    change β ≤ M p
    change β < M p at h
    exact h.le
  rw [hd,measure_sdiff hsub (measurableSet_lt measurable_const hm).nullMeasurableSet
    (measure_ne_top _ _),he,tsub_self]



/-- Proof of `DOZZ.brownian_zeroDrift_barrier_bound`. -/
theorem brownian_zeroDrift_barrier_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (β t : ℝ)
    (hβ : 0 < β) (ht : 0 < t) :
    P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω ≤ β} =
        ENNReal.ofReal (Real.sqrt (2 / Real.pi) *
          ∫ u in Set.Icc (0 : ℝ) (β / Real.sqrt t), Real.exp (-u ^ 2 / 2)) ∧
      P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω ≤ β} ≤
        ENNReal.ofReal (Real.sqrt (2 / Real.pi) * β / Real.sqrt t) := by
  let T : ℝ≥0 := ⟨t,ht.le⟩
  have hT : T ≠ 0 := by
    intro he
    have ht0 : t = 0 := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    exact ht.ne' ht0
  have htime (u : ℝ≥0) : (u : ℝ) ≤ t ↔ u ≤ T := Iff.rfl
  have hevent : {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω ≤ β} =
      {ω | ∀ u : ℝ≥0, u ≤ T → B u ω ≤ β} := by
    ext ω
    simp only [mem_ofPred_eq,htime]
  have he : P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ t → B u ω ≤ β} =
      ENNReal.ofReal (Real.sqrt (2/Real.pi)*
        ∫ x in Icc (0 : ℝ) (β/Real.sqrt t), Real.exp (-x^2/2)) := by
    rw [hevent,brownian_barrier_probability_gaussian hB β hβ T hT]
    exact gaussianReal_barrier_integral T hT β hβ.le
  refine ⟨he,?_⟩
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt (2/Real.pi)*(β/Real.sqrt t) :=
      mul_le_mul_of_nonneg_left (integral_halfGaussian_le _ (by positivity)) (Real.sqrt_nonneg _)
    _ = _ := by ring
end DOZZ.Proofs
