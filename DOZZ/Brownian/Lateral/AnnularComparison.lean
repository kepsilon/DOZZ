/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.Brownian.Lateral.IntervalMoments
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Probability.Independence.Integration

/-!
# Annular comparison for a given lateral chaos

Removing and reinserting the radial weight compares lateral interval mass with plane annulus
mass. The continuous radial path supplies a measurable compact-window bound. Independence,
already present in the source lateral predicate, factors the comparison at every real moment
order. No change of regularization or construction of a new lateral chaos is used here.
The transfer includes positive orders above one and every inverse order.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The plane annulus corresponding to a logarithmic interval, with the origin excluded. -/
def lateralLogAnnulus (a b : ℝ) : Set ℂ :=
  {x | x ≠ 0 ∧ -Real.log ‖x‖ ∈ Ioc a b}

/-- The annulus is a Borel set even when its interval is empty. -/
theorem measurableSet_lateralLogAnnulus (a b : ℝ) :
    MeasurableSet (lateralLogAnnulus a b) := by
  exact (measurableSet_singleton (0 : ℂ)).compl.inter
    (measurableSet_Ioc.preimage
      (measurable_neg.comp (Real.measurable_log.comp measurable_norm)))

/-- A measurable pathwise bound for the absolute forward radial exponent on a compact window. -/
noncomputable def lateralWindowBound (γ a b : ℝ) (A : TwoSidedPath) : ℝ :=
  |γ| * ‖A.restrict (Icc a b)‖ + |γ * Q γ| * max |a| |b|

/-- Compact-window bounds vary continuously with the full radial path. -/
theorem continuous_lateralWindowBound (γ a b : ℝ) :
    Continuous (lateralWindowBound γ a b) := by
  unfold lateralWindowBound
  exact (continuous_const.mul
    (continuous_norm.comp (ContinuousMap.continuous_restrict _))).add continuous_const

/-- Every compact-window exponent bound is nonnegative. -/
theorem lateralWindowBound_nonneg (γ a b : ℝ) (A : TwoSidedPath) :
    0 ≤ lateralWindowBound γ a b A := by
  unfold lateralWindowBound
  positivity

/-- The compact norm controls every exponent on the specified interval. -/
theorem abs_lateralForwardExponent_le (γ a b : ℝ) (A : TwoSidedPath)
    (s : ℝ) (hs : s ∈ Icc a b) :
    abs (γ * A s - γ * Q γ * |s|) ≤ lateralWindowBound γ a b A := by
  have hA : |A s| ≤ ‖A.restrict (Icc a b)‖ :=
    (A.restrict (Icc a b)).norm_coe_le_norm ⟨s, hs⟩
  have hsabs : |s| ≤ max |a| |b| := by
    apply abs_le.mpr
    constructor
    · exact le_trans (neg_le_neg (le_max_left _ _))
        (le_trans (neg_abs_le a) hs.1)
    · exact le_trans hs.2 (le_trans (le_abs_self b) (le_max_right _ _))
  calc
    _ ≤ |γ * A s| + abs (γ * Q γ * |s|) := abs_sub _ _
    _ = |γ| * |A s| + |γ * Q γ| * |s| := by
      rw [abs_mul, abs_mul, abs_abs]
    _ ≤ lateralWindowBound γ a b A :=
      add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hsabs (abs_nonneg _))

/-- The forward weight lies between positive reciprocal bounds on every compact window. -/
theorem lateralForwardWeight_window_bounds (γ a b : ℝ) (A : TwoSidedPath)
    (s : ℝ) (hs : s ∈ Icc a b) :
    ENNReal.ofReal (Real.exp (-lateralWindowBound γ a b A)) ≤
        lateralForwardWeight γ A s ∧
      lateralForwardWeight γ A s ≤
        ENNReal.ofReal (Real.exp (lateralWindowBound γ a b A)) := by
  have h := abs_le.mp (abs_lateralForwardExponent_le γ a b A s hs)
  exact ⟨ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h.1),
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr h.2)⟩

/-- Reinsertion on an interval is exactly annulus mass; no no-atom hypothesis at zero is needed. -/
theorem lateralProjectedGMC_reinsert_interval (γ a b : ℝ) (A : TwoSidedPath)
    (M : Measure ℂ) :
    (∫⁻ s in Ioc a b, lateralForwardWeight γ A s ∂lateralProjectedGMC γ A M) =
      M (lateralLogAnnulus a b) := by
  rw [← lintegral_indicator measurableSet_Ioc]
  have heq : (Ioc a b).indicator (lateralForwardWeight γ A) =
      fun s => lateralForwardWeight γ A s * (Ioc a b).indicator (fun _ => 1) s := by
    funext s
    by_cases hs : s ∈ Ioc a b <;> simp [hs]
  rw [heq, lateralProjectedGMC_reinsert_lintegral γ A M _
    (measurable_const.indicator measurableSet_Ioc)]
  have hfun : (fun x : ℂ => if x = 0 then (0 : ℝ≥0∞) else
      (Ioc a b).indicator (fun _ => 1) (-Real.log ‖x‖)) =
      (lateralLogAnnulus a b).indicator (fun _ => 1) := by
    funext x
    by_cases hx : x = 0
    · have hm : x ∉ lateralLogAnnulus a b := fun h => h.1 hx
      rw [indicator_of_notMem hm]
      simp only [hx, ite_true]
    · by_cases hs : -Real.log ‖x‖ ∈ Ioc a b
      · have hm : x ∈ lateralLogAnnulus a b := ⟨hx, hs⟩
        simp only [hx, ite_false, indicator_of_mem hs, indicator_of_mem hm]
      · have hm : x ∉ lateralLogAnnulus a b := fun h => hs h.2
        simp only [hx, ite_false, indicator_of_notMem hs, indicator_of_notMem hm]
  rw [hfun, lintegral_indicator (measurableSet_lateralLogAnnulus a b),
    setLIntegral_const, one_mul]

/-- Annulus mass is bounded above and below by the same projected interval mass, with the
measurable radial-window factor. This deterministic identity is valid for every plane measure. -/
theorem lateralProjectedGMC_annular_mass_bounds (γ a b : ℝ) (A : TwoSidedPath)
    (M : Measure ℂ) :
    ENNReal.ofReal (Real.exp (-lateralWindowBound γ a b A)) *
        lateralProjectedGMC γ A M (Ioc a b) ≤ M (lateralLogAnnulus a b) ∧
      M (lateralLogAnnulus a b) ≤
        ENNReal.ofReal (Real.exp (lateralWindowBound γ a b A)) *
          lateralProjectedGMC γ A M (Ioc a b) := by
  rw [← lateralProjectedGMC_reinsert_interval]
  constructor
  · rw [← setLIntegral_const]
    apply setLIntegral_mono' measurableSet_Ioc
    intro s hs
    exact (lateralForwardWeight_window_bounds γ a b A s ⟨hs.1.le, hs.2⟩).1
  · rw [← setLIntegral_const]
    apply setLIntegral_mono' measurableSet_Ioc
    intro s hs
    exact (lateralForwardWeight_window_bounds γ a b A s ⟨hs.1.le, hs.2⟩).2

/-- Exponentiation of a positive finite exponential factor agrees with the real exponential. -/
theorem ennreal_exp_rpow (x q : ℝ) :
    (ENNReal.ofReal (Real.exp x)) ^ q = ENNReal.ofReal (Real.exp (x * q)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]

/-- A reciprocal exponential sandwich yields a moment comparison at every real order,
including negative orders and zero masses. Finite masses avoid the extended zero-times-infinity
exception when distributing a negative power. -/
theorem ennreal_rpow_le_of_exp_sandwich (x y : ℝ≥0∞) (C q : ℝ)
    (hy : y ≠ ⊤)
    (hl : ENNReal.ofReal (Real.exp (-C)) * y ≤ x)
    (hu : x ≤ ENNReal.ofReal (Real.exp C) * y) :
    ENNReal.ofReal (Real.exp (-|q| * C)) * y ^ q ≤ x ^ q := by
  by_cases hq : 0 ≤ q
  · have h := ENNReal.rpow_le_rpow hl hq
    rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hy,
      ennreal_exp_rpow] at h
    rw [abs_of_nonneg hq]
    have he : -C * q = -q * C := by ring
    simpa only [he] using h
  · have hq' : 0 ≤ -q := by linarith
    have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hu hq')
    rw [← ENNReal.rpow_neg, ← ENNReal.rpow_neg, neg_neg,
      ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hy,
      ennreal_exp_rpow] at h
    rw [abs_of_neg (lt_of_not_ge hq)]
    have he : C * q = -(-q) * C := by ring
    simpa only [he] using h

/-- Attenuation used to factor a moment comparison without inverse radial factors. -/
noncomputable def lateralMomentAttenuation (γ a b q : ℝ) (A : TwoSidedPath) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-|q| * lateralWindowBound γ a b A))

/-- The attenuation is measurable on the full continuous-path carrier. -/
theorem measurable_lateralMomentAttenuation (γ a b q : ℝ) :
    Measurable (lateralMomentAttenuation γ a b q) := by
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_lateralWindowBound γ a b).measurable))

/-- The comparison factor is strictly positive and at most one on every path. -/
theorem lateralMomentAttenuation_bounds (γ a b q : ℝ) (A : TwoSidedPath) :
    0 < lateralMomentAttenuation γ a b q A ∧
      lateralMomentAttenuation γ a b q A ≤ 1 := by
  constructor
  · exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  · have he : -|q| * lateralWindowBound γ a b A ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _))
        (lateralWindowBound_nonneg γ a b A)
    exact le_trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr he)) (by simp)

/-- Under any probability law, the mean attenuation is a strictly positive finite factor. -/
theorem lateralMomentAttenuation_mean_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (γ a b q : ℝ)
    (A : Ω → TwoSidedPath) (hA : AEMeasurable A P) :
    0 < (∫⁻ ω, lateralMomentAttenuation γ a b q (A ω) ∂P) ∧
      (∫⁻ ω, lateralMomentAttenuation γ a b q (A ω) ∂P) ≤ 1 := by
  have hm := (measurable_lateralMomentAttenuation γ a b q).comp_aemeasurable hA
  constructor
  · apply pos_iff_ne_zero.mpr
    intro hz
    have hae := (lintegral_eq_zero_iff' hm).mp hz
    obtain ⟨ω, hω⟩ := hae.exists
    exact (ne_of_gt (lateralMomentAttenuation_bounds γ a b q (A ω)).1) hω
  · calc
      _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P :=
        lintegral_mono (fun ω => (lateralMomentAttenuation_bounds γ a b q (A ω)).2)
      _ = 1 := by simp

/-- At every real moment order, actual independent radial removal gives the factored lower
bound by the corresponding plane-annulus moment. -/
theorem lateral_interval_moment_annular_comparison {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ a b q : ℝ) (A : Ω → TwoSidedPath)
    (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hA : AEMeasurable A P) (hZ : AEMeasurable Z P)
    (hInd : IndepFun A Z P)
    (hEq : ∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω))
    (hfinite : ∀ᵐ ω ∂P, Z ω (Ioc a b) < ⊤) :
    (∫⁻ ω, lateralMomentAttenuation γ a b q (A ω) ∂P) *
        (∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P) ≤
      ∫⁻ ω, (M ω (lateralLogAnnulus a b)) ^ q ∂P := by
  let f : TwoSidedPath → ℝ≥0∞ := lateralMomentAttenuation γ a b q
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Ioc a b)) ^ q
  have hf : Measurable f := measurable_lateralMomentAttenuation γ a b q
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Ioc)
  have hi : IndepFun (fun ω => f (A ω)) (fun ω => g (Z ω)) P := hInd.comp hf hg
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hA) (hg.comp_aemeasurable hZ) hi
  change (∫⁻ ω, f (A ω) * g (Z ω) ∂P) =
    (∫⁻ ω, f (A ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) at hprod
  change (∫⁻ ω, f (A ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) ≤ _
  rw [← hprod]
  apply lintegral_mono_ae
  filter_upwards [hEq, hfinite] with ω he hfω
  have hb := lateralProjectedGMC_annular_mass_bounds γ a b (A ω) (M ω)
  rw [← he] at hb
  exact ennreal_rpow_le_of_exp_sandwich _ _ _ _ hfω.ne hb.1 hb.2

/-- Source data already supply independence of the actual radial path and the given lateral
measure. Compatible-cutoff uniqueness is needed to construct source data, not to consume them. -/
theorem sourceLateral_exists_independent_radial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ)
    (Z : Ω → Measure ℝ) (hS : IsSourceLateralProjection P X γ M Z) :
    ∃ A : Ω → TwoSidedPath, AEMeasurable A P ∧ IndepFun A Z P ∧
      (∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω)) := by
  obtain ⟨_, _, A, _, hA, _, _, _, _, _, hInd, he⟩ := hS
  exact ⟨A, hA, hInd.congr (Filter.Eventually.of_forall (fun _ => rfl)) (he.mono (fun _ h => h.symm)), he⟩

/-- A finite plane-annulus moment transfers to the given lateral interval at the same order,
including inverse orders. No positive or negative moment assumption is hidden in the source
predicate. -/
theorem sourceLateral_interval_moment_finite_of_annular {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (γ : ℝ) (M : Ω → Measure ℂ)
    (Z : Ω → Measure ℝ) (hS : IsSourceLateralProjection P X γ M Z)
    (hZ : AEMeasurable Z P) (a b q : ℝ)
    (hMoment : (∫⁻ ω, (M ω (lateralLogAnnulus a b)) ^ q ∂P) < ⊤) :
    (∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P) < ⊤ := by
  let _ := hS.1.1
  obtain ⟨A, hA, hi, he⟩ := sourceLateral_exists_independent_radial P X γ M Z hS
  have hf : ∀ᵐ ω ∂P, Z ω (Ioc a b) < ⊤ := by
    filter_upwards [he] with ω hω
    rw [hω]
    let _ := hS.2.1.1 ω
    exact lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self)
      (lateralProjectedGMC_Icc_ne_top γ (A ω) (M ω) a b)
  have hb := lateral_interval_moment_annular_comparison P γ a b q A M Z hA hZ hi he hf
  have hp := (lateralMomentAttenuation_mean_bounds P γ a b q A hA).1
  exact ENNReal.lt_top_of_mul_ne_top_right (lt_of_le_of_lt hb hMoment).ne hp.ne'


/-- Quantitative division of the annular comparison by any deterministic lower bound for
its mean radial factor. The estimate holds at every real order and retains the source mass. -/
theorem lateral_interval_moment_le_annular_div {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ a b q : ℝ) (A : Ω → TwoSidedPath)
    (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hA : AEMeasurable A P) (hZ : AEMeasurable Z P) (hInd : IndepFun A Z P)
    (hEq : ∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω))
    (hfinite : ∀ᵐ ω ∂P, Z ω (Ioc a b) < ⊤)
    (η : ℝ) (hη : 0 < η)
    (hRadial : ENNReal.ofReal η ≤ ∫⁻ ω, lateralMomentAttenuation γ a b q (A ω) ∂P) :
    (∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P) ≤
      (∫⁻ ω, (M ω (lateralLogAnnulus a b)) ^ q ∂P) / ENNReal.ofReal η := by
  have hb := lateral_interval_moment_annular_comparison P γ a b q A M Z
    hA hZ hInd hEq hfinite
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (ne_of_gt (ENNReal.ofReal_pos.mpr hη)))
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  rw [mul_comm]
  exact le_trans (mul_le_mul' hRadial le_rfl) hb

/-- Uniform plane-annulus bounds and a uniform lower radial factor give uniform lateral
bounds. Stationarity then supplies every translate required by the conclusion of
`DOZZ.lateralGMC_interval_moment_range`. The two quantitative analytic inputs are explicit, so
this theorem does not presume their closure from intensity or local finiteness. -/
theorem lateralGMC_uniform_interval_moments_of_annular_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kq : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (A : ℝ → Ω → TwoSidedPath) (M : ℝ → Ω → Measure ℂ)
    (hA : ∀ γ ∈ Kγ, AEMeasurable (A γ) P)
    (hInd : ∀ γ ∈ Kγ, IndepFun (A γ) (Z γ) P)
    (hEq : ∀ γ ∈ Kγ, ∀ᵐ ω ∂P,
      Z γ ω = lateralProjectedGMC γ (A γ ω) (M γ ω))
    (a b : ℝ) (η : ℝ) (hη : 0 < η) (C : ℝ≥0∞) (hC : C < ⊤)
    (hRadial : ∀ γ ∈ Kγ, ∀ q ∈ Kq,
      ENNReal.ofReal η ≤ ∫⁻ ω, lateralMomentAttenuation γ a b q (A γ ω) ∂P)
    (hAnnular : ∀ γ ∈ Kγ, ∀ q ∈ Kq,
      (∫⁻ ω, (M γ ω (lateralLogAnnulus a b)) ^ q ∂P) ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
      (∫⁻ ω, (Z γ ω (Ioc (a + t) (b + t))) ^ q ∂P) ≤ C' := by
  refine ⟨C / ENNReal.ofReal η,
    ENNReal.div_lt_top hC.ne (ne_of_gt (ENNReal.ofReal_pos.mpr hη)), ?_⟩
  intro γ hγ q hq t
  rw [lateralGMC_interval_moment_translation_eq P γ (Z γ) (hZ γ hγ) a b q t]
  have hf := lateralGMC_interval_mass_finite_ae P γ (Z γ) (hZ γ hγ)
  have hb := lateral_interval_moment_le_annular_div P γ a b q (A γ) (M γ) (Z γ)
    (hA γ hγ) (hZ γ hγ).2.2.2.1 (hInd γ hγ) (hEq γ hγ)
    (hf.mono (fun _ h => h a b)) η hη (hRadial γ hγ q hq)
  exact hb.trans (ENNReal.div_le_div_right (hAnnular γ hγ q hq) _)

/-- The logarithmic annulus is literally a radial norm annulus. In particular its inner
boundary stays away from zero, as required for local GMC moment estimates. -/
theorem mem_lateralLogAnnulus_iff (a b : ℝ) (x : ℂ) :
    x ∈ lateralLogAnnulus a b ↔ Real.exp (-b) ≤ ‖x‖ ∧ ‖x‖ < Real.exp (-a) := by
  constructor
  · rintro ⟨hx, hleft, hright⟩
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    constructor
    · rw [← Real.exp_log hn]
      exact Real.exp_le_exp.mpr (by linarith)
    · rw [← Real.exp_log hn]
      exact Real.exp_lt_exp.mpr (by linarith)
  · rintro ⟨hleft, hright⟩
    have hn : 0 < ‖x‖ := (Real.exp_pos _).trans_le hleft
    refine ⟨norm_ne_zero_iff.mp hn.ne', ?_, ?_⟩
    · have hlog := Real.log_lt_log hn hright
      rw [Real.log_exp] at hlog
      linarith
    · have hlog := Real.log_le_log (Real.exp_pos _) hleft
      rw [Real.log_exp] at hlog
      linarith

/-- The source annulus lies in a fixed ball, independently of the radial witness. -/
theorem lateralLogAnnulus_subset_ball (a b : ℝ) :
    lateralLogAnnulus a b ⊆ Metric.ball (0 : ℂ) (Real.exp (-a)) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right]
  exact ((mem_lateralLogAnnulus_iff a b x).mp hx).2



/-- Radial removal preserves zero mass exactly on every logarithmic interval. -/
theorem lateralProjectedGMC_interval_eq_zero_iff_annulus (γ a b : ℝ)
    (A : TwoSidedPath) (M : Measure ℂ) :
    lateralProjectedGMC γ A M (Ioc a b) = 0 ↔ M (lateralLogAnnulus a b) = 0 := by
  have hb := lateralProjectedGMC_annular_mass_bounds γ a b A M
  constructor
  · intro hz
    rw [hz, mul_zero] at hb
    exact le_antisymm (by simpa only [mul_zero] using hb.2) bot_le
  · intro hz
    rw [hz] at hb
    have he : ENNReal.ofReal (Real.exp (-lateralWindowBound γ a b A)) *
        lateralProjectedGMC γ A M (Ioc a b) = 0 := le_antisymm hb.1 bot_le
    exact (mul_eq_zero.mp he).resolve_left
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))



end DOZZ.Proofs
