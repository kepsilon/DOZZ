/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.BrownianWindowExponential
public import DOZZ.Brownian.Lateral.ReflectionInverse
public import DOZZ.Brownian.Williams.ThinBand

/-!
# Positive blocks under the upper-conditioned Brownian law

The source comparison uses negative-drift Brownian motion conditioned below one. Its actual
normalized whole-path law is already constructed by Williams. Here its unit-block envelopes
are bounded by the truncated endpoint moment and an independent Brownian unit-increment
exponential. The endpoint bound gives summable decay. The resulting envelopes also bound blocks
of any given lateral measure, without splitting its half-lines into independent measures.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- A positive unit-block exponential envelope on the continuous path carrier. -/
noncomputable def positiveBlockEnvelope (γ : ℝ) (n : ℝ≥0) (p : BrownianPath) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * p n + |γ| * brownianUnitNorm (brownianShiftPath n p)))

/-- The envelope is measurable as a function of the actual full path. -/
theorem measurable_positiveBlockEnvelope (γ : ℝ) (n : ℝ≥0) :
    Measurable (positiveBlockEnvelope γ n) := by
  have hs : Measurable (brownianShiftPath n) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_const.mul (ContinuousMap.measurable_eval n)).add
      (measurable_const.mul (continuous_brownianUnitNorm.measurable.comp hs))))

/-- A Brownian value is independent of its entire future increment path. -/
theorem brownianPath_value_indep_shift (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (n : ℝ≥0) :
    IndepFun (fun p : BrownianPath => p n) (brownianShiftPath n) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ℝ≥0)
  let _ := hDc.to_subtype
  let E : BrownianPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval
    (fun t => ContinuousMap.measurable_eval t.1)
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    exact congrFun (hDd.denseRange_val.equalizer p.continuous q.continuous hpq)
  have hEmb := hmE.measurableEmbedding hinj
  let r : (ℝ≥0 → ℝ) → (D → ℝ) := fun p t => p t.1
  have hr : Measurable r := Measurable.of_eval (fun t => measurable_pi_apply t.1)
  have hi := (hB.indepFun_shift n).comp hr
    (measurable_pi_apply (⟨n, le_rfl⟩ : Iic n))
  change IndepFun (E ∘ brownianShiftPath n) (fun p : BrownianPath => p n) P at hi
  rw [IndepFun_iff_Indep, ← MeasurableSpace.comap_comp, hEmb.comap_eq] at hi
  exact ((IndepFun_iff_Indep _ _ P).mpr hi).symm

/-- A negative deterministic drift increases the absolute unit-increment norm by at most its
unit-time magnitude. This estimate is deterministic and does not use an entrance law. -/
theorem brownianUnitNorm_shift_drift_le (ν : ℝ) (hν : 0 ≤ ν)
    (n : ℝ≥0) (p : BrownianPath) :
    brownianUnitNorm (brownianShiftPath n (driftedBrownianPath (-ν) p)) ≤
      brownianUnitNorm (brownianShiftPath n p) + ν := by
  apply (ContinuousMap.norm_le _
    (add_nonneg (brownianUnitNorm_nonneg _) hν)).mpr
  intro t
  have ht : (t.val : ℝ) ≤ 1 := by exact_mod_cast t.property.2
  have he : brownianShiftPath n (driftedBrownianPath (-ν) p) t.val =
      brownianShiftPath n p t.val - ν * (t.val : ℝ) := by
    simp only [brownianShiftPath, driftedBrownianPath, ContinuousMap.coe_mk,
      NNReal.coe_add]
    ring
  change |brownianShiftPath n (driftedBrownianPath (-ν) p) t.val| ≤ _
  rw [he]
  calc
    _ ≤ |brownianShiftPath n p t.val| + |ν * (t.val : ℝ)| := abs_sub _ _
    _ ≤ brownianUnitNorm (brownianShiftPath n p) + ν := by
      rw [abs_of_nonneg (mul_nonneg hν t.val.coe_nonneg)]
      exact add_le_add
        (((brownianShiftPath n p).restrict (Icc 0 (1 : ℝ≥0))).norm_coe_le_norm t)
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht hν)

/-- The raw truncated endpoint and unit-increment exponential factor into their expectations. -/
theorem brownian_truncated_endpoint_increment_factorization
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (n : ℝ≥0) (ν θ : ℝ) :
    (∫⁻ p, {p : BrownianPath | p n - ν * n ≤ 1}.indicator
        (fun p => ENNReal.ofReal (Real.exp (θ * (p n - ν * n)))) p *
          ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath n p))) ∂P) =
      (∫⁻ p in {p | p n - ν * n ≤ 1},
        ENNReal.ofReal (Real.exp (θ * (p n - ν * n))) ∂P) *
          (∫⁻ p, ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p)) ∂P) := by
  let f : ℝ → ℝ≥0∞ := {x : ℝ | x - ν * n ≤ 1}.indicator
    (fun x => ENNReal.ofReal (Real.exp (θ * (x - ν * n))))
  let g : BrownianPath → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (θ * brownianUnitNorm p))
  have hf : Measurable f := by
    apply Measurable.indicator
    · fun_prop
    · exact measurableSet_le (measurable_id.sub measurable_const) measurable_const
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul continuous_brownianUnitNorm.measurable))
  have hs : Measurable (brownianShiftPath n) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hi := (brownianPath_value_indep_shift P hB n).comp hf hg
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hf.comp (ContinuousMap.measurable_eval n)) (hg.comp hs) hi
  change (∫⁻ p, f (p n) * g (brownianShiftPath n p) ∂P) =
    (∫⁻ p, f (p n) ∂P) * (∫⁻ p, g (brownianShiftPath n p) ∂P) at hprod
  have he : (fun p : BrownianPath => f (p n)) =
      {p : BrownianPath | p n - ν * n ≤ 1}.indicator
        (fun p => ENNReal.ofReal (Real.exp (θ * (p n - ν * n)))) := by
    funext p
    rfl
  rw [he, lintegral_indicator
    (show MeasurableSet {p : BrownianPath | p n - ν * n ≤ 1} from
      measurableSet_le ((ContinuousMap.measurable_eval n).sub measurable_const) measurable_const)]
      at hprod
  have hmap := lintegral_map hg hs (μ := P)
  change (∫⁻ p, g p ∂P.map (brownianShiftPath n)) =
    (∫⁻ p, g (brownianShiftPath n p) ∂P) at hmap
  rw [brownianPath_deterministic_shift_map P hB n] at hmap
  rw [← hmap] at hprod
  exact hprod

/-- Normalized upper conditioning yields the actual unit-block envelope bound. -/
theorem upperConditioned_positiveBlockEnvelope_mean_le
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν θ : ℝ) (hν : 0 ≤ ν) (hθ : 0 ≤ θ) (n : ℝ≥0) :
    (∫⁻ p, positiveBlockEnvelope θ n p ∂brownianBelowConditionedLaw P ν 1) ≤
      (ENNReal.ofReal (conditionedH ν 1))⁻¹ * ENNReal.ofReal (Real.exp (θ * ν)) *
        brownianWindowExponentialConstant θ *
          (ENNReal.ofReal (Real.exp (-θ * ν * n / 2)) +
            ENNReal.ofReal (Real.exp (θ - ν ^ 2 * n / 8))) := by
  let E : Set BrownianPath := {p | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < 1}
  have hE : MeasurableSet E := (measurableSet_brownianPath_below 1).preimage
    (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  let F : BrownianPath → ℝ≥0∞ := fun p =>
    {p : BrownianPath | p n - ν * n ≤ 1}.indicator
      (fun p => ENNReal.ofReal (Real.exp (θ * (p n - ν * n)))) p *
        ENNReal.ofReal (Real.exp (θ * brownianUnitNorm (brownianShiftPath n p)))
  have hb : ∀ p ∈ E, positiveBlockEnvelope θ n (driftedBrownianPath (-ν) p) ≤
      ENNReal.ofReal (Real.exp (θ * ν)) * F p := by
    intro p hp
    have hpn : p n - ν * n ≤ 1 := by
      have hn := hp n
      change p n + -ν * n < 1 at hn
      linarith
    dsimp [F]
    rw [indicator_of_mem (show p ∈ {p : BrownianPath | p n - ν * n ≤ 1} from hpn),
      ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity), ← Real.exp_add, ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    have hn := mul_le_mul_of_nonneg_left (brownianUnitNorm_shift_drift_le ν hν n p) hθ
    change θ * (p n + -ν * n) + |θ| *
      brownianUnitNorm (brownianShiftPath n (driftedBrownianPath (-ν) p)) ≤ _
    rw [abs_of_nonneg hθ]
    nlinarith
  rw [lintegral_brownianBelowConditionedLaw P ν 1 _ (measurable_positiveBlockEnvelope θ n)]
  have hbound : (∫⁻ p in E, positiveBlockEnvelope θ n (driftedBrownianPath (-ν) p) ∂P) ≤
      ENNReal.ofReal (Real.exp (θ * ν)) * ∫⁻ p, F p ∂P := by
    calc
      _ ≤ ∫⁻ p in E, ENNReal.ofReal (Real.exp (θ * ν)) * F p ∂P :=
        setLIntegral_mono' hE hb
      _ ≤ ∫⁻ p, ENNReal.ofReal (Real.exp (θ * ν)) * F p ∂P :=
        lintegral_mono' Measure.restrict_le_self le_rfl
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have he := brownian_truncated_endpoint_increment_factorization P hB n ν θ
  change (∫⁻ p, F p ∂P) = _ at he
  have hfin := brownianUnitNorm_exponential_moment_le P hB θ hθ
  have hterm := brownian_drift_truncated_exponential_moment_le P hB n ν θ hν hθ
  have hf : (∫⁻ p, F p ∂P) ≤ brownianWindowExponentialConstant θ *
      (ENNReal.ofReal (Real.exp (-θ * ν * n / 2)) +
        ENNReal.ofReal (Real.exp (θ - ν ^ 2 * n / 8))) := by
    rw [he, mul_comm]
    exact mul_le_mul' hfin hterm
  exact (mul_le_mul' le_rfl hbound).trans
    (by simpa only [mul_assoc] using
      mul_le_mul' (le_rfl : (ENNReal.ofReal (conditionedH ν 1))⁻¹ *
        ENNReal.ofReal (Real.exp (θ * ν)) ≤ _) hf)

/-- Raising a nonnegative-charge envelope to a nonnegative power multiplies its charge. -/
theorem positiveBlockEnvelope_rpow (γ q : ℝ) (n : ℝ≥0) (p : BrownianPath)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) :
    (positiveBlockEnvelope γ n p) ^ q = positiveBlockEnvelope (q * γ) n p := by
  rw [positiveBlockEnvelope, ennreal_exp_rpow]
  unfold positiveBlockEnvelope
  rw [abs_of_nonneg hγ, abs_of_nonneg (mul_nonneg hq hγ)]
  congr 2
  ring

/-- A block of the positive half-cylinder for an arbitrary continuous radial path and measure. -/
noncomputable def positiveLateralBlock (γ : ℝ) (n : ℝ≥0)
    (p : BrownianPath) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc (n : ℝ) ((n : ℝ) + 1),
    ENNReal.ofReal (Real.exp (γ * p (Real.toNNReal s))) ∂μ

/-- The actual block mass is bounded by the radial envelope times the lateral block mass. -/
theorem positiveLateralBlock_le_envelope (γ : ℝ) (hγ : 0 ≤ γ) (n : ℝ≥0)
    (p : BrownianPath) (μ : Measure ℝ) :
    positiveLateralBlock γ n p μ ≤
      positiveBlockEnvelope γ n p * μ (Ioc (n : ℝ) ((n : ℝ) + 1)) := by
  rw [← setLIntegral_const]
  apply setLIntegral_mono' measurableSet_Ioc
  intro s hs
  let t : ℝ≥0 := ⟨s - (n : ℝ), sub_nonneg.mpr hs.1.le⟩
  have ht : t ∈ Icc 0 (1 : ℝ≥0) := ⟨bot_le, by exact_mod_cast (by
    change s - (n : ℝ) ≤ 1
    linarith [hs.2])⟩
  have hspos : 0 ≤ s := n.coe_nonneg.trans hs.1.le
  have he : Real.toNNReal s = n + t := by
    apply NNReal.eq_iff.mpr
    rw [Real.coe_toNNReal s hspos, NNReal.coe_add]
    change s = (n : ℝ) + (s - (n : ℝ))
    ring
  have hn := ((brownianShiftPath n p).restrict (Icc 0 (1 : ℝ≥0))).norm_coe_le_norm ⟨t, ht⟩
  change |p (n + t) - p n| ≤ brownianUnitNorm (brownianShiftPath n p) at hn
  have hex : p (Real.toNNReal s) ≤ p n + brownianUnitNorm (brownianShiftPath n p) := by
    rw [he]
    have hle := (le_abs_self (p (n + t) - p n)).trans hn
    linarith
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonneg hγ]
  have h := mul_le_mul_of_nonneg_left hex hγ
  nlinarith

/-- Independent radial and lateral inputs factor the arbitrary given-chaos block estimate. -/
theorem positiveLateralBlock_moment_le_independent_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) (n : ℝ≥0)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P) (hi : IndepFun B Z P) :
    (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ≤
      (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) *
        (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) := by
  let f : BrownianPath → ℝ≥0∞ := positiveBlockEnvelope (q * γ) n
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q
  have hf : Measurable f := measurable_positiveBlockEnvelope _ _
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Ioc)
  have hind := hi.comp hf hg
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hB) (hg.comp_aemeasurable hZ) hind
  change (∫⁻ ω, f (B ω) * g (Z ω) ∂P) =
    (∫⁻ ω, f (B ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) at he
  rw [← he]
  apply lintegral_mono
  intro ω
  have hb := ENNReal.rpow_le_rpow (positiveLateralBlock_le_envelope γ hγ n (B ω) (Z ω)) hq
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq,
    positiveBlockEnvelope_rpow γ q n (B ω) hγ hq] at hb
  exact hb

/-- Stationarity reduces every positive block moment to the same initial lateral interval. -/
theorem positiveLateralBlock_moment_le_lateral_unit_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (hq : 0 ≤ q) (n : ℝ≥0) (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P) :
    (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ≤
      (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) *
        (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) := by
  have he := lateralGMC_interval_moment_translation_eq P γ Z hZ 0 1 q (n : ℝ)
  simp only [zero_add] at he
  rw [add_comm 1] at he
  have hb := positiveLateralBlock_moment_le_independent_envelope P γ q hZ.1.le hq n
    B Z hB hZ.2.2.2.1 hi
  rw [he] at hb
  exact hb

/-- An actual upper-conditioned radial law transfers the decaying envelope bound to blocks
of the given independent lateral chaos. This is the positive-block analytic input for the
conditioned-path comparison. -/
theorem upperConditioned_positiveLateralBlock_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ)
    (hν : 0 ≤ ν) (hq : 0 ≤ q) (n : ℝ≥0)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1) :
    (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ≤
      ((ENNReal.ofReal (conditionedH ν 1))⁻¹ * ENNReal.ofReal (Real.exp ((q * γ) * ν)) *
        brownianWindowExponentialConstant (q * γ) *
          (ENNReal.ofReal (Real.exp (-(q * γ) * ν * n / 2)) +
            ENNReal.ofReal (Real.exp ((q * γ) - ν ^ 2 * n / 8)))) *
        (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) := by
  have he := lintegral_map' (measurable_positiveBlockEnvelope (q * γ) n).aemeasurable hB
  change (∫⁻ p, positiveBlockEnvelope (q * γ) n p ∂P.map B) =
    (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω) ∂P) at he
  rw [hLaw] at he
  apply (positiveLateralBlock_moment_le_lateral_unit_moment P γ q hq n B Z hB hZ hi).trans
  rw [← he]
  exact mul_le_mul' (upperConditioned_positiveBlockEnvelope_mean_le P₀ hP₀ ν (q * γ)
    hν (mul_nonneg hq hZ.1.le) n) le_rfl

/-- Positive drift makes the below-one normalization strictly positive. -/
theorem conditionedH_one_pos (ν : ℝ) (hν : 0 < ν) : 0 < conditionedH ν 1 := by
  rw [conditionedH, ite_eq_right hν.ne']
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith))

/-- At positive drift, every given finite lateral moment yields a finite actual
upper-conditioned block moment of the same order. -/
theorem upperConditioned_positiveLateralBlock_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ)
    (hν : 0 < ν) (hq : 0 ≤ q) (n : ℝ≥0)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1)
    (hMoment : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) < ⊤) :
    (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  apply lt_of_le_of_lt (upperConditioned_positiveLateralBlock_moment_le
    P P₀ hP₀ ν γ q hν.le hq n B Z hB hZ hi hLaw)
  apply ENNReal.mul_lt_top _ hMoment
  apply ENNReal.mul_lt_top
  · apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (conditionedH_one_pos ν hν)))
        ENNReal.ofReal_lt_top
    · exact brownianWindowExponentialConstant_lt_top _
  · exact ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

/-- The sum of all actual upper-conditioned block moments is finite for every positive order
whose lateral unit-interval moment is finite. This supplies the subadditive positive-moment
assembly and the decay sequence for the higher-order Minkowski assembly. -/
theorem upperConditioned_positiveLateralBlock_moment_tsum_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ)
    (hν : 0 < ν) (hq : 0 < q)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1)
    (hMoment : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) < ⊤) :
    (∑' n : ℕ, ∫⁻ ω, (positiveLateralBlock γ (n : ℝ≥0) (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  let θ : ℝ := q * γ
  have hθ : 0 < θ := mul_pos hq hZ.1
  let C : ℝ≥0∞ := (ENNReal.ofReal (conditionedH ν 1))⁻¹ *
    ENNReal.ofReal (Real.exp (θ * ν)) * brownianWindowExponentialConstant θ *
      (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P)
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (conditionedH_one_pos ν hν)))
      ENNReal.ofReal_lt_top) (brownianWindowExponentialConstant_lt_top _)) hMoment
  let D : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-θ * ν * (n : ℝ) / 2)) +
    ENNReal.ofReal (Real.exp (θ - ν ^ 2 * (n : ℝ) / 8))
  have hD : (∑' n, D n) < ⊤ := by
    have he : D = fun n : ℕ => ENNReal.ofReal
        (Real.exp (-θ * ν * (n : ℝ) / 2) + Real.exp (θ - ν ^ 2 * (n : ℝ) / 8)) := by
      funext n
      exact (ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le).symm
    rw [he]
    exact (summable_brownian_drift_exponential_decay ν θ hν hθ).tsum_ofReal_lt_top
  have hb : ∀ n : ℕ,
      (∫⁻ ω, (positiveLateralBlock γ (n : ℝ≥0) (B ω) (Z ω)) ^ q ∂P) ≤ C * D n := by
    intro n
    have h := upperConditioned_positiveLateralBlock_moment_le
      P P₀ hP₀ ν γ q hν.le hq.le n B Z hB hZ hi hLaw
    convert h using 1
    dsimp [C, D, θ]
    simp only [NNReal.coe_natCast]
    ring
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hb)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top hC hD


/-- Integer open-closed unit intervals partition the positive real half-line. -/
theorem positive_unit_intervals_union :
    (⋃ n : ℕ, Ioc (n : ℝ) ((n : ℝ) + 1)) = Ioi (0 : ℝ) := by
  ext s
  constructor
  · intro hs
    obtain ⟨n, hn⟩ := mem_iUnion.mp hs
    exact lt_of_le_of_lt (Nat.cast_nonneg _) hn.1
  · intro hs
    have hceil : 1 ≤ Nat.ceil s := Nat.one_le_ceil_iff.mpr hs
    let n : ℕ := Nat.ceil s - 1
    have hn : n + 1 = Nat.ceil s := Nat.sub_add_cancel hceil
    have he : (n : ℝ) + 1 = (Nat.ceil s : ℝ) := by exact_mod_cast hn
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · have hc := Nat.ceil_lt_add_one hs.le
      linarith
    · rw [he]
      exact Nat.le_ceil s

/-- The positive unit intervals are disjoint even at their shared integer endpoints. -/
theorem positive_unit_intervals_pairwise_disjoint :
    Pairwise (fun m n : ℕ => Disjoint (Ioc (m : ℝ) ((m : ℝ) + 1))
      (Ioc (n : ℝ) ((n : ℝ) + 1))) := by
  intro m n hmn
  apply disjoint_left.mpr
  intro x hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have he : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.add_one_le_iff.mpr h
    exact not_lt_of_ge (hm.2.trans he) hn.1
  · have he : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.add_one_le_iff.mpr h
    exact not_lt_of_ge (hn.2.trans he) hm.1

/-- Integrating the exponential radial weight over the positive half-line. -/
noncomputable def positiveLateralMass (γ : ℝ) (p : BrownianPath) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (γ * p (Real.toNNReal s))) ∂μ

/-- The actual positive half-mass is precisely the sum of its unit blocks. -/
theorem positiveLateralMass_eq_tsum_blocks (γ : ℝ) (p : BrownianPath) (μ : Measure ℝ) :
    positiveLateralMass γ p μ = ∑' n : ℕ, positiveLateralBlock γ n p μ := by
  unfold positiveLateralMass positiveLateralBlock
  rw [← positive_unit_intervals_union]
  exact lintegral_iUnion (fun _ => measurableSet_Ioc)
    positive_unit_intervals_pairwise_disjoint _

/-- Each actual block is AE measurable for a given locally finite lateral measure. -/
theorem positiveLateralBlock_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (n : ℝ≥0)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) :
    AEMeasurable (fun ω => positiveLateralBlock γ n (B ω) (Z ω)) P := by
  let I : Set ℝ := Ioc (n : ℝ) ((n : ℝ) + 1)
  let f : BrownianPath × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (γ * z.1 (Real.toNNReal z.2)))
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (continuous_eval.comp (continuous_fst.prodMk
        (continuous_real_toNNReal.comp continuous_snd))).measurable))
  have hk := measurable_lintegral_finiteMeasure_parameter hf
  have hr : Measurable (fun μ : Measure ℝ => finiteRestrictionOnSet I μ) :=
    measurable_finiteRestrictionOnSet I measurableSet_Ioc
  have hrest := hr.comp_aemeasurable hZ.2.2.2.1
  have hp : AEMeasurable (fun ω => (B ω, finiteRestrictionOnSet I (Z ω))) P :=
    hB.prodMk hrest
  have hext := hk.comp_aemeasurable hp
  apply hext.congr
  filter_upwards [lateralGMC_interval_mass_finite_ae P γ Z hZ] with ω hω
  have hI : Z ω I < ⊤ := hω n ((n : ℝ) + 1)
  have he : (finiteRestrictionOnSet I (Z ω) : Measure ℝ) = (Z ω).restrict I := by
    simp [finiteRestrictionOnSet, hI]
  change (∫⁻ s, f (B ω, s) ∂(finiteRestrictionOnSet I (Z ω) : Measure ℝ)) = _
  rw [he]
  rfl

/-- The whole positive half-mass is AE measurable through its actual countable block sum. -/
theorem positiveLateralMass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) :
    AEMeasurable (fun ω => positiveLateralMass γ (B ω) (Z ω)) P := by
  have hm : AEMeasurable (fun ω => ∑' n : ℕ, positiveLateralBlock γ n (B ω) (Z ω)) P :=
    AEMeasurable.tsum (fun n : ℕ => positiveLateralBlock_aemeasurable P γ n B Z hB hZ)
  exact hm.congr (ae_of_all _ (fun ω => (positiveLateralMass_eq_tsum_blocks γ (B ω) (Z ω)).symm))

/-- Every given lateral chaos has finite positive half-mass mean under the independent
upper-conditioned Brownian path law. This conclusion needs only the already proved intensity. -/
theorem upperConditioned_positiveLateralMass_mean_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ : ℝ) (hν : 0 < ν)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1) :
    (∫⁻ ω, positiveLateralMass γ (B ω) (Z ω) ∂P) < ⊤ := by
  have hMoment : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ (1 : ℝ) ∂P) < ⊤ := by
    simp only [ENNReal.rpow_one]
    exact lateralGMC_Ioc_mean_lt_top P γ Z hZ 0 1 (by norm_num)
  have hb := upperConditioned_positiveLateralBlock_moment_tsum_lt_top
    P P₀ hP₀ ν γ 1 hν (by norm_num) B Z hB hZ hi hLaw hMoment
  simp only [ENNReal.rpow_one] at hb
  have he : (fun ω => positiveLateralMass γ (B ω) (Z ω)) =
      fun ω => ∑' n : ℕ, positiveLateralBlock γ n (B ω) (Z ω) :=
    funext (fun ω => positiveLateralMass_eq_tsum_blocks γ (B ω) (Z ω))
  rw [he, lintegral_tsum (fun n : ℕ => positiveLateralBlock_aemeasurable P γ n B Z hB hZ)]
  exact hb

/-- All subunit nonnegative half-mass moments are finite under that actual radial law,
for arbitrary given lateral chaos. No sharp positive or inverse GMC moment input is needed. -/
theorem upperConditioned_positiveLateralMass_subunit_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ) (hν : 0 < ν)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  have hb := lintegral_rpow_le_mean_rpow P hZ.2.2.1 _
    (positiveLateralMass_aemeasurable P γ B Z hB hZ) q hq0 hq1
  apply lt_of_le_of_lt hb
  exact ENNReal.rpow_lt_top_of_nonneg hq0
    (upperConditioned_positiveLateralMass_mean_lt_top P P₀ hP₀ ν γ hν B Z hB hZ hi hLaw).ne

private theorem lintegral_finset_rpow_root_le_sum
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Ω → ℝ≥0∞)
    (hF : ∀ n, AEMeasurable (F n) P) (q : ℝ) (hq : 1 ≤ q) (S : Finset ℕ) :
    (∫⁻ ω, (∑ n ∈ S, F n ω) ^ q ∂P) ^ (1 / q) ≤
      ∑ n ∈ S, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, lintegral_zero,
      ENNReal.zero_rpow_of_pos (lt_of_lt_of_le zero_lt_one hq),
      ENNReal.zero_rpow_of_pos (one_div_pos.mpr (lt_of_lt_of_le zero_lt_one hq))]
    exact le_rfl
  | @insert n S hn ih =>
    have hs : AEMeasurable (fun ω => ∑ i ∈ S, F i ω) P :=
      by
        convert Finset.aemeasurable_sum S (fun i _ => hF i) using 1
        funext ω
        exact (Finset.sum_apply ω S F).symm
    have hb := ENNReal.lintegral_Lp_add_le (hF n) hs hq
    change (∫⁻ ω, (F n ω + ∑ i ∈ S, F i ω) ^ q ∂P) ^ (1 / q) ≤
      (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q) +
        (∫⁻ ω, (∑ i ∈ S, F i ω) ^ q ∂P) ^ (1 / q) at hb
    simp only [Finset.sum_insert hn]
    exact hb.trans (add_le_add le_rfl ih)

/-- Infinite Minkowski assembly for nonnegative block masses, using their actual root moments. -/
theorem lintegral_tsum_rpow_le_root_moments_power
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Ω → ℝ≥0∞)
    (hF : ∀ n, AEMeasurable (F n) P) (q : ℝ) (hq : 1 ≤ q)
    : (∫⁻ ω, (∑' n, F n ω) ^ q ∂P) ≤
      (∑' n, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q)) ^ q := by
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let C : ℝ≥0∞ := ∑' n, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q)
  have hb : ∀ N : ℕ, (∫⁻ ω, (∑ n ∈ Finset.range N, F n ω) ^ q ∂P) ≤ C ^ q := by
    intro N
    have h := (lintegral_finset_rpow_root_le_sum P F hF q hq (Finset.range N)).trans
      (ENNReal.sum_le_tsum (Finset.range N))
    have he := ENNReal.rpow_le_rpow h hqp.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hqp.ne', ENNReal.rpow_one] at he
    exact he
  have hm : ∀ N : ℕ, AEMeasurable
      (fun ω => (∑ n ∈ Finset.range N, F n ω) ^ q) P := fun N =>
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (by
        classical
        convert Finset.aemeasurable_sum (Finset.range N) (fun n _ => hF n) using 1
        funext ω
        exact (Finset.sum_apply ω (Finset.range N) F).symm)
  have hmono : ∀ ω : Ω, Monotone (fun N : ℕ => (∑ n ∈ Finset.range N, F n ω) ^ q) := by
    intro ω N M hNM
    apply ENNReal.rpow_le_rpow _ hqp.le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM) (fun _ _ _ => bot_le)
  have hlim : ∀ ω : Ω, Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, F n ω) ^ q) atTop (𝓝 ((∑' n, F n ω) ^ q)) :=
    fun ω => ENNReal.continuous_rpow_const.continuousAt.tendsto.comp
      (ENNReal.tendsto_nat_tsum (fun n => F n ω))
  have hi := lintegral_tendsto_of_tendsto_of_monotone hm
    (ae_of_all _ hmono) (ae_of_all _ hlim)
  exact le_of_tendsto' hi hb

/-- A finite sum of block root moments implies a finite moment of the entire block sum. -/
theorem lintegral_tsum_rpow_lt_top_of_root_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (F : ℕ → Ω → ℝ≥0∞)
    (hF : ∀ n, AEMeasurable (F n) P) (q : ℝ) (hq : 1 ≤ q)
    (hRoot : (∑' n, (∫⁻ ω, (F n ω) ^ q ∂P) ^ (1 / q)) < ⊤) :
    (∫⁻ ω, (∑' n, F n ω) ^ q ∂P) < ⊤ := by
  exact lt_of_le_of_lt (lintegral_tsum_rpow_le_root_moments_power P F hF q hq)
    (ENNReal.rpow_lt_top_of_nonneg (le_trans zero_le_one hq) hRoot.ne)

private theorem summable_two_exponential_decay (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Summable (fun n : ℕ => Real.exp (-a * (n : ℝ)) + Real.exp (c - b * (n : ℝ))) := by
  have h1 := (Real.summable_exp_nat_mul_iff (a := -a)).mpr (neg_neg_of_pos ha)
  have h2 := (Real.summable_exp_nat_mul_iff (a := -b)).mpr (neg_neg_of_pos hb)
  have he : (fun n : ℕ => Real.exp (-a * (n : ℝ)) + Real.exp (c - b * (n : ℝ))) =
      fun n : ℕ => Real.exp ((n : ℝ) * -a) + Real.exp c * Real.exp ((n : ℝ) * -b) := by
    funext n
    rw [← Real.exp_add]
    congr 2 <;> ring
  rw [he]
  exact h1.add (h2.mul_left _)

/-- Taking a positive root preserves summability of the exponential block decay. -/
theorem ennreal_tsum_root_exponential_decay_lt_top
    (C : ℝ≥0∞) (hC : C < ⊤) (a b c r : ℝ) (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    (∑' n : ℕ, (C * (ENNReal.ofReal (Real.exp (-a * (n : ℝ))) +
      ENNReal.ofReal (Real.exp (c - b * (n : ℝ))))) ^ r) < ⊤ := by
  let D : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal
    (Real.exp (-(a * r) * (n : ℝ)) + Real.exp ((c * r) - (b * r) * (n : ℝ)))
  have hD : (∑' n, D n) < ⊤ :=
    (summable_two_exponential_decay (a * r) (b * r) (c * r)
      (mul_pos ha hr) (mul_pos hb hr)).tsum_ofReal_lt_top
  have hbound : ∀ n : ℕ,
      (C * (ENNReal.ofReal (Real.exp (-a * (n : ℝ))) +
        ENNReal.ofReal (Real.exp (c - b * (n : ℝ))))) ^ r ≤ C ^ r * 2 ^ r * D n := by
    intro n
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
    have hp := ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow
      (ENNReal.ofReal (Real.exp (-a * (n : ℝ))))
      (ENNReal.ofReal (Real.exp (c - b * (n : ℝ)))) hr.le
    rw [ennreal_exp_rpow, ennreal_exp_rpow] at hp
    have he : ENNReal.ofReal (Real.exp ((-a * (n : ℝ)) * r)) +
        ENNReal.ofReal (Real.exp ((c - b * (n : ℝ)) * r)) = D n := by
      dsimp [D]
      have h1 : (-a * (n : ℝ)) * r = -(a * r) * (n : ℝ) := by ring
      have h2 : (c - b * (n : ℝ)) * r = c * r - (b * r) * (n : ℝ) := by ring
      rw [h1, h2, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    rw [he] at hp
    exact (mul_le_mul' le_rfl hp).trans_eq (mul_assoc _ _ _).symm
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound)
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr.le hC.ne)
      (ENNReal.rpow_lt_top_of_nonneg hr.le (by norm_num))) hD

/-- The actual upper-conditioned block root moments are summable at every positive order
with a finite lateral unit moment. This includes orders above one. -/
theorem upperConditioned_positiveLateralBlock_root_moments_tsum_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ)
    (hν : 0 < ν) (hq : 0 < q)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1)
    (hMoment : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) < ⊤) :
    (∑' n : ℕ, (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ^ (1 / q)) < ⊤ := by
  let θ : ℝ := q * γ
  have hθ : 0 < θ := mul_pos hq hZ.1
  let C : ℝ≥0∞ := (ENNReal.ofReal (conditionedH ν 1))⁻¹ *
    ENNReal.ofReal (Real.exp (θ * ν)) * brownianWindowExponentialConstant θ *
      (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P)
  have hC : C < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (conditionedH_one_pos ν hν)))
      ENNReal.ofReal_lt_top) (brownianWindowExponentialConstant_lt_top _)) hMoment
  have hb : ∀ n : ℕ, (∫⁻ ω, (positiveLateralBlock γ n (B ω) (Z ω)) ^ q ∂P) ≤
      C * (ENNReal.ofReal (Real.exp (-(θ * ν / 2) * (n : ℝ))) +
        ENNReal.ofReal (Real.exp (θ - (ν ^ 2 / 8) * (n : ℝ)))) := by
    intro n
    have h := upperConditioned_positiveLateralBlock_moment_le
      P P₀ hP₀ ν γ q hν.le hq.le n B Z hB hZ hi hLaw
    convert h using 1
    dsimp [C, θ]
    simp only [NNReal.coe_natCast]
    have he1 : -(q * γ) * ν * (n : ℝ) / 2 = -(q * γ * ν / 2) * (n : ℝ) := by ring
    have he2 : q * γ - ν ^ 2 * (n : ℝ) / 8 = q * γ - (ν ^ 2 / 8) * (n : ℝ) := by ring
    rw [he1, he2]
    ring
  apply lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun n : ℕ =>
    ENNReal.rpow_le_rpow (hb n) (one_div_pos.mpr hq).le))
  exact ennreal_tsum_root_exponential_decay_lt_top C hC (θ * ν / 2) (ν ^ 2 / 8) θ (1 / q)
    (div_pos (mul_pos hθ hν) (by norm_num))
    (div_pos (sq_pos_of_pos hν) (by norm_num)) (one_div_pos.mpr hq)

/-- Infinite Minkowski closes the whole positive half-mass moment above order one, using the
already proved actual block root moments and measurability. -/
theorem upperConditioned_positiveLateralMass_higher_moment_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ) (hν : 0 < ν) (hq : 1 ≤ q)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1)
    (hMoment : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) < ⊤) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  have hRoot := upperConditioned_positiveLateralBlock_root_moments_tsum_lt_top
    P P₀ hP₀ ν γ q hν (lt_of_lt_of_le zero_lt_one hq) B Z hB hZ hi hLaw hMoment
  have hb := lintegral_tsum_rpow_lt_top_of_root_moments P
    (fun n : ℕ => fun ω => positiveLateralBlock γ n (B ω) (Z ω))
    (fun n => positiveLateralBlock_aemeasurable P γ n B Z hB hZ) q hq hRoot
  simpa only [positiveLateralMass_eq_tsum_blocks] using hb

/-- Every given finite nonnegative lateral unit-interval moment transfers to the whole
upper-conditioned half-cylinder mass. The proof includes the infinite block sum at all orders. -/
theorem upperConditioned_positiveLateralMass_moment_finite_of_unit_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (ν γ q : ℝ) (hν : 0 < ν) (hq : 0 ≤ q)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hi : IndepFun B Z P)
    (hLaw : P.map B = brownianBelowConditionedLaw P₀ ν 1)
    (hMoment : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P) < ⊤) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  rcases le_total q 1 with hq1 | hq1
  · exact upperConditioned_positiveLateralMass_subunit_moment_lt_top
      P P₀ hP₀ ν γ q hν hq hq1 B Z hB hZ hi hLaw
  · exact upperConditioned_positiveLateralMass_higher_moment_lt_top
      P P₀ hP₀ ν γ q hν hq1 B Z hB hZ hi hLaw hMoment

/-- Positive-order moment bounds transfer along an actual ordered radial coupling while
retaining the same given lateral measure. No coupling existence is assumed implicitly. -/
theorem positiveLateralMass_moment_finite_of_ordered_radial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ) (hγ : 0 ≤ γ) (hq : 0 ≤ q)
    (B B' : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hOrder : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, B ω t ≤ B' ω t)
    (hMoment : (∫⁻ ω, (positiveLateralMass γ (B' ω) (Z ω)) ^ q ∂P) < ⊤) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) < ⊤ := by
  apply lt_of_le_of_lt _ hMoment
  apply lintegral_mono_ae
  filter_upwards [hOrder] with ω hω
  apply ENNReal.rpow_le_rpow _ hq
  apply lintegral_mono
  intro s
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hω (Real.toNNReal s)) hγ))

end DOZZ.Proofs
