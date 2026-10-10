/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralMomentConcave
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Intensity and translated moments of the lateral measure

The exact interval intensity determines the entire expected measure. This gives the first
moment of every nonnegative Borel test and null mass at every fixed interval endpoint.
Stationarity gives exact equality of interval moments at every real translate and for every
real exponent. Bounding a compact exponent range reduces to bounding its two endpoint moments;
the reduction covers negative orders and the extended-real values zero and infinity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The expected lateral measure is precisely its flat reference measure. -/
theorem lateralGMC_bind_eq_volume {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    P.bind Z = ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ) := by
  have hZm : AEMeasurable Z P := hZ.2.2.2.1
  have hI : ∀ a b : ℝ, a < b →
      (P.bind Z) (Ioc a b) = ENNReal.ofReal (2 * Real.pi * (b - a)) := by
    intro a b hab
    rw [Measure.bind_apply measurableSet_Ioc hZm]
    exact lateralGMC_interval_first_moment P γ Z hZ a b hab
  apply Measure.ext_of_Ioc'
  · intro a b hab
    rw [hI a b hab]
    exact ENNReal.ofReal_ne_top
  · intro a b hab
    rw [hI a b hab, Measure.smul_apply, Real.volume_Ioc, smul_eq_mul,
      ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]

/-- Every nonnegative Borel test has the exact flat lateral first moment. -/
theorem lateralGMC_lintegral_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ s, f s ∂Z ω ∂P) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ s, f s ∂(volume : Measure ℝ) := by
  rw [← Measure.lintegral_bind hZ.2.2.2.1 hf.aemeasurable,
    lateralGMC_bind_eq_volume P γ Z hZ, lintegral_smul_measure, smul_eq_mul]

/-- The mean of each measurable set mass is its flat reference mass. -/
theorem lateralGMC_set_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫⁻ ω, Z ω S ∂P) = ENNReal.ofReal (2 * Real.pi) * volume S := by
  rw [← Measure.bind_apply hS hZ.2.2.2.1,
    lateralGMC_bind_eq_volume P γ Z hZ, Measure.smul_apply, smul_eq_mul]

/-- Any fixed Lebesgue-null Borel set has zero lateral mass almost surely. -/
theorem lateralGMC_null_set_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (S : Set ℝ) (hS : MeasurableSet S) (hnull : volume S = 0) :
    ∀ᵐ ω ∂P, Z ω S = 0 := by
  have hm : AEMeasurable (fun ω => Z ω S) P :=
    (Measure.measurable_coe hS).comp_aemeasurable hZ.2.2.2.1
  apply (lintegral_eq_zero_iff' hm).1
  rw [lateralGMC_set_mean P γ Z hZ S hS, hnull, mul_zero]

/-- Each deterministic endpoint has zero mass, without asserting an uncountable common event. -/
theorem lateralGMC_singleton_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a : ℝ) : ∀ᵐ ω ∂P, Z ω {a} = 0 :=
  lateralGMC_null_set_ae P γ Z hZ {a} (measurableSet_singleton a) (measure_singleton a)

/-- A fixed closed interval and its open-closed version agree almost surely. -/
theorem lateralGMC_Icc_eq_Ioc_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b : ℝ) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, Z ω (Icc a b) = Z ω (Ioc a b) := by
  filter_upwards [lateralGMC_singleton_ae P γ Z hZ a] with ω hω
  have hset : Icc a b = {a} ∪ Ioc a b := by
    ext x
    simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
    constructor
    · intro hx
      rcases eq_or_lt_of_le hx.1 with he | he
      · exact Or.inl he.symm
      · exact Or.inr ⟨he, hx.2⟩
    · rintro (rfl | hx)
      · exact ⟨le_rfl, hab⟩
      · exact ⟨hx.1.le, hx.2⟩
  rw [hset, measure_union (by simp) measurableSet_Ioc, hω, zero_add]

/-- Powers of interval mass are AE measurable at every real exponent. -/
theorem lateralGMC_interval_rpow_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) :
    AEMeasurable (fun ω => (Z ω (Ioc a b)) ^ q) P := by
  exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
    ((Measure.measurable_coe measurableSet_Ioc).comp_aemeasurable hZ.2.2.2.1)

/-- A deterministic real translate has exactly the same interval moment, for positive,
zero, and negative exponents. -/
theorem lateralGMC_interval_moment_translation_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q t : ℝ) :
    (∫⁻ ω, (Z ω (Ioc (a + t) (b + t))) ^ q ∂P) =
      ∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P := by
  let F : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Ioc a b)) ^ q
  have hF : Measurable F :=
    ENNReal.continuous_rpow_const.measurable.comp (Measure.measurable_coe measurableSet_Ioc)
  let T : Measure ℝ → Measure ℝ := fun μ => μ.map (fun s : ℝ => s + (-t))
  have hT : Measurable T := Measure.measurable_map _ (by fun_prop)
  have hTZ : AEMeasurable (fun ω => T (Z ω)) P :=
    hT.comp_aemeasurable hZ.2.2.2.1
  have hstat : P.map (fun ω => T (Z ω)) = P.map Z := hZ.2.2.2.2.2.1 (-t)
  have hpre : (fun s : ℝ => s + (-t)) ⁻¹' Ioc a b = Ioc (a + t) (b + t) := by
    ext s
    simp only [mem_preimage, mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hpoint (ω : Ω) : F (T (Z ω)) = (Z ω (Ioc (a + t) (b + t))) ^ q := by
    dsimp [F, T]
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioc, hpre]
  calc
    _ = ∫⁻ ω, F (T (Z ω)) ∂P := lintegral_congr (fun ω => (hpoint ω).symm)
    _ = ∫⁻ μ, F μ ∂P.map (fun ω => T (Z ω)) :=
      (lintegral_map' hF.aemeasurable hTZ).symm
    _ = ∫⁻ μ, F μ ∂P.map Z := by rw [hstat]
    _ = ∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P := lintegral_map' hF.aemeasurable hZ.2.2.2.1

/-- Uniformity over translates costs no additional moment estimate. -/
theorem lateralGMC_uniform_interval_moment_iff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Kγ Kq : Set ℝ) (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ)) (a b : ℝ) (C : ℝ≥0∞) :
    (∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
      (∫⁻ ω, (Z γ ω (Ioc (a + t) (b + t))) ^ q ∂P) ≤ C) ↔
    (∀ γ ∈ Kγ, ∀ q ∈ Kq, (∫⁻ ω, (Z γ ω (Ioc a b)) ^ q ∂P) ≤ C) := by
  constructor
  · intro h γ hγ q hq
    simpa only [add_zero] using h γ hγ q hq 0
  · intro h γ hγ q hq t
    rw [lateralGMC_interval_moment_translation_eq P γ (Z γ) (hZ γ hγ)]
    exact h γ hγ q hq

/-- Every exponent between two real endpoints is bounded by the sum of their powers,
including at the extended-real boundary values. -/
theorem ennreal_rpow_le_endpoint_sum (x : ℝ≥0∞) {l q u : ℝ} (hl : l ≤ q) (hu : q ≤ u) :
    x ^ q ≤ x ^ l + x ^ u := by
  rcases le_total x 1 with hx | hx
  · exact (ENNReal.rpow_le_rpow_of_exponent_ge hx hl).trans (le_add_right le_rfl)
  · exact (ENNReal.rpow_le_rpow_of_exponent_le hx hu).trans (le_add_left le_rfl)

/-- Two endpoint moments bound every exponent between them. -/
theorem lintegral_rpow_le_endpoint_sum {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (V : Ω → ℝ≥0∞) (hV : AEMeasurable V P)
    {l q u : ℝ} (hl : l ≤ q) (hu : q ≤ u) :
    (∫⁻ ω, (V ω) ^ q ∂P) ≤ (∫⁻ ω, (V ω) ^ l ∂P) + ∫⁻ ω, (V ω) ^ u ∂P := by
  calc
    _ ≤ ∫⁻ ω, (V ω) ^ l + (V ω) ^ u ∂P :=
      lintegral_mono (fun ω => ennreal_rpow_le_endpoint_sum (V ω) hl hu)
    _ = _ := lintegral_add_left' (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hV) _


/-- A compact charge set satisfying the lateral carrier stays strictly inside `(0,2)`. -/
theorem lateralGMC_compact_charge_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Kγ : Set ℝ) (hKγ : IsCompact Kγ) (hne : Kγ.Nonempty)
    (Z : ℝ → Ω → Measure ℝ) (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ)) :
    ∃ γlo γhi : ℝ, 0 < γlo ∧ γhi < 2 ∧ ∀ γ ∈ Kγ, γlo ≤ γ ∧ γ ≤ γhi := by
  obtain ⟨γlo, hlo, hmin⟩ := hKγ.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨γhi, hhi, hmax⟩ := hKγ.exists_isMaxOn hne continuous_id.continuousOn
  refine ⟨γlo, γhi, (hZ γlo hlo).1, (hZ γhi hhi).2.1, ?_⟩
  intro γ hγ
  exact ⟨hmin hγ, hmax hγ⟩

/-- Compact strict subcritical parameter ranges have a quantitative uniform margin. -/
theorem lateralGMC_compact_moment_margin
    (Kγ Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKq : IsCompact Kq)
    (hγne : Kγ.Nonempty) (hqne : Kq.Nonempty)
    (hγ : ∀ γ ∈ Kγ, 0 < γ) (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ ∈ Kγ, ∀ q ∈ Kq, q + δ ≤ 4 / γ ^ 2 := by
  let D : ℝ × ℝ → ℝ := fun p => 4 / p.1 ^ 2 - p.2
  have hc : ContinuousOn D (Kγ ×ˢ Kq) := by
    exact (continuousOn_const.div (continuous_fst.pow 2).continuousOn
      (fun p hp => pow_ne_zero 2 (hγ p.1 hp.1).ne')).sub continuous_snd.continuousOn
  obtain ⟨p, hp, hmin⟩ := (hKγ.prod hKq).exists_isMinOn (hγne.prod hqne) hc
  have hd : 0 < D p := sub_pos.mpr (hq p.1 hp.1 p.2 hp.2)
  refine ⟨D p, hd, ?_⟩
  intro γ hγm q hqm
  have h := hmin (show (γ, q) ∈ Kγ ×ˢ Kq from ⟨hγm, hqm⟩)
  change D p ≤ 4 / γ ^ 2 - q at h
  linarith

/-- Choose two exponents strictly enclosing the compact moment set, with one common positive
subcritical margin for the upper endpoint over the entire compact charge set. -/
theorem lateralGMC_compact_moment_endpoints
    (Kγ Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKq : IsCompact Kq)
    (hγne : Kγ.Nonempty) (hqne : Kq.Nonempty)
    (hγ : ∀ γ ∈ Kγ, 0 < γ) (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ l u δ : ℝ, 0 < δ ∧
      (∀ q ∈ Kq, l < q ∧ q < u) ∧ (∀ γ ∈ Kγ, u + δ ≤ 4 / γ ^ 2) := by
  obtain ⟨qlo, hlo, hmin⟩ := hKq.exists_isMinOn hqne continuous_id.continuousOn
  obtain ⟨qhi, hhi, hmax⟩ := hKq.exists_isMaxOn hqne continuous_id.continuousOn
  obtain ⟨δ, hδ, hmargin⟩ := lateralGMC_compact_moment_margin
    Kγ Kq hKγ hKq hγne hqne hγ hq
  refine ⟨qlo - 1, qhi + δ / 2, δ / 2, by positivity, ?_, ?_⟩
  · intro q hqm
    have hloq : qlo ≤ q := hmin hqm
    have hhiq : q ≤ qhi := hmax hqm
    constructor <;> linarith
  · intro γ hγm
    have h := hmargin γ hγm qhi hhi
    linarith

/-- Finiteness of any negative interval moment rules out zero interval mass almost surely. -/
theorem lateralGMC_interval_pos_ae_of_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hq : q < 0)
    (hfinite : (∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P) < ⊤) :
    ∀ᵐ ω ∂P, 0 < Z ω (Ioc a b) := by
  have hf := ae_lt_top' (lateralGMC_interval_rpow_aemeasurable P γ Z hZ a b q) hfinite.ne
  filter_upwards [hf] with ω hω
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, ENNReal.zero_rpow_of_neg hq] at hω
  exact hω.false

/-- Fixed closed-interval masses have exactly the same moments as their open-closed versions. -/
theorem lateralGMC_Icc_moment_eq_Ioc {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) (hab : a ≤ b) :
    (∫⁻ ω, (Z ω (Icc a b)) ^ q ∂P) = ∫⁻ ω, (Z ω (Ioc a b)) ^ q ∂P := by
  apply lintegral_congr_ae
  filter_upwards [lateralGMC_Icc_eq_Ioc_ae P γ Z hZ a b hab] with ω hω
  rw [hω]

/-- Expected mass on a bounded interval is finite at every charge in the lateral carrier. -/
theorem lateralGMC_Ioc_mean_lt_top {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b : ℝ) (hab : a < b) : (∫⁻ ω, Z ω (Ioc a b) ∂P) < ⊤ := by
  rw [lateralGMC_interval_first_moment P γ Z hZ a b hab]
  exact ENNReal.ofReal_lt_top



/-- Empty parameter sets satisfy the exact moment-bound conclusion without additional data. -/
theorem lateralGMC_interval_uniform_empty {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Kγ Kq : Set ℝ) (Z : ℝ → Ω → Measure ℝ)
    (a b : ℝ) (hempty : Kγ = ∅ ∨ Kq = ∅) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
      (∫⁻ ω, (Z γ ω (Ioc (a + t) (b + t))) ^ q ∂P) ≤ C := by
  refine ⟨0, bot_lt_top, ?_⟩
  rcases hempty with hγ | hq
  · simp only [hγ, mem_empty_iff_false, false_implies, forall_const]
  · simp only [hq, mem_empty_iff_false, false_implies, forall_const, implies_true]


/-- Reflection gives exact moment equality for closed intervals on the two half-cylinders. -/
theorem lateralGMC_Icc_moment_reflection_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b q : ℝ) :
    (∫⁻ ω, (Z ω (Icc (-b) (-a))) ^ q ∂P) = ∫⁻ ω, (Z ω (Icc a b)) ^ q ∂P := by
  let F : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Icc a b)) ^ q
  have hF : Measurable F :=
    ENNReal.continuous_rpow_const.measurable.comp (Measure.measurable_coe measurableSet_Icc)
  let T : Measure ℝ → Measure ℝ := fun μ => μ.map (fun s : ℝ => -s)
  have hT : Measurable T := Measure.measurable_map _ measurable_neg
  have hTZ : AEMeasurable (fun ω => T (Z ω)) P :=
    hT.comp_aemeasurable hZ.2.2.2.1
  have hstat : P.map (fun ω => T (Z ω)) = P.map Z := hZ.2.2.2.2.2.2.1
  have hpre : (fun s : ℝ => -s) ⁻¹' Icc a b = Icc (-b) (-a) := by
    ext s
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hpoint (ω : Ω) : F (T (Z ω)) = (Z ω (Icc (-b) (-a))) ^ q := by
    dsimp [F, T]
    rw [Measure.map_apply measurable_neg measurableSet_Icc, hpre]
  calc
    _ = ∫⁻ ω, F (T (Z ω)) ∂P := lintegral_congr (fun ω => (hpoint ω).symm)
    _ = ∫⁻ μ, F μ ∂P.map (fun ω => T (Z ω)) :=
      (lintegral_map' hF.aemeasurable hTZ).symm
    _ = ∫⁻ μ, F μ ∂P.map Z := by rw [hstat]
    _ = ∫⁻ ω, (Z ω (Icc a b)) ^ q ∂P := lintegral_map' hF.aemeasurable hZ.2.2.2.1




/-- Finite interval mass holds on one common event for every deterministic translate. -/
theorem lateralGMC_interval_mass_finite_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤ := by
  filter_upwards [hZ.2.2.2.2.1] with ω hω a b
  exact (measure_mono Ioc_subset_Icc_self).trans_lt (hω a b)


/-- The interval-finiteness clause gives genuine local finiteness on the line. -/
theorem lateralGMC_locallyFinite_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z ω) := by
  filter_upwards [hZ.2.2.2.2.1] with ω hω
  refine ⟨fun x => ?_⟩
  exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), hω _ _⟩




end DOZZ.Proofs
