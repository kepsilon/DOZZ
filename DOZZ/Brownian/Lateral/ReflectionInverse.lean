/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.AnnularComparison
public import DOZZ.Brownian.ReflectionMassMeasurability

/-!
# Initial-block inverse estimates for the two-sided reflection mass

For arbitrary continuous radial paths and an independent given lateral chaos, the initial
positive-time block gives an inverse-moment estimate. It uses one lateral measure throughout;
no independence between its two half-lines is required. The radial exponential-supremum
estimate and the lateral inverse-moment estimate remain explicit analytic inputs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The norm on a bounded time window of both continuous half-paths controls their joined value. -/
noncomputable def reflectionWindowBound (γ : ℝ) (T : ℝ≥0)
    (b : BrownianPath × BrownianPath) : ℝ :=
  |γ| * (‖b.1.restrict (Icc 0 T)‖ + ‖b.2.restrict (Icc 0 T)‖)

/-- The compact norm bound is continuous on the actual full path-pair carrier. -/
theorem continuous_reflectionWindowBound (γ : ℝ) (T : ℝ≥0) :
    Continuous (reflectionWindowBound γ T) := by
  unfold reflectionWindowBound
  exact continuous_const.mul
    ((continuous_norm.comp ((ContinuousMap.continuous_restrict _).comp continuous_fst)).add
      (continuous_norm.comp ((ContinuousMap.continuous_restrict _).comp continuous_snd)))


/-- Both signed halves are controlled by the same compact-window bound. -/
theorem abs_twoSidedConditionedExponent_le {Ω : Type*} (γ : ℝ) (T : ℝ≥0)
    (B : Ω → BrownianPath × BrownianPath) (ω : Ω) (s : ℝ) (hs : |s| ≤ T) :
    |γ * twoSidedConditionedValue B ω s| ≤ reflectionWindowBound γ T (B ω) := by
  have hbound : |twoSidedConditionedValue B ω s| ≤
      ‖(B ω).1.restrict (Icc 0 T)‖ + ‖(B ω).2.restrict (Icc 0 T)‖ := by
    by_cases hs0 : 0 ≤ s
    · let t : ℝ≥0 := ⟨s, hs0⟩
      have ht : t ∈ Icc 0 T := ⟨bot_le, by exact_mod_cast (abs_of_nonneg hs0 ▸ hs)⟩
      have h := ((B ω).1.restrict (Icc 0 T)).norm_coe_le_norm ⟨t, ht⟩
      change |(B ω).1 t| ≤ _ at h
      have he : twoSidedConditionedValue B ω s = (B ω).1 t := by
        simp only [twoSidedConditionedValue, hs0, dite_true, t]
      rw [he]
      exact h.trans (le_add_of_nonneg_right (norm_nonneg _))
    · have hns : 0 ≤ -s := by linarith
      let t : ℝ≥0 := ⟨-s, hns⟩
      have ht : t ∈ Icc 0 T := ⟨bot_le, by
        exact_mod_cast (abs_of_neg (lt_of_not_ge hs0) ▸ hs)⟩
      have h := ((B ω).2.restrict (Icc 0 T)).norm_coe_le_norm ⟨t, ht⟩
      change |(B ω).2 t| ≤ _ at h
      have he : twoSidedConditionedValue B ω s = (B ω).2 t := by
        simp only [twoSidedConditionedValue, hs0, dite_false, t]
      rw [he]
      exact h.trans (le_add_of_nonneg_left (norm_nonneg _))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)

/-- Retaining the first positive-time block gives a pathwise lower bound for the whole mass. -/
theorem twoSidedReflectionMass_initialBlock_lower {Ω : Type*} (γ : ℝ) (T : ℝ≥0)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    ENNReal.ofReal (Real.exp (-reflectionWindowBound γ T (B ω))) *
        Z ω (Ioc 0 (T : ℝ)) ≤ twoSidedReflectionMass γ B Z ω := by
  calc
    _ = ∫⁻ s in Ioc 0 (T : ℝ),
        ENNReal.ofReal (Real.exp (-reflectionWindowBound γ T (B ω))) ∂Z ω :=
      (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ s in Ioc 0 (T : ℝ),
        ENNReal.ofReal (Real.exp (γ * twoSidedConditionedValue B ω s)) ∂Z ω := by
      apply setLIntegral_mono' measurableSet_Ioc
      intro s hs
      have habs : |s| ≤ T := by rw [abs_of_pos hs.1]; exact hs.2
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
        (abs_le.mp (abs_twoSidedConditionedExponent_le γ T B ω s habs)).1)
    _ ≤ twoSidedReflectionMass γ B Z ω :=
      lintegral_mono' Measure.restrict_le_self le_rfl

/-- Nonpositive powers reverse mass inequalities, including at zero and infinity. -/
theorem ennreal_rpow_antitone_nonpos (x y : ℝ≥0∞) (q : ℝ)
    (hxy : x ≤ y) (hq : q ≤ 0) : y ^ q ≤ x ^ q := by
  have h := ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hxy (neg_nonneg.mpr hq))
  simpa only [← ENNReal.rpow_neg, neg_neg] using h

/-- The inverse of the full reflection mass is controlled by a single lateral interval and
a compact-window radial exponential. Only the lateral interval mass must be finite. -/
theorem twoSidedReflectionMass_inverse_le_initialBlock {Ω : Type*}
    (γ q : ℝ) (hq : q ≤ 0) (T : ℝ≥0)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω)
    (hfinite : Z ω (Ioc 0 (T : ℝ)) ≠ ⊤) :
    (twoSidedReflectionMass γ B Z ω) ^ q ≤
      ENNReal.ofReal (Real.exp (|q| * reflectionWindowBound γ T (B ω))) *
        (Z ω (Ioc 0 (T : ℝ))) ^ q := by
  have h := ennreal_rpow_antitone_nonpos _ _ q
    (twoSidedReflectionMass_initialBlock_lower γ T B Z ω) hq
  rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hfinite,
    ennreal_exp_rpow] at h
  have he : (-reflectionWindowBound γ T (B ω)) * q =
      |q| * reflectionWindowBound γ T (B ω) := by
    rw [abs_of_nonpos hq]
    ring
  simpa only [he] using h

/-- The radial factor in the initial-block inverse estimate. -/
noncomputable def reflectionInverseWindowFactor (γ q : ℝ) (T : ℝ≥0)
    (b : BrownianPath × BrownianPath) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (|q| * reflectionWindowBound γ T b))

/-- The radial factor is measurable on the full path-pair carrier. -/
theorem measurable_reflectionInverseWindowFactor (γ q : ℝ) (T : ℝ≥0) :
    Measurable (reflectionInverseWindowFactor γ q T) := by
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_reflectionWindowBound γ T).measurable))

/-- Independence factors the initial-block inverse bound into its two actual expectations. -/
theorem twoSidedReflectionMass_inverse_moment_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ q : ℝ) (hq : q ≤ 0) (T : ℝ≥0)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P) (hInd : IndepFun B Z P)
    (hfinite : ∀ᵐ ω ∂P, Z ω (Ioc 0 (T : ℝ)) < ⊤) :
    (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) ≤
      (∫⁻ ω, reflectionInverseWindowFactor γ q T (B ω) ∂P) *
        (∫⁻ ω, (Z ω (Ioc 0 (T : ℝ))) ^ q ∂P) := by
  let f : BrownianPath × BrownianPath → ℝ≥0∞ := reflectionInverseWindowFactor γ q T
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Ioc 0 (T : ℝ))) ^ q
  have hf : Measurable f := measurable_reflectionInverseWindowFactor γ q T
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Ioc)
  have hi : IndepFun (fun ω => f (B ω)) (fun ω => g (Z ω)) P := hInd.comp hf hg
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hB) (hg.comp_aemeasurable hZ) hi
  change (∫⁻ ω, f (B ω) * g (Z ω) ∂P) =
      (∫⁻ ω, f (B ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) at hprod
  rw [← hprod]
  apply lintegral_mono_ae
  filter_upwards [hfinite] with ω hω
  exact twoSidedReflectionMass_inverse_le_initialBlock γ q hq T B Z ω hω.ne


/-- Local finiteness makes the actual full reflection mass AE measurable for any AE measurable
path pair; a conditioned law is not needed for this carrier fact. -/
theorem twoSidedReflectionMass_aemeasurable_of_lateral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) :
    AEMeasurable (fun ω => twoSidedReflectionMass γ B Z ω) P := by
  have hp : AEMeasurable (fun ω => (B ω, Z ω)) P := hB.prodMk hZ.2.2.2.1
  have hl : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω) := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω
    intro n
    exact hω (-(n : ℝ)) n
  have hm := aemeasurable_reflectionMassInput_map_of_locallyFinite P γ
    (fun ω => (B ω, Z ω)) hp hl
  exact hm.comp_aemeasurable hp

/-- Every real moment integrand of the actual reflection mass is AE measurable. -/
theorem twoSidedReflectionMass_rpow_aemeasurable_of_lateral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) :
    AEMeasurable (fun ω => (twoSidedReflectionMass γ B Z ω) ^ q) P := by
  exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
    (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hB hZ)

/-- The zero-order reflection moment is exactly one under lateral probability normalization. -/
theorem twoSidedReflectionMass_moment_zero_of_lateral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) :
    (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ (0 : ℝ) ∂P) = 1 := by
  let _ := hZ.2.2.1
  simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one]

/-- A finite strictly negative moment implies almost sure positive reflection mass. -/
theorem twoSidedReflectionMass_pos_ae_of_negative_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hq : q < 0)
    (hm : (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) < ⊤) :
    ∀ᵐ ω ∂P, 0 < twoSidedReflectionMass γ B Z ω := by
  have hf := ae_lt_top' (twoSidedReflectionMass_rpow_aemeasurable_of_lateral
    P γ q B Z hB hZ) hm.ne
  filter_upwards [hf] with ω hω
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [hz, ENNReal.zero_rpow_of_neg hq] at hω
  exact (lt_irrefl _ hω)

/-- A finite strictly positive moment implies almost sure finite reflection mass. -/
theorem twoSidedReflectionMass_finite_ae_of_positive_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) (hq : 0 < q)
    (hm : (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) < ⊤) :
    ∀ᵐ ω ∂P, twoSidedReflectionMass γ B Z ω < ⊤ := by
  have hf := ae_lt_top' (twoSidedReflectionMass_rpow_aemeasurable_of_lateral
    P γ q B Z hB hZ) hm.ne
  filter_upwards [hf] with ω hω
  apply lt_top_iff_ne_top.mpr
  intro hz
  rw [hz, ENNReal.top_rpow_of_pos hq] at hω
  exact lt_irrefl _ hω

/-- Two enclosing moment bounds control every intervening reflection moment. -/
theorem twoSidedReflectionMass_moment_le_endpoints
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ l u q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z)
    (hl : l ≤ q) (hu : q ≤ u) :
    (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) ≤
      (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ l ∂P) +
        (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ u ∂P) := by
  exact lintegral_rpow_le_endpoint_sum P _
    (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hB hZ) hl hu

/-- The two conditioned-process clauses already imply AE measurability of the whole path pair. -/
theorem conditionedPair_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath × BrownianPath) (ν : ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) : AEMeasurable B P :=
  hB.1.1.prodMk hB.2.1.1

/-- Endpoint moment bounds assemble the exact uniform moment conclusion for a family of
reflection data. The enclosing orders and their bounds are supplied explicitly. -/
theorem twoSidedReflectionMass_uniform_moments_of_endpoints
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν Kq : Set ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (l u : ℝ) (hl : ∀ q ∈ Kq, l ≤ q) (hu : ∀ q ∈ Kq, q ≤ u)
    (Cl Cu : ℝ≥0∞) (hCl : Cl < ⊤) (hCu : Cu < ⊤)
    (hLower : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (twoSidedReflectionMass γ (B ν) (Z γ) ω) ^ l ∂P) ≤ Cl)
    (hUpper : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (twoSidedReflectionMass γ (B ν) (Z γ) ω) ^ u ∂P) ≤ Cu) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (twoSidedReflectionMass γ (B ν) (Z γ) ω) ^ q ∂P) ≤ C := by
  refine ⟨Cl + Cu, ENNReal.add_lt_top.mpr ⟨hCl, hCu⟩, ?_⟩
  intro γ hγ ν hν q hq
  have hd := hData γ hγ ν hν
  exact (twoSidedReflectionMass_moment_le_endpoints P γ l u q (B ν) (Z γ)
    (conditionedPair_aemeasurable P (B ν) ν hd.1) hd.2.1 (hl q hq) (hu q hq)).trans
    (add_le_add (hLower γ hγ ν hν) (hUpper γ hγ ν hν))


/-- Positivity can also be transferred directly from an almost surely positive initial
lateral block, without using independence or a conditioned radial law. -/
theorem twoSidedReflectionMass_pos_ae_of_initialBlock
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (T : ℝ≥0)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hBlock : ∀ᵐ ω ∂P, 0 < Z ω (Ioc 0 (T : ℝ))) :
    ∀ᵐ ω ∂P, 0 < twoSidedReflectionMass γ B Z ω := by
  filter_upwards [hBlock] with ω hω
  exact lt_of_lt_of_le
    (ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) hω.ne')
    (twoSidedReflectionMass_initialBlock_lower γ T B Z ω)


/-- Concavity bounds every moment between zero and one by the full first moment. -/
theorem twoSidedReflectionMass_subunit_moment_le_mean
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) ≤
      (∫⁻ ω, twoSidedReflectionMass γ B Z ω ∂P) ^ q := by
  exact lintegral_rpow_le_mean_rpow P hZ.2.2.1 _
    (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hB hZ) q hq0 hq1






end DOZZ.Proofs
