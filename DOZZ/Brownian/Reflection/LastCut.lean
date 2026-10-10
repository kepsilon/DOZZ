/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import DOZZ.Brownian.Reflection.Moments
public import DOZZ.Statements.Brownian.TwoSidedReflectionCutMass
public import DOZZ.Brownian.ReflectionMassMeasurability
public import DOZZ.Brownian.MeasureTranslationFinite
public import DOZZ.Brownian.ReflectionLastCutShift
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import DOZZ.Brownian.Williams.StoppedPaths
import Mathlib.Topology.Hom.ContinuousEval

/-!
# The last-cut estimate for the two-sided reflection mass

Cutting at the negative-side last exit from `-c` discards exactly `exp(-γ c) D_c`, where `D_c` is
the half-line mass of the post-last-exit path against the reflected translated lateral measure
(`ReflectionLastCutShift`). The post-last-exit law and the random translation give `D_c` the law
of an entrance half-line mass, so its moments are uniform. No independence between the retained
and discarded masses is used. The increment steps are Bernoulli's inequality: the derivative at
the left endpoint for orders at most one, at the right endpoint for orders at least one; Hölder
then needs an inverse moment of the retained mass (through the initial unit block) or a positive
moment of the full mass.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Concavity increment for subunit powers: `(x + d)^p ≤ x^p + p d x^{p-1}`. -/
theorem ennreal_rpow_add_le_of_le_one {x d : ℝ≥0∞} (hx0 : 0 < x) (hx : x < ⊤) (hd : d < ⊤)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (x + d) ^ p ≤ x ^ p + ENNReal.ofReal p * d * x ^ (p - 1) := by
  obtain ⟨a, ha, rfl⟩ : ∃ a : ℝ, 0 < a ∧ x = ENNReal.ofReal a :=
    ⟨x.toReal, ENNReal.toReal_pos hx0.ne' hx.ne, (ENNReal.ofReal_toReal hx.ne).symm⟩
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 ≤ e ∧ d = ENNReal.ofReal e :=
    ⟨d.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hd.ne).symm⟩
  have hae : 0 < a + e := by linarith only [ha, he]
  have hL : (ENNReal.ofReal a + ENNReal.ofReal e) ^ p = ENNReal.ofReal ((a + e) ^ p) := by
    rw [← ENNReal.ofReal_add ha.le he]
    exact ENNReal.ofReal_rpow_of_pos hae
  have hR : ENNReal.ofReal a ^ p + ENNReal.ofReal p * ENNReal.ofReal e * ENNReal.ofReal a ^ (p - 1)
      = ENNReal.ofReal (a ^ p + p * e * a ^ (p - 1)) := by
    rw [ENNReal.ofReal_add (Real.rpow_nonneg ha.le p)
        (mul_nonneg (mul_nonneg hp.le he) (Real.rpow_nonneg ha.le _)),
      ENNReal.ofReal_mul (mul_nonneg hp.le he), ENNReal.ofReal_mul hp.le,
      ENNReal.ofReal_rpow_of_pos ha, ENNReal.ofReal_rpow_of_pos ha]
  rw [hL, hR]
  apply ENNReal.ofReal_le_ofReal
  linarith [real_rpow_add_increment_le_subunit a e p ha he hp hp1]

/-- Convexity increment for superunit powers: `(x + d)^p ≤ x^p + p d (x + d)^{p-1}`. -/
theorem ennreal_rpow_add_le_of_one_le {x d : ℝ≥0∞} (hx0 : 0 < x) (hx : x < ⊤) (hd : d < ⊤)
    {p : ℝ} (hp1 : 1 ≤ p) :
    (x + d) ^ p ≤ x ^ p + ENNReal.ofReal p * d * (x + d) ^ (p - 1) := by
  obtain ⟨a, ha', rfl⟩ : ∃ a : ℝ, 0 < a ∧ x = ENNReal.ofReal a :=
    ⟨x.toReal, ENNReal.toReal_pos hx0.ne' hx.ne, (ENNReal.ofReal_toReal hx.ne).symm⟩
  have ha : 0 ≤ a := ha'.le
  obtain ⟨e, he, rfl⟩ : ∃ e : ℝ, 0 ≤ e ∧ d = ENNReal.ofReal e :=
    ⟨d.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hd.ne).symm⟩
  have hp0 : 0 ≤ p := by linarith only [hp1]
  have hp10 : 0 ≤ p - 1 := by linarith only [hp1]
  have hae : 0 ≤ a + e := by linarith only [ha, he]
  have hL : (ENNReal.ofReal a + ENNReal.ofReal e) ^ p = ENNReal.ofReal ((a + e) ^ p) := by
    rw [← ENNReal.ofReal_add ha he]
    exact ENNReal.ofReal_rpow_of_nonneg hae hp0
  have hR : ENNReal.ofReal a ^ p + ENNReal.ofReal p * ENNReal.ofReal e *
        (ENNReal.ofReal a + ENNReal.ofReal e) ^ (p - 1)
      = ENNReal.ofReal (a ^ p + p * e * (a + e) ^ (p - 1)) := by
    rw [← ENNReal.ofReal_add ha he,
      ENNReal.ofReal_add (Real.rpow_nonneg ha p)
        (mul_nonneg (mul_nonneg hp0 he) (Real.rpow_nonneg hae _)),
      ENNReal.ofReal_mul (mul_nonneg hp0 he), ENNReal.ofReal_mul hp0,
      ENNReal.ofReal_rpow_of_nonneg ha hp0, ENNReal.ofReal_rpow_of_nonneg hae hp10]
  rw [hL, hR]
  apply ENNReal.ofReal_le_ofReal
  linarith [real_rpow_add_increment_le_superunit a e p ha' he hp1]

/-- The retained cut mass never exceeds the full mass. -/
theorem twoSidedReflectionCutMass_le_mass {Ω : Type*} (γ c : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    twoSidedReflectionCutMass γ c B Z ω ≤ twoSidedReflectionMass γ B Z ω := by
  unfold twoSidedReflectionCutMass twoSidedReflectionMass
  refine lintegral_mono fun s => ?_
  beta_reduce
  split_ifs
  · exact le_rfl
  · exact zero_le

/-- The retained cut mass contains the initial positive unit block. -/
theorem initialUnitBlockMass_le_cutMass {Ω : Type*} (γ c : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    initialUnitBlockMass γ (B ω).1 (Z ω) ≤ twoSidedReflectionCutMass γ c B Z ω := by
  unfold initialUnitBlockMass twoSidedReflectionCutMass
  refine lintegral_mono fun t => ?_
  beta_reduce
  by_cases ht : 0 ≤ t ∧ t ≤ 1
  · have hcut : -((negativeLastExitTime (B ω).2 c : ℝ)) ≤ t :=
      (neg_nonpos.mpr (NNReal.coe_nonneg _)).trans ht.1
    simp only [ht, hcut, and_self, dite_true, ite_true, twoSidedConditionedValue]
    exact le_rfl
  · simp [ht]

/-- The joined value of a pair of entrance paths is jointly measurable in the pair and the signed
time. -/
theorem measurable_uncurry_reflectionPairValue :
    Measurable (Function.uncurry reflectionPairValue) := by
  classical
  have heval : Measurable (fun z : (ℝ≥0 × BrownianPath) => z.2 z.1) :=
    by exact (continuous_eval.comp continuous_swap).measurable
  let pos : (BrownianPath × BrownianPath) × ℝ → ℝ := fun z =>
    z.1.1 ⟨max z.2 0, le_max_right _ _⟩
  let neg : (BrownianPath × BrownianPath) × ℝ → ℝ := fun z =>
    z.1.2 ⟨max (-z.2) 0, le_max_right _ _⟩
  have hpos : Measurable pos := by
    dsimp [pos]
    exact heval.comp ((by fun_prop : Measurable fun z : (BrownianPath × BrownianPath) × ℝ =>
      ((⟨max z.2 0, le_max_right _ _⟩ : ℝ≥0), z.1.1)))
  have hneg : Measurable neg := by
    dsimp [neg]
    exact heval.comp ((by fun_prop : Measurable fun z : (BrownianPath × BrownianPath) × ℝ =>
      ((⟨max (-z.2) 0, le_max_right _ _⟩ : ℝ≥0), z.1.2)))
  have hm : Measurable (fun z : (BrownianPath × BrownianPath) × ℝ =>
      if 0 ≤ z.2 then pos z else neg z) :=
    Measurable.ite (measurableSet_le measurable_const measurable_snd) hpos hneg
  convert hm using 1
  funext z
  change (if hs : 0 ≤ z.2 then z.1.1 ⟨z.2, hs⟩ else z.1.2 ⟨-z.2, by linarith⟩) =
    (if 0 ≤ z.2 then pos z else neg z)
  by_cases hs : 0 ≤ z.2
  · simp [hs, pos]
  · have hneg : 0 ≤ -z.2 := by linarith
    simp [hs, neg, max_eq_left hneg]

/-- The cut integrand: the exponential of the joined value, kept only to the right of `-L`, where
`L` is the last exit time of the negative-side path from `-c`. -/
noncomputable def reflectionCutIntegrand (γ c : ℝ)
    (z : (BrownianPath × BrownianPath) × ℝ) : ℝ≥0∞ :=
  if -((negativeLastExitTime z.1.2 c : ℝ)) ≤ z.2 then
    ENNReal.ofReal (Real.exp (γ * reflectionPairValue z.1 z.2)) else 0

/-- The cut integrand is jointly measurable in the path pair and the signed time. -/
theorem measurable_reflectionCutIntegrand (γ c : ℝ) :
    Measurable (reflectionCutIntegrand γ c) := by
  have hexit : Measurable (fun z : (BrownianPath × BrownianPath) × ℝ =>
      negativeLastExitTime z.1.2 c) :=
    measurable_negativeLastExitTime_joint.comp
      (measurable_const.prodMk (measurable_snd.comp measurable_fst))
  have hval : Measurable (fun z : (BrownianPath × BrownianPath) × ℝ =>
      reflectionPairValue z.1 z.2) := measurable_uncurry_reflectionPairValue
  exact Measurable.ite (measurableSet_le hexit.coe_nnreal_real.neg measurable_snd)
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hval)))
    measurable_const

/-- The contribution of one finite translation shell to the cut mass. -/
noncomputable def reflectionCutShell (γ c : ℝ) (n : ℕ)
    (z : (BrownianPath × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s, reflectionCutIntegrand γ c (z.1, s) ∂
    (finiteRestrictionOnSet (translationShell n) z.2 : Measure ℝ)

/-- Each shell contribution is jointly measurable in the path pair and the lateral measure. -/
theorem measurable_reflectionCutShell (γ c : ℝ) (n : ℕ) :
    Measurable (reflectionCutShell γ c n) := by
  have hInt := measurable_lintegral_finiteMeasure_parameter
    (f := reflectionCutIntegrand γ c) (measurable_reflectionCutIntegrand γ c)
  have hrest : Measurable (fun z : (BrownianPath × BrownianPath) × Measure ℝ =>
      finiteRestrictionOnSet (translationShell n) z.2) :=
    (measurable_finiteRestrictionOnSet _ (measurableSet_translationShell n)).comp
      measurable_snd
  have hpair : Measurable (fun z : (BrownianPath × BrownianPath) × Measure ℝ =>
      (z.1, finiteRestrictionOnSet (translationShell n) z.2)) :=
    measurable_fst.prodMk hrest
  exact hInt.comp hpair

/-- Integrating against a measure that is finite on every translation shell is the sum of the
integrals against the finite restrictions to the shells. -/
theorem lintegral_eq_tsum_finiteRestrictionOnSet_translationShell
    (f : ℝ → ℝ≥0∞) (μ : Measure ℝ) (hfin : ∀ n : ℕ, μ (translationShell n) < ⊤) :
    ∫⁻ s, f s ∂μ =
      ∑' n : ℕ, ∫⁻ s, f s ∂(finiteRestrictionOnSet (translationShell n) μ : Measure ℝ) := by
  have hshell (n : ℕ) : (finiteRestrictionOnSet (translationShell n) μ : Measure ℝ) =
      μ.restrict (translationShell n) := by
    simp [finiteRestrictionOnSet, hfin n]
  have hdecomp : Measure.sum (fun n => μ.restrict (translationShell n)) = μ := by
    rw [← Measure.restrict_iUnion translationShell_pairwise_disjoint
      (fun n => measurableSet_translationShell n), translationShell_iUnion,
      Measure.restrict_univ]
  calc ∫⁻ s, f s ∂μ
      = ∫⁻ s, f s ∂Measure.sum (fun n => μ.restrict (translationShell n)) := by
        rw [hdecomp]
    _ = ∑' n : ℕ, ∫⁻ s, f s ∂μ.restrict (translationShell n) :=
        lintegral_sum_measure f _
    _ = _ := tsum_congr fun n => by rw [hshell n]

/-- The cut mass is almost everywhere measurable for a.e.-measurable inputs whose lateral
measure is almost surely finite on bounded intervals. -/
theorem twoSidedReflectionCutMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (γ c : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) :
    AEMeasurable (fun ω => twoSidedReflectionCutMass γ c B Z ω) P := by
  have hpair : AEMeasurable (fun ω => (B ω, Z ω)) P := hB.prodMk hZ
  have hsum : AEMeasurable
      (fun ω => ∑' n : ℕ, reflectionCutShell γ c n (B ω, Z ω)) P :=
    AEMeasurable.tsum fun n =>
      (measurable_reflectionCutShell γ c n).comp_aemeasurable hpair
  refine hsum.congr ?_
  filter_upwards [hfin] with ω hω
  have hshell (n : ℕ) : Z ω (translationShell n) < ⊤ :=
    lt_of_le_of_lt (measure_mono (translationShell_subset_window n)) (hω _ _)
  exact (lintegral_eq_tsum_finiteRestrictionOnSet_translationShell
    (fun s => reflectionCutIntegrand γ c (B ω, s)) (Z ω) hshell).symm

/-- Finiteness on the standard windows gives finiteness on every bounded interval. -/
theorem measure_Ioc_lt_top_of_locallyFinite {μ : Measure ℝ}
    (h : LocallyFiniteOnTranslationWindows μ) (a b : ℝ) : μ (Ioc a b) < ⊤ := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max |a| |b|)
  refine lt_of_le_of_lt (measure_mono ?_) (h n)
  intro x hx
  have ha : |a| ≤ n := (le_max_left _ _).trans hn
  have hb : |b| ≤ n := (le_max_right _ _).trans hn
  constructor
  · have := neg_abs_le a
    linarith [hx.1]
  · have := le_abs_self b
    linarith [hx.2]

/-- The discarded post-last-exit half-line mass has the moments of the entrance half-line mass of
the negative-side path. -/
theorem postLastExit_entranceMass_rpow_lintegral_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (ν γ c q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsNegativeConditionedBrownianProcess P (fun ω => (B ω).2) ν)
    (hν : 0 < ν) (hc : 0 < c) (hZ : IsLateralGMCOf P γ Z) (hInd : IndepFun B Z P) :
    (∫⁻ ω, (positiveLateralMass γ (negativeConditionedPostLastExitPath c (B ω).2)
        (lastExitReflectedMeasure c B Z ω)) ^ q ∂P) =
      ∫⁻ ω, (positiveLateralMass γ (B ω).2 (Z ω)) ^ q ∂P := by
  have hlaw := postLastExit_reflectedJointLaw_eq P ν γ c B Z hB hν hc hZ hInd
  let pair₁ : Ω → BrownianPath × Measure ℝ := fun ω =>
    (negativeConditionedPostLastExitPath c (B ω).2, lastExitReflectedMeasure c B Z ω)
  let pair₂ : Ω → BrownianPath × Measure ℝ := fun ω => ((B ω).2, Z ω)
  let F : BrownianPath × Measure ℝ → ℝ≥0∞ := fun z => (positiveLateralMass γ z.1 z.2) ^ q
  have hpair₂ : AEMeasurable pair₂ P := hB.1.prodMk hZ.2.2.2.1
  have hIndDZ : IndepFun (fun ω => (B ω).2) Z P := hInd.comp measurable_snd measurable_id
  have hpair₁ : AEMeasurable pair₁ P :=
    ((measurable_negativeConditionedPostLastExitPath c).comp_aemeasurable hB.1).prodMk
      (lastExitReflectedMeasure_law_independent P γ c B Z hB.1 hZ hIndDZ).1
  have hset : MeasurableSet {z : BrownianPath × Measure ℝ |
      LocallyFiniteOnTranslationWindows z.2} :=
    measurableSet_locallyFiniteOnTranslationWindows.preimage measurable_snd
  have hloc : ∀ᵐ z ∂(P.map pair₂), LocallyFiniteOnTranslationWindows z.2 := by
    refine (ae_map_iff hpair₂ hset).mpr ?_
    filter_upwards [hZ.2.2.2.2.1] with ω hω n
    exact hω _ _
  have hfin : ∀ᵐ z ∂(P.map pair₂), ∀ a b : ℝ, z.2 (Ioc a b) < ⊤ := by
    filter_upwards [hloc] with z hz a b
    exact measure_Ioc_lt_top_of_locallyFinite hz a b
  have hF : AEMeasurable F (P.map pair₂) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (positiveLateralMass_aemeasurable_of_finite (P.map pair₂) γ Prod.fst Prod.snd
        measurable_fst.aemeasurable measurable_snd.aemeasurable hfin)
  have hF' : AEMeasurable F (P.map pair₁) := by
    change AEMeasurable F (P.map (fun ω =>
      (negativeConditionedPostLastExitPath c (B ω).2, lastExitReflectedMeasure c B Z ω)))
    rw [hlaw]
    exact hF
  calc (∫⁻ ω, (positiveLateralMass γ (negativeConditionedPostLastExitPath c (B ω).2)
        (lastExitReflectedMeasure c B Z ω)) ^ q ∂P)
      = ∫⁻ ω, F (pair₁ ω) ∂P := rfl
    _ = ∫⁻ z, F z ∂P.map pair₁ := (lintegral_map' hF' hpair₁).symm
    _ = ∫⁻ z, F z ∂P.map pair₂ := by
        change (∫⁻ z, F z ∂P.map (fun ω =>
          (negativeConditionedPostLastExitPath c (B ω).2, lastExitReflectedMeasure c B Z ω))) = _
        rw [hlaw]
    _ = ∫⁻ ω, F (pair₂ ω) ∂P := lintegral_map' hF hpair₂
    _ = _ := rfl

/-- The discarded post-last-exit mass, as a function of the sample. -/
noncomputable def lastCutDiscardMass {Ω : Type*} (γ c : ℝ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (ω : Ω) : ℝ≥0∞ :=
  positiveLateralMass γ (negativeConditionedPostLastExitPath c (B ω).2)
    (lastExitReflectedMeasure c B Z ω)

/-- The full mass is the retained cut mass plus `exp(-γ c)` times the discarded mass. -/
theorem twoSidedReflectionMass_eq_cut_add_discard {Ω : Type*} (γ c : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω) :
    twoSidedReflectionMass γ B Z ω = twoSidedReflectionCutMass γ c B Z ω +
      ENNReal.ofReal (Real.exp (-γ * c)) * lastCutDiscardMass γ c B Z ω := by
  rw [twoSidedReflectionMass_eq_cut_add_tail γ c B Z ω,
    twoSidedReflectionTailMass_eq_postLastExit_entranceMass γ c B Z ω]
  rfl

/-- Reflection and translation keep bounded intervals finite. -/
theorem lastExitReflectedMeasure_Ioc_lt_top {Ω : Type*} (c : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) (ω : Ω)
    (hZ : ∀ a b : ℝ, Z ω (Icc a b) < ⊤) (a b : ℝ) :
    lastExitReflectedMeasure c B Z ω (Ioc a b) < ⊤ := by
  unfold lastExitReflectedMeasure
  have hg : Measurable (fun s : ℝ => -s - (negativeLastExitTime (B ω).2 c : ℝ)) := by fun_prop
  rw [Measure.map_apply hg measurableSet_Ioc]
  refine lt_of_le_of_lt (measure_mono ?_) (hZ (-b - (negativeLastExitTime (B ω).2 c : ℝ))
    (-a - (negativeLastExitTime (B ω).2 c : ℝ)))
  intro s hs
  simp only [mem_preimage, mem_Ioc] at hs
  constructor <;> linarith [hs.1, hs.2]

/-- The discarded mass is almost everywhere measurable for conditioned reflection inputs. -/
theorem lastCutDiscardMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ c : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable (fun ω => (B ω).2) P) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun (fun ω => (B ω).2) Z P) :
    AEMeasurable (fun ω => lastCutDiscardMass γ c B Z ω) P := by
  have hpost : AEMeasurable (fun ω => negativeConditionedPostLastExitPath c (B ω).2) P :=
    (measurable_negativeConditionedPostLastExitPath c).comp_aemeasurable hB
  have hrefl := (lastExitReflectedMeasure_law_independent P γ c B Z hB hZ hInd).1
  have hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, lastExitReflectedMeasure c B Z ω (Ioc a b) < ⊤ := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω a b
    exact lastExitReflectedMeasure_Ioc_lt_top c B Z ω hω a b
  exact positiveLateralMass_aemeasurable_of_finite P γ _ _ hpost hrefl hfin


/-- Hölder bound for a product of a mass and a real power of another mass, with conjugate
exponents `r` and `r/(r-1)`. -/
theorem lintegral_mul_rpow_le_holder {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D X : Ω → ℝ≥0∞) (hD : AEMeasurable D P) (hX : AEMeasurable X P) (r e : ℝ) (hr : 1 < r) :
    (∫⁻ ω, D ω * X ω ^ e ∂P) ≤
      (∫⁻ ω, D ω ^ r ∂P) ^ (1 / r) *
        (∫⁻ ω, X ω ^ (e * (r / (r - 1))) ∂P) ^ (1 / (r / (r - 1))) := by
  have hconj : r.HolderConjugate (r / (r - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hr).mpr rfl
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj hD (hX.pow_const e)
  have heq : (∫⁻ ω, (X ω ^ e) ^ (r / (r - 1)) ∂P) = ∫⁻ ω, X ω ^ (e * (r / (r - 1))) ∂P := by
    apply lintegral_congr
    intro ω
    rw [← ENNReal.rpow_mul]
  simpa only [Pi.mul_apply, heq] using h

/-- One-step moment increment across the last cut, for a single order `p`, from three moment
bounds: the discarded mass at order `r`, the retained mass at the negative order `(p-1) r'`
(subunit `p`) and the full mass at order `(p-1) r'` (superunit `p`). -/
theorem lastCut_moment_le_add
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (k : ℝ≥0∞) (hk : k < ⊤)
    (J Jc D : Ω → ℝ≥0∞) (hJ : AEMeasurable J P) (hJc : AEMeasurable Jc P)
    (hD : AEMeasurable D P) (hsplit : ∀ᵐ ω ∂P, J ω = Jc ω + k * D ω)
    (hJcpos : ∀ᵐ ω ∂P, 0 < Jc ω) (hJfin : ∀ᵐ ω ∂P, J ω < ⊤) (hDfin : ∀ᵐ ω ∂P, D ω < ⊤)
    (p r : ℝ) (hp : 0 < p) (hr : 1 < r) :
    (∫⁻ ω, J ω ^ p ∂P) ≤ (∫⁻ ω, Jc ω ^ p ∂P) +
      ENNReal.ofReal p * k * ((∫⁻ ω, D ω ^ r ∂P) ^ (1 / r) *
        (∫⁻ ω, (if p ≤ 1 then Jc ω else J ω) ^ ((p - 1) * (r / (r - 1))) ∂P) ^
          (1 / (r / (r - 1)))) := by
  set G : Ω → ℝ≥0∞ := fun ω => if p ≤ 1 then Jc ω else J ω with hG
  have hGm : AEMeasurable G P := by
    by_cases hp1 : p ≤ 1
    · simpa [hG, hp1] using hJc
    · simpa [hG, hp1] using hJ
  have hpoint : ∀ᵐ ω ∂P, J ω ^ p ≤ Jc ω ^ p + ENNReal.ofReal p * k * (D ω * G ω ^ (p - 1)) := by
    filter_upwards [hsplit, hJcpos, hJfin, hDfin] with ω hs hpos hfin hdfin
    have hJcfin : Jc ω < ⊤ := lt_of_le_of_lt (by rw [hs]; exact le_self_add) hfin
    have hkd : k * D ω < ⊤ := ENNReal.mul_lt_top hk hdfin
    by_cases hp1 : p ≤ 1
    · have h := ennreal_rpow_add_le_of_le_one hpos hJcfin hkd hp hp1
      have hGJ : G ω = Jc ω := by simp only [hG, hp1, ite_true]
      calc J ω ^ p = (Jc ω + k * D ω) ^ p := by rw [hs]
        _ ≤ Jc ω ^ p + ENNReal.ofReal p * (k * D ω) * Jc ω ^ (p - 1) := h
        _ = Jc ω ^ p + ENNReal.ofReal p * k * (D ω * G ω ^ (p - 1)) := by
          rw [hGJ]
          ring
    · have h := ennreal_rpow_add_le_of_one_le hpos hJcfin hkd (le_of_lt (not_le.mp hp1))
      have hGJ : G ω = J ω := by simp only [hG, hp1, ite_false]
      calc J ω ^ p = (Jc ω + k * D ω) ^ p := by rw [hs]
        _ ≤ Jc ω ^ p + ENNReal.ofReal p * (k * D ω) * (Jc ω + k * D ω) ^ (p - 1) := h
        _ = Jc ω ^ p + ENNReal.ofReal p * k * (D ω * G ω ^ (p - 1)) := by
          rw [hGJ, ← hs]
          ring
  calc (∫⁻ ω, J ω ^ p ∂P)
      ≤ ∫⁻ ω, Jc ω ^ p + ENNReal.ofReal p * k * (D ω * G ω ^ (p - 1)) ∂P :=
        lintegral_mono_ae hpoint
    _ = (∫⁻ ω, Jc ω ^ p ∂P) + ENNReal.ofReal p * k * ∫⁻ ω, D ω * G ω ^ (p - 1) ∂P := by
        have hDG : AEMeasurable (fun ω => D ω * G ω ^ (p - 1)) P := hD.mul (hGm.pow_const _)
        rw [lintegral_add_left' (hJc.pow_const p), lintegral_const_mul'' _ hDG]
    _ ≤ _ := by
        gcongr
        exact lintegral_mul_rpow_le_holder P D G hD hGm r (p - 1) hr


/-- Negative powers of order `w ≤ w₀` are controlled by `1 + x^(-w₀)`. -/
theorem ennreal_rpow_neg_le_one_add (x : ℝ≥0∞) {w w₀ : ℝ} (hw : 0 ≤ w) (hww₀ : w ≤ w₀) :
    x ^ (-w) ≤ 1 + x ^ (-w₀) := by
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg, ← ENNReal.inv_rpow, ← ENNReal.inv_rpow]
  exact ennreal_rpow_le_one_add_rpow _ hw hww₀

/-- A finite negative moment forces almost-sure positivity. -/
theorem ae_pos_of_lintegral_rpow_neg_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ≥0∞} (hX : AEMeasurable X P) {w : ℝ} (hw : 0 < w)
    (h : (∫⁻ ω, X ω ^ (-w) ∂P) < ⊤) : ∀ᵐ ω ∂P, 0 < X ω := by
  filter_upwards [ae_lt_top' (hX.pow_const _) h.ne] with ω hω
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0∞) ≤ X ω) with h0 | hpos
  · rw [← h0, ENNReal.zero_rpow_of_neg (by linarith)] at hω
    exact absurd hω (lt_irrefl _)
  · exact hpos

/-- A finite positive moment forces almost-sure finiteness. -/
theorem ae_lt_top_of_lintegral_rpow_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ≥0∞} (hX : AEMeasurable X P) {q : ℝ} (hq : 0 < q)
    (h : (∫⁻ ω, X ω ^ q ∂P) < ⊤) : ∀ᵐ ω ∂P, X ω < ⊤ := by
  filter_upwards [ae_lt_top' (hX.pow_const _) h.ne] with ω hω
  exact lt_top_iff_ne_top.mpr fun htop => by
    rw [htop, ENNReal.top_rpow_of_pos hq] at hω
    exact lt_irrefl _ hω

/-- The last-cut bound `DOZZ.reflectionMass_lastCut_bound`, from the lateral inverse unit
moments. -/
theorem reflectionMass_lastCut_bound_of_inverse
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (Kν Kp : Set ℝ)
    (hKν : IsCompact Kν) (hKp : IsCompact Kp)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν ∈ Kν,
      0 < ν ∧ IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν ∈ Kν, IndepFun (B ν) Z P)
    (hp : ∀ p ∈ Kp, 0 < p ∧ p < 4 / γ ^ 2)
    (hinv : ∀ v : ℝ, 0 < v → (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-v) ∂P) < ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ν ∈ Kν, ∀ p ∈ Kp, ∀ c : ℝ, 0 ≤ c →
        0 ≤
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) p ∂P).toReal -
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionCutMass γ c (B ν) Z ω) p ∂P).toReal ∧
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) p ∂P).toReal -
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionCutMass γ c (B ν) Z ω) p ∂P).toReal ≤
            C * Real.exp (-γ * c) := by
  rcases Kν.eq_empty_or_nonempty with hKν0 | hKν0
  · exact ⟨0, le_rfl, fun ν hν => by simp [hKν0] at hν⟩
  rcases Kp.eq_empty_or_nonempty with hKp0 | hKp0
  · exact ⟨0, le_rfl, fun _ _ p hpK => by simp [hKp0] at hpK⟩
  have hP : IsProbabilityMeasure P := hZ.2.2.1
  -- the compact parameter ranges
  set ν₁ := sInf Kν with hν₁def
  set ν₂ := sSup Kν with hν₂def
  set p₁ := sInf Kp with hp₁def
  set p₂ := sSup Kp with hp₂def
  have hν₁ : 0 < ν₁ := (hB ν₁ (hKν.sInf_mem hKν0)).1
  have hνb : ∀ ν ∈ Kν, ν₁ ≤ ν ∧ ν ≤ ν₂ := fun ν hν =>
    ⟨csInf_le hKν.bddBelow hν, le_csSup hKν.bddAbove hν⟩
  have hpb : ∀ p ∈ Kp, p₁ ≤ p ∧ p ≤ p₂ := fun p hpK =>
    ⟨csInf_le hKp.bddBelow hpK, le_csSup hKp.bddAbove hpK⟩
  have hp₁ : 0 < p₁ := (hp p₁ (hKp.sInf_mem hKp0)).1
  set M : ℝ := 4 / γ ^ 2 with hMdef
  have hp₂M : p₂ < M := (hp p₂ (hKp.sSup_mem hKp0)).2
  have hγsq : γ ^ 2 < 4 := by
    have := pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero
    linarith only [this]
  have hM1 : 1 < M := by
    rw [hMdef, lt_div_iff₀ (by positivity)]
    linarith
  have hp₁₂ : p₁ ≤ p₂ := (hpb p₁ (hKp.sInf_mem hKp0)).2
  -- the Hölder exponent and its conjugate
  have hden : 0 < M - p₂ + 1 := by linarith
  have hfrac : M / (M - p₂ + 1) < M := by
    rcases le_or_gt p₂ 1 with h | h
    · have : M / (M - p₂ + 1) ≤ M := div_le_self (by linarith) (by linarith)
      have hlt : M / (M - p₂ + 1) ≤ M / 1 := div_le_div_of_nonneg_left (by linarith) one_pos
        (by linarith)
      rcases eq_or_lt_of_le h with h1 | h1
      · rw [h1] at hden ⊢
        rw [show M - 1 + 1 = M by ring, div_self (by linarith)]
        exact hM1
      · rw [div_lt_iff₀ hden]
        linarith only [mul_pos (by linarith only [hM1] : (0 : ℝ) < M) (sub_pos.mpr hp₂M)]
    · rw [div_lt_iff₀ hden]
      linarith only [mul_pos (by linarith only [hM1] : (0 : ℝ) < M) (sub_pos.mpr hp₂M)]
  set r : ℝ := max ((1 + M) / 2) ((M / (M - p₂ + 1) + M) / 2) with hrdef
  have hr1 : 1 < r := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hrM : r < M := max_lt (by linarith) (by linarith)
  have hrfrac : M / (M - p₂ + 1) < r := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  set r' : ℝ := r / (r - 1) with hr'def
  have hr'0 : 0 < r' := div_pos (by linarith) (by linarith)
  -- top order of the full mass, and top inverse order of the retained mass
  set sTop : ℝ := max p₂ ((p₂ - 1) * r') with hsTopdef
  have hsTop : sTop < M := by
    refine max_lt hp₂M ?_
    rcases le_or_gt p₂ 1 with h | h
    · linarith only [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hr'0.le, hM1]
    · rw [hr'def, mul_div_assoc', div_lt_iff₀ (by linarith)]
      rw [div_lt_iff₀ hden] at hrfrac
      linarith only [hrfrac]
  have hsTop0 : 0 < sTop := lt_of_lt_of_le (lt_of_lt_of_le hp₁ hp₁₂) (le_max_left _ _)
  set wTop : ℝ := max 1 ((1 - p₁) * r') with hwTopdef
  have hwTop0 : 0 < wTop := lt_of_lt_of_le one_pos (le_max_left _ _)
  -- uniform moment bounds
  obtain ⟨CJ, hCJ, hCJb⟩ := twoSidedReflectionMass_rpow_lintegral_le_compact P γ ν₁ ν₂ sTop
    hγ hν₁ hsTop0 hsTop Z hZ
  have hZfinIoc : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤ := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω a b
    exact lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self) (hω a b)
  have hLr : (∫⁻ ω, (Z ω (Ioc 0 1)) ^ r ∂P) < ⊤ :=
    lateralGMC_interval_nonnegative_moment_finite P γ Z hZ 0 1 r (by linarith) hrM
  have hLrb : ∀ n : ℕ, (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ r ∂P) ≤
      ∫⁻ ω, (Z ω (Ioc 0 1)) ^ r ∂P := by
    intro n
    have h := lateralGMC_interval_moment_translation_eq P γ Z hZ 0 1 r (n : ℝ)
    simp only [zero_add] at h
    rw [add_comm 1 (n : ℝ)] at h
    exact h.le
  obtain ⟨CD, hCD, hCDb⟩ := positiveLateralMass_rpow_lintegral_le_compact_drift P γ ν₁ ν₂ r
    hγ hν₁ (by linarith) Z hZ.2.2.2.1 hZfinIoc _ hLr hLrb
  obtain ⟨C0, hC0, hC0b⟩ := initialUnitBlockMass_inverse_moment_le P γ ν₂ wTop hγ hwTop0 Z
    hZ.2.2.2.1 hZ.2.2.2.2.1
  set CI : ℝ≥0∞ := 1 + C0 * ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-wTop) ∂P with hCIdef
  have hCI : CI < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
    ENNReal.mul_lt_top hC0 (hinv wTop hwTop0)⟩
  set A : ℝ≥0∞ := ENNReal.ofReal p₂ * (CD ^ (1 / r) * (max CI CJ) ^ (1 / r')) with hAdef
  have hA : A < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) hCD.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (max_lt hCI hCJ).ne))
  refine ⟨max CJ.toReal A.toReal, le_max_of_le_left ENNReal.toReal_nonneg, ?_⟩
  intro ν hν p hpK c hc
  obtain ⟨hν0, hBν⟩ := hB ν hν
  have hνr := hνb ν hν
  have hpr := hpb p hpK
  have hp0 : 0 < p := (hp p hpK).1
  set J : Ω → ℝ≥0∞ := fun ω => twoSidedReflectionMass γ (B ν) Z ω with hJdef
  set Jc : Ω → ℝ≥0∞ := fun ω => twoSidedReflectionCutMass γ c (B ν) Z ω with hJcdef
  have hJm : AEMeasurable J P := twoSidedReflectionMass_aemeasurable_of_lateral P γ (B ν) Z
    (aemeasurable_of_twoSidedConditioned hBν) hZ
  have hJcm : AEMeasurable Jc P := twoSidedReflectionCutMass_aemeasurable P γ c (B ν) Z
    (aemeasurable_of_twoSidedConditioned hBν) hZ.2.2.2.1 hZ.2.2.2.2.1
  have hJpCJ : (∫⁻ ω, J ω ^ p ∂P) ≤ CJ :=
    hCJb ν hνr.1 hνr.2 p hp0.le (hpr.2.trans (le_max_left _ _)) (B ν) hBν (hInd ν hν)
  have hJp : (∫⁻ ω, J ω ^ p ∂P) < ⊤ := lt_of_le_of_lt hJpCJ hCJ
  have hJcle : (∫⁻ ω, Jc ω ^ p ∂P) ≤ ∫⁻ ω, J ω ^ p ∂P :=
    lintegral_mono fun ω => ENNReal.rpow_le_rpow
      (twoSidedReflectionCutMass_le_mass γ c (B ν) Z ω) hp0.le
  have hJcp : (∫⁻ ω, Jc ω ^ p ∂P) < ⊤ := lt_of_le_of_lt hJcle hJp
  refine ⟨sub_nonneg.mpr (ENNReal.toReal_mono hJp.ne hJcle), ?_⟩
  rcases eq_or_lt_of_le hc with hc0 | hcpos
  · -- no cut: the difference is at most the full moment
    have hexp : Real.exp (-γ * c) = 1 := by rw [← hc0, mul_zero, Real.exp_zero]
    rw [hexp, mul_one]
    calc (∫⁻ ω, J ω ^ p ∂P).toReal - (∫⁻ ω, Jc ω ^ p ∂P).toReal
        ≤ (∫⁻ ω, J ω ^ p ∂P).toReal := sub_le_self _ ENNReal.toReal_nonneg
      _ ≤ CJ.toReal := ENNReal.toReal_mono hCJ.ne hJpCJ
      _ ≤ max CJ.toReal A.toReal := le_max_left _ _
  · -- a genuine cut
    set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-γ * c)) with hkdef
    set D : Ω → ℝ≥0∞ := fun ω => lastCutDiscardMass γ c (B ν) Z ω with hDdef
    have hIndDZ : IndepFun (fun ω => (B ν ω).2) Z P := (hInd ν hν).comp measurable_snd measurable_id
    have hDm : AEMeasurable D P :=
      lastCutDiscardMass_aemeasurable P γ c (B ν) Z hBν.2.1.1 hZ hIndDZ
    have hDr : (∫⁻ ω, D ω ^ r ∂P) ≤ CD := by
      have he := postLastExit_entranceMass_rpow_lintegral_eq P ν γ c r (B ν) Z hBν.2.1 hν0
        hcpos hZ (hInd ν hν)
      change (∫⁻ ω, (positiveLateralMass γ (negativeConditionedPostLastExitPath c (B ν ω).2)
        (lastExitReflectedMeasure c (B ν) Z ω)) ^ r ∂P) ≤ CD
      rw [he]
      exact hCDb ν hνr.1 hνr.2 _ hBν.2.1 hIndDZ
    -- inverse moments of the retained mass through the initial block
    have hblock := hC0b ν hνr.2 (fun ω => (B ν ω).1) hBν.1
      ((hInd ν hν).comp measurable_fst measurable_id)
    have hblockm : AEMeasurable (fun ω => initialUnitBlockMass γ (B ν ω).1 (Z ω)) P :=
      initialUnitBlockMass_aemeasurable P γ _ Z hBν.1.1 hZ.2.2.2.1 hZ.2.2.2.2.1
    have hblockfin : (∫⁻ ω, (initialUnitBlockMass γ (B ν ω).1 (Z ω)) ^ (-wTop) ∂P) < ⊤ :=
      lt_of_le_of_lt hblock (ENNReal.mul_lt_top hC0 (hinv wTop hwTop0))
    have hJcpos : ∀ᵐ ω ∂P, 0 < Jc ω := by
      filter_upwards [ae_pos_of_lintegral_rpow_neg_lt_top hblockm hwTop0 hblockfin] with ω hω
      exact lt_of_lt_of_le hω (initialUnitBlockMass_le_cutMass γ c (B ν) Z ω)
    have hJcinv : ∀ w : ℝ, 0 ≤ w → w ≤ wTop → (∫⁻ ω, Jc ω ^ (-w) ∂P) ≤ CI := by
      intro w hw hwle
      calc (∫⁻ ω, Jc ω ^ (-w) ∂P)
          ≤ ∫⁻ ω, (initialUnitBlockMass γ (B ν ω).1 (Z ω)) ^ (-w) ∂P :=
            lintegral_mono fun ω => ennreal_rpow_antitone_nonpos _ _ _
              (initialUnitBlockMass_le_cutMass γ c (B ν) Z ω) (by linarith)
        _ ≤ ∫⁻ ω, 1 + (initialUnitBlockMass γ (B ν ω).1 (Z ω)) ^ (-wTop) ∂P :=
            lintegral_mono fun ω => ennreal_rpow_neg_le_one_add _ hw hwle
        _ = 1 + ∫⁻ ω, (initialUnitBlockMass γ (B ν ω).1 (Z ω)) ^ (-wTop) ∂P := by
            rw [lintegral_add_left measurable_const]
            simp
        _ ≤ CI := add_le_add le_rfl hblock
    have hsplit : ∀ᵐ ω ∂P, J ω = Jc ω + k * D ω := ae_of_all _ fun ω =>
      twoSidedReflectionMass_eq_cut_add_discard γ c (B ν) Z ω
    have hJfin := ae_lt_top_of_lintegral_rpow_lt_top hJm hp0 hJp
    have hDfin := ae_lt_top_of_lintegral_rpow_lt_top hDm (by linarith) (lt_of_le_of_lt hDr hCD)
    have hstep := lastCut_moment_le_add P k ENNReal.ofReal_lt_top J Jc D hJm hJcm hDm hsplit
      hJcpos hJfin hDfin p r hp0 hr1
    -- the Hölder bracket is at most `A`
    have hG : (∫⁻ ω, (if p ≤ 1 then Jc ω else J ω) ^ ((p - 1) * (r / (r - 1))) ∂P) ≤
        max CI CJ := by
      by_cases hp1 : p ≤ 1
      · simp only [hp1, ite_true]
        have hw : (p - 1) * (r / (r - 1)) = -((1 - p) * r') := by rw [hr'def]; ring
        rw [hw]
        refine (hJcinv _ (mul_nonneg (by linarith) hr'0.le) ?_).trans (le_max_left _ _)
        exact (mul_le_mul_of_nonneg_right (by linarith [hpr.1]) hr'0.le).trans (le_max_right _ _)
      · simp only [hp1, ite_false]
        refine le_trans ?_ (le_max_right _ _)
        exact hCJb ν hνr.1 hνr.2 _ (mul_nonneg (by linarith [not_le.mp hp1]) hr'0.le)
          ((mul_le_mul_of_nonneg_right (by linarith [hpr.2]) hr'0.le).trans (le_max_right _ _))
          (B ν) hBν (hInd ν hν)
    have hbracket : ENNReal.ofReal p * k * ((∫⁻ ω, D ω ^ r ∂P) ^ (1 / r) *
        (∫⁻ ω, (if p ≤ 1 then Jc ω else J ω) ^ ((p - 1) * (r / (r - 1))) ∂P) ^
          (1 / (r / (r - 1)))) ≤ k * A := by
      rw [hAdef, mul_comm (ENNReal.ofReal p) k, mul_assoc]
      refine mul_le_mul_right ?_ k
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal hpr.2) (mul_le_mul'
        (ENNReal.rpow_le_rpow hDr (by positivity)) (ENNReal.rpow_le_rpow hG (by positivity)))
    have hfinal : (∫⁻ ω, J ω ^ p ∂P) ≤ (∫⁻ ω, Jc ω ^ p ∂P) + k * A :=
      hstep.trans (add_le_add le_rfl hbracket)
    have hkA : k * A < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA
    have hreal := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨hJcp, hkA⟩).ne hfinal
    rw [ENNReal.toReal_add hJcp.ne hkA.ne, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le] at hreal
    calc (∫⁻ ω, J ω ^ p ∂P).toReal - (∫⁻ ω, Jc ω ^ p ∂P).toReal
        ≤ Real.exp (-γ * c) * A.toReal := by linarith
      _ ≤ max CJ.toReal A.toReal * Real.exp (-γ * c) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

end DOZZ.Proofs

end
