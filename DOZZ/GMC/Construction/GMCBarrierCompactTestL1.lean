/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCenteredJointlyGaussian
public import DOZZ.Statements.GMC.GaussianVariance
public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import DOZZ.GMC.FiniteChaosMean

/-! Uniform-barrier cutoff construction for compact GMC tests. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

noncomputable def gaussianRectangleIndicator {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c : ι → ℝ) : Ω → ℝ :=
  fun ω => if ∀ i, Z ω i + c i ≤ b i then 1 else 0

private theorem gaussianRectangleIndicator_aestronglyMeasurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b c : ι → ℝ) : AEStronglyMeasurable (gaussianRectangleIndicator Z b c) P := by
  let S : Set (ι → ℝ) := {z | ∀ i, z i + c i ≤ b i}
  have hS : MeasurableSet S := by
    have hEq : (⋂ i, {z : ι → ℝ | z i + c i ≤ b i}) = S := by
      ext z
      simp [S]
    rw [← hEq]
    apply MeasurableSet.iInter
    intro i
    have hcoord : Measurable (fun z : ι → ℝ => z i + c i) := by fun_prop
    exact measurableSet_le hcoord measurable_const
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro i
    exact hZ.2.1 i
  have hF : Measurable (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) :=
    Measurable.ite hS measurable_const measurable_const
  have hEq : gaussianRectangleIndicator Z b c =
      (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) ∘ Z := by
    funext ω
    rfl
  rw [hEq]
  exact hF.comp_aemeasurable hZae |>.aestronglyMeasurable

private noncomputable def gaussianRectangleShiftBandIndicator
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c d : ι → ℝ) (i : ι) : Ω → ℝ :=
  Set.indicator {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
      (max (b i - c i) (b i - d i))} (fun _ => (1 : ℝ))

private theorem gaussianRectangleShiftBandIndicator_nonneg
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c d : ι → ℝ) (i : ι) (ω : Ω) :
    0 ≤ gaussianRectangleShiftBandIndicator Z b c d i ω := by
  change 0 ≤ Set.indicator {ω' | Z ω' i ∈ Set.Icc
    (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i))}
    (fun _ => (1 : ℝ)) ω
  by_cases hi : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
      (max (b i - c i) (b i - d i))
  · have hi' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} := hi
    rw [Set.indicator_of_mem hi']
    norm_num
  · have hi' : ω ∉ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} := hi
    rw [Set.indicator_of_notMem hi']

private theorem gaussianRectangleShiftBandIndicator_aestronglyMeasurable
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b c d : ι → ℝ) (i : ι) :
    AEStronglyMeasurable (gaussianRectangleShiftBandIndicator Z b c d i) P := by
  let S : Set (ι → ℝ) := {z | z i ∈ Set.Icc (min (b i - c i) (b i - d i))
    (max (b i - c i) (b i - d i))}
  have hS : MeasurableSet S := by
    change MeasurableSet ((fun z : ι → ℝ => z i) ⁻¹'
      Set.Icc (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i)))
    exact isClosed_Icc.measurableSet.preimage (measurable_pi_apply i)
  have hZae : AEMeasurable Z P := by
    apply AEMeasurable.of_eval
    intro j
    exact hZ.2.1 j
  have hF : Measurable (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) :=
    Measurable.ite hS measurable_const measurable_const
  have hEq : gaussianRectangleShiftBandIndicator Z b c d i =
      (fun z : ι → ℝ => if z ∈ S then (1 : ℝ) else 0) ∘ Z := by
    funext ω
    simp [S, gaussianRectangleShiftBandIndicator, Set.indicator]
  rw [hEq]
  exact hF.comp_aemeasurable hZae |>.aestronglyMeasurable

private theorem gaussianRectangleShiftBandIndicator_pointwise
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Z : Ω → ι → ℝ) (b c d : ι → ℝ) (ω : Ω) :
    |gaussianRectangleIndicator Z b c ω - gaussianRectangleIndicator Z b d ω| ≤
      ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω := by
  classical
  by_cases hc : ∀ i, Z ω i + c i ≤ b i
  · by_cases hd : ∀ i, Z ω i + d i ≤ b i
    · have hsum : 0 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
        Finset.sum_nonneg fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω
      simpa [gaussianRectangleIndicator, hc, hd] using hsum
    · obtain ⟨i, hi⟩ := not_forall.mp hd
      have hgt : b i < Z ω i + d i := lt_of_not_ge hi
      have hupper : Z ω i ≤ b i - c i := by linarith [hc i]
      have hlower : b i - d i < Z ω i := by linarith
      have hmem : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i)) := by
        constructor
        · exact (min_le_right _ _).trans hlower.le
        · exact hupper.trans (le_max_left _ _)
      have hband : gaussianRectangleShiftBandIndicator Z b c d i ω = 1 := by
        change Set.indicator {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} (fun _ => (1 : ℝ)) ω = 1
        have hmem' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
            (max (b i - c i) (b i - d i))} := hmem
        rw [Set.indicator_of_mem hmem']
      have hsum : 1 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω := by
        calc
          1 = gaussianRectangleShiftBandIndicator Z b c d i ω := hband.symm
          _ ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
            Finset.single_le_sum
              (fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω)
              (Finset.mem_univ i)
      simpa [gaussianRectangleIndicator, hc, hd] using hsum
  · by_cases hd : ∀ i, Z ω i + d i ≤ b i
    · obtain ⟨i, hi⟩ := not_forall.mp hc
      have hgt : b i < Z ω i + c i := lt_of_not_ge hi
      have hupper : Z ω i ≤ b i - d i := by linarith [hd i]
      have hlower : b i - c i < Z ω i := by linarith
      have hmem : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i)) := by
        constructor
        · exact (min_le_left _ _).trans hlower.le
        · exact hupper.trans (le_max_right _ _)
      have hband : gaussianRectangleShiftBandIndicator Z b c d i ω = 1 := by
        change Set.indicator {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} (fun _ => (1 : ℝ)) ω = 1
        have hmem' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
            (max (b i - c i) (b i - d i))} := hmem
        rw [Set.indicator_of_mem hmem']
      have hsum : 1 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω := by
        calc
          1 = gaussianRectangleShiftBandIndicator Z b c d i ω := hband.symm
          _ ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
            Finset.single_le_sum
              (fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω)
              (Finset.mem_univ i)
      simpa [gaussianRectangleIndicator, hc, hd] using hsum
    · have hnonneg : 0 ≤ ∑ j, gaussianRectangleShiftBandIndicator Z b c d j ω :=
        Finset.sum_nonneg fun j _ => gaussianRectangleShiftBandIndicator_nonneg Z b c d j ω
      simpa [gaussianRectangleIndicator, hc, hd] using hnonneg

private theorem gaussian_coordinate_level_set_null
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (i : ι) (t : ℝ) (hv : 0 < gaussianVariance P (fun ω => Z ω i)) :
    P {ω | Z ω i = t} = 0 := by
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ i
  have hv' : v ≠ 0 := by
    intro hz
    have hz' : gaussianVariance P (fun ω => Z ω i) = 0 := by
      rw [hvar, hz]
      norm_num
    linarith
  have hsingle : gaussianReal (0 : ℝ) v {t} = 0 := by
    exact (nullSingletonClass_gaussianReal hv').measure_singleton t
  have hset : {ω | Z ω i = t} = (fun ω => Z ω i) ⁻¹' ({t} : Set ℝ) := by
    ext ω
    rfl
  rw [hset]
  calc
    P ((fun ω => Z ω i) ⁻¹' ({t} : Set ℝ)) =
        P.map (fun ω => Z ω i) {t} :=
          (Measure.map_apply_of_aemeasurable (hZ.2.1 i) (measurableSet_singleton t)).symm
    _ = 0 := by rw [hmap, hsingle]

/-- The probability of a finite Gaussian rectangle is continuous when its coordinate variances
are positive. This remains true for singular joint covariance matrices. -/
theorem finite_gaussian_rectangle_probability_continuous_shift
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b : ι → ℝ) (hv : ∀ i, 0 < gaussianVariance P (fun ω => Z ω i)) :
    Continuous (fun c : ι → ℝ =>
      ∫ ω, gaussianRectangleIndicator Z b c ω ∂P) := by
  classical
  have hboundIntegrable : Integrable (fun _ : Ω => (1 : ℝ)) P := by
    have hfinite : IsFiniteMeasure P := by
      refine ⟨?_⟩
      rw [hZ.1.measure_univ]
      exact ENNReal.one_lt_top
    exact (integrable_const_iff (μ := P) (c := (1 : ℝ))).2
      (Or.inr hfinite)
  apply continuous_iff_continuousAt.mpr
  intro c
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
  · exact Filter.Eventually.of_forall fun c' =>
      gaussianRectangleIndicator_aestronglyMeasurable P Z hZ b c'
  · filter_upwards [] with c'
    exact ae_of_all P (fun ω => by
      change ‖if ∀ i, Z ω i + c' i ≤ b i then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num)
  · exact hboundIntegrable
  · have hboundary : ∀ᵐ ω ∂P, ∀ i, Z ω i + c i ≠ b i := by
      apply ae_all_iff.2
      intro i
      have hnull := gaussian_coordinate_level_set_null P Z hZ i (b i - c i) (hv i)
      have hEq : {ω | Z ω i + c i = b i} = {ω | Z ω i = b i - c i} := by
        ext ω
        simp only [Set.mem_ofPred_eq]
        constructor <;> intro h <;> linarith
      have hbad : P {ω | ¬ (Z ω i + c i ≠ b i)} = 0 := by
        have hbadEq : {ω | ¬ (Z ω i + c i ≠ b i)} = {ω | Z ω i + c i = b i} := by
          ext ω
          simp
        rw [hbadEq, hEq]
        exact hnull
      exact ae_iff.mpr hbad
    filter_upwards [hboundary] with ω hω
    have hstable : ∀ᶠ c' in 𝓝 c,
        gaussianRectangleIndicator Z b c' ω = gaussianRectangleIndicator Z b c ω := by
      have hcoord : ∀ i, ∀ᶠ c' in 𝓝 c,
          (Z ω i + c' i ≤ b i) ↔ (Z ω i + c i ≤ b i) := by
        intro i
        have hT : Tendsto (fun c' : ι → ℝ => Z ω i + c' i) (𝓝 c)
            (𝓝 (Z ω i + c i)) := by
          have hcont : Continuous (fun c' : ι → ℝ => Z ω i + c' i) := by fun_prop
          exact hcont.continuousAt.tendsto
        by_cases hlt : Z ω i + c i < b i
        · have hev : ∀ᶠ c' in 𝓝 c, Z ω i + c' i < b i :=
            hT.eventually (isOpen_Iio.mem_nhds hlt)
          filter_upwards [hev] with c' hc'
          constructor <;> intro _
          · exact hlt.le
          · exact hc'.le
        · have hgt : b i < Z ω i + c i := lt_of_le_of_ne (le_of_not_gt hlt)
            (Ne.symm (hω i))
          have hev : ∀ᶠ c' in 𝓝 c, b i < Z ω i + c' i :=
            hT.eventually (isOpen_Ioi.mem_nhds hgt)
          filter_upwards [hev] with c' hc'
          constructor <;> intro h
          · exact False.elim ((not_le_of_gt hc') h)
          · exact False.elim ((not_le_of_gt hgt) h)
      filter_upwards [eventually_all.2 hcoord] with c' hc'
      have hiff : (∀ i, Z ω i + c' i ≤ b i) ↔ (∀ i, Z ω i + c i ≤ b i) :=
        forall_congr' hc'
      change (if ∀ i, Z ω i + c' i ≤ b i then (1 : ℝ) else 0) =
        if ∀ i, Z ω i + c i ≤ b i then (1 : ℝ) else 0
      by_cases hp : ∀ i, Z ω i + c' i ≤ b i
      · have hq : ∀ i, Z ω i + c i ≤ b i := hiff.mp hp
        simp [hp, hq]
      · have hnq : ¬ ∀ i, Z ω i + c i ≤ b i := fun hq => hp (hiff.mpr hq)
        simp [hp, hnq]
    have hstable' : ∀ᶠ c' in 𝓝 c,
        gaussianRectangleIndicator Z b c ω = gaussianRectangleIndicator Z b c' ω := by
      filter_upwards [hstable] with c' hc'
      exact hc'.symm
    exact tendsto_const_nhds.congr' hstable'

/-- On a bounded set of deterministic shifts, the probability of a finite Gaussian rectangle
has a uniform modulus of continuity. This is useful when fixed coarse coordinates are tilted by
fine fields whose covariance shifts converge uniformly away from the spatial diagonal. -/
theorem finite_gaussian_rectangle_probability_uniform_shift
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b : ι → ℝ) (hv : ∀ i, 0 < gaussianVariance P (fun ω => Z ω i))
    (R : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ c d : ι → ℝ,
      ‖c‖ ≤ R → ‖d‖ ≤ R → ‖c - d‖ < δ →
      |(∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
        (∫ ω, gaussianRectangleIndicator Z b d ω ∂P)| < η := by
  let F : (ι → ℝ) → ℝ := fun c =>
    ∫ ω, gaussianRectangleIndicator Z b c ω ∂P
  have hF : Continuous F := by
    exact finite_gaussian_rectangle_probability_continuous_shift P Z hZ b hv
  let B : Set (ι → ℝ) := Metric.closedBall 0 R
  have hB : IsCompact B := isCompact_closedBall 0 R
  have hUC : UniformContinuousOn F B := by
    exact hB.uniformContinuousOn_of_continuous hF.continuousOn
  intro η hη
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  refine ⟨δ, hδ, ?_⟩
  intro c d hc hd hcd
  have hcB : c ∈ B := by
    change dist c 0 ≤ R
    simpa [dist_eq_norm] using hc
  have hdB : d ∈ B := by
    change dist d 0 ≤ R
    simpa [dist_eq_norm] using hd
  have hdist : dist c d < δ := by
    simpa [dist_eq_norm] using hcd
  have hval := hmod c hcB d hdB hdist
  change |F c - F d| < η
  simpa [F, Real.dist_eq] using hval

/-- Uniform convergence of deterministic shifts gives uniform convergence of the associated
finite Gaussian rectangle probabilities, provided the shifts remain in one bounded ball. -/
theorem finite_gaussian_rectangle_probability_tendstoUniformlyOn
    {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b : ι → ℝ) (hv : ∀ i, 0 < gaussianVariance P (fun ω => Z ω i))
    (S : Set α) (c : ℝ → α → ι → ℝ) (d : α → ι → ℝ) (R : ℝ)
    (hc : ∀ᶠ r : ℝ in atTop, ∀ a ∈ S, ‖c r a‖ ≤ R)
    (hd : ∀ a ∈ S, ‖d a‖ ≤ R)
    (hshift : ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop,
      ∀ a ∈ S, ‖c r a - d a‖ < δ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop,
      ∀ a ∈ S,
        |(∫ ω, gaussianRectangleIndicator Z b (c r a) ω ∂P) -
          (∫ ω, gaussianRectangleIndicator Z b (d a) ω ∂P)| < η := by
  intro η hη
  obtain ⟨δ, hδ, hmod⟩ :=
    finite_gaussian_rectangle_probability_uniform_shift P Z hZ b hv R η hη
  filter_upwards [hc, hshift δ hδ] with r hcr hshift'
  intro a ha
  exact hmod (c r a) (d a) (hcr a ha) (hd a ha) (hshift' a ha)

/-- The fixed-coarse covariance limit in admissibility applies uniformly to both fine roots of a
two-root tilt, with the coarse coordinate at either center. -/
theorem admissible_fixed_coarse_two_root_covariance_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (k : ℕ) (hkcut : Real.exp (-(k : ℝ)) ≤ ε₀) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ ε₀ → 0 < ε' → ε' ≤ min δ ε₀ →
        ∀ x ∈ K, ∀ y ∈ K,
          |gaussianCovariance P (fun ω => Y ω ε x)
              (fun ω => Y ω (Real.exp (-(k : ℝ))) y) - coarseKernel k x y| < η ∧
          |gaussianCovariance P (fun ω => Y ω ε' y)
              (fun ω => Y ω (Real.exp (-(k : ℝ))) x) - coarseKernel k y x| < η := by
  obtain ⟨coarseKernel, hfixed⟩ := hY.fixedCoarseLimit
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  obtain ⟨δ, hδ, hfixed'⟩ := hfixed K hK hKU k hkcut η hη
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut x hx y hy
  refine ⟨hfixed' ε hε hεcut x hx y hy, ?_⟩
  exact hfixed' ε' hε' hε'cut y hy x hx

/-- For finitely many fixed coarse barrier coordinates, the deterministic shift induced by two
fine Wick roots converges uniformly in both root locations. The limit is obtained by applying the
fixed-coarse covariance kernel to each root separately. -/
theorem admissible_finite_coarse_double_root_shift_tendsto_uniformly
    {Ω α ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (rootX rootY : α → ℂ)
    (hrootX : ∀ a ∈ S, rootX a ∈ K) (hrootY : ∀ a ∈ S, rootY a ∈ K)
    (scale : ι → ℕ) (center : α → ι → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ ε₀)
    (Γ : Set ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ ε₀ → 0 < ε' → ε' ≤ min δ ε₀ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i,
          |γ * gaussianCovariance P (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => Y ω ε (rootX a)) +
            γ * gaussianCovariance P (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                (fun ω => Y ω ε' (rootY a)) -
            (γ * coarseKernel (scale i) (rootX a) (center a i) +
              γ * coarseKernel (scale i) (rootY a) (center a i))| < η := by
  obtain ⟨coarseKernel, hfixed⟩ := hY.fixedCoarseLimit
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  let η' : ℝ := η / (2 * (B + 1))
  have hη' : 0 < η' := by
    dsimp [η']
    positivity
  have hlocal (i : ι) : ∃ δi : ℝ, 0 < δi ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ min δi ε₀ → ∀ a ∈ S,
        |gaussianCovariance P (fun ω => Y ω ε (rootX a))
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) -
          coarseKernel (scale i) (rootX a) (center a i)| < η' ∧
        |gaussianCovariance P (fun ω => Y ω ε (rootY a))
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) -
          coarseKernel (scale i) (rootY a) (center a i)| < η' := by
    obtain ⟨δi, hδi, hfixed'⟩ :=
      hfixed K hK hKU (scale i) (hscale i) η' hη'
    refine ⟨δi, hδi, ?_⟩
    intro ε hε hεcut a ha
    exact ⟨hfixed' ε hε hεcut (rootX a) (hrootX a ha)
        (center a i) (hcenter a ha i),
      hfixed' ε hε hεcut (rootY a) (hrootY a ha)
        (center a i) (hcenter a ha i)⟩
  choose δi hδi hcov using hlocal
  obtain ⟨i₀, hmin⟩ := Finite.exists_min (fun i : ι => δi i)
  let δ : ℝ := δi i₀
  have hδ : 0 < δ := hδi i₀
  have hcovComm (f g : Ω → ℝ) :
      gaussianCovariance P f g = gaussianCovariance P g f := by
    unfold gaussianCovariance
    apply integral_congr_ae
    exact ae_of_all P (fun ω => by ring)
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha i
  have hδle : δ ≤ δi i := hmin i
  have hεcut' : ε ≤ min (δi i) ε₀ := by
    apply le_min
    · exact (hεcut.trans (min_le_left _ _)).trans hδle
    · exact hεcut.trans (min_le_right _ _)
  have hε'cut' : ε' ≤ min (δi i) ε₀ := by
    apply le_min
    · exact (hε'cut.trans (min_le_left _ _)).trans hδle
    · exact hε'cut.trans (min_le_right _ _)
  have ⟨hfirst, _⟩ := hcov i ε hε hεcut' a ha
  have ⟨_, hsecond⟩ := hcov i ε' hε' hε'cut' a ha
  have hfirst' : |gaussianCovariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
      (fun ω => Y ω ε (rootX a)) -
        coarseKernel (scale i) (rootX a) (center a i)| < η' := by
    rw [hcovComm]
    exact hfirst
  have hsecond' : |gaussianCovariance P
      (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
      (fun ω => Y ω ε' (rootY a)) -
        coarseKernel (scale i) (rootY a) (center a i)| < η' := by
    rw [hcovComm]
    exact hsecond
  have hsum :
      |γ * gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
            (fun ω => Y ω ε (rootX a)) +
        γ * gaussianCovariance P
            (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
            (fun ω => Y ω ε' (rootY a)) -
        (γ * coarseKernel (scale i) (rootX a) (center a i) +
          γ * coarseKernel (scale i) (rootY a) (center a i))| < η := by
    have hsmall : 2 * B * η' < η := by
      dsimp [η']
      have hden : 0 < 2 * (B + 1) := by positivity
      field_simp
      nlinarith [hB]
    calc
      _ = |γ * (gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
              (fun ω => Y ω ε (rootX a)) -
                coarseKernel (scale i) (rootX a) (center a i)) +
            γ * (gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
              (fun ω => Y ω ε' (rootY a)) -
                coarseKernel (scale i) (rootY a) (center a i))| := by
                congr 1
                ring
      _ ≤ |γ * (gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
              (fun ω => Y ω ε (rootX a)) -
                coarseKernel (scale i) (rootX a) (center a i))| +
            |γ * (gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
              (fun ω => Y ω ε' (rootY a)) -
                coarseKernel (scale i) (rootY a) (center a i))| :=
                abs_add_le _ _
      _ = |γ| * |gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
              (fun ω => Y ω ε (rootX a)) -
                coarseKernel (scale i) (rootX a) (center a i)| +
            |γ| * |gaussianCovariance P
              (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
              (fun ω => Y ω ε' (rootY a)) -
                coarseKernel (scale i) (rootY a) (center a i)| := by
                rw [abs_mul, abs_mul]
      _ ≤ |γ| * η' + |γ| * η' := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (le_of_lt hfirst') (abs_nonneg γ))
          (mul_le_mul_of_nonneg_left (le_of_lt hsecond') (abs_nonneg γ))
      _ = 2 * |γ| * η' := by ring
      _ ≤ 2 * B * η' := by
        calc
          2 * |γ| * η' = (2 * |γ|) * η' := by ring
          _ ≤ (2 * B) * η' :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hΓ γ hγ) (by norm_num)) (le_of_lt hη')
          _ = 2 * B * η' := by ring
      _ < η := hsmall
  exact hsum

/-- A real Gaussian with variance at least one assigns an interval no more mass than its
Lebesgue length. This gives a covariance-independent boundary-strip bound for finite Gaussian
rectangle probabilities. -/
theorem gaussianReal_interval_le_length_of_variance_ge_one
    (μ : ℝ) (v : ℝ≥0) (hv : 1 ≤ (v : ℝ)) (a b : ℝ) (hab : a ≤ b) :
    gaussianReal μ v (Set.Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz] at hv
    norm_num at hv
  have hpdf (x : ℝ) : gaussianPDFReal μ v x ≤ 1 := by
    rw [gaussianPDFReal_def]
    have harg : (1 : ℝ) ≤ 2 * Real.pi * (v : ℝ) := by
      nlinarith [Real.pi_gt_three]
    have hden : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (v : ℝ)) := by
      have h := Real.sqrt_le_sqrt harg
      simpa using h
    have hdenpos : 0 < Real.sqrt (2 * Real.pi * (v : ℝ)) := by positivity
    have hinv : (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hdenpos]
      exact hden
    have hargExp : -(x - μ) ^ 2 / (2 * (v : ℝ)) ≤ 0 := by
      have hnum : -(x - μ) ^ 2 ≤ 0 := neg_nonpos.mpr (sq_nonneg (x - μ))
      have hdenExp : 0 < 2 * (v : ℝ) := by positivity
      exact div_nonpos_of_nonpos_of_nonneg hnum hdenExp.le
    have hexp : Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤ 1 := by
      exact (Real.exp_le_one_iff.mpr hargExp)
    calc
      (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-(x - μ) ^ 2 / (2 * (v : ℝ))) ≤
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 1 := by simpa using hinv
  have hpdfInt : IntegrableOn (gaussianPDFReal μ v) (Set.Icc a b) :=
    (integrable_gaussianPDFReal μ v).integrableOn
  have hconstInt : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) :=
    integrableOn_const (by simp)
  have hInt : (∫ x in Set.Icc a b, gaussianPDFReal μ v x) ≤ b - a := by
    calc
      (∫ x in Set.Icc a b, gaussianPDFReal μ v x) ≤
          ∫ x in Set.Icc a b, (1 : ℝ) :=
        setIntegral_mono_on hpdfInt hconstInt isClosed_Icc.measurableSet fun x _ => hpdf x
      _ = b - a := by
        rw [setIntegral_const, Real.volume_real_Icc_of_le hab]
        simp
  rw [gaussianReal_apply_eq_integral μ hvne (Set.Icc a b)]
  exact ENNReal.ofReal_le_ofReal hInt

/-- A coordinate of a centered jointly Gaussian vector with variance at least one has a
covariance-independent interval probability bound. -/
theorem gaussian_coordinate_interval_probability_le_length_of_variance_ge_one
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (i : ι) (hv : 1 ≤ gaussianVariance P (fun ω => Z ω i))
    (a b : ℝ) (hab : a ≤ b) :
    P {ω | Z ω i ∈ Set.Icc a b} ≤ ENNReal.ofReal (b - a) := by
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ i
  have hv' : 1 ≤ (v : ℝ) := by simpa [hvar] using hv
  have hprob : P {ω | Z ω i ∈ Set.Icc a b} =
      gaussianReal 0 v (Set.Icc a b) := by
    let Zi : Ω → ℝ := fun ω => Z ω i
    have hZi : AEMeasurable Zi P := hZ.2.1 i
    calc
      P {ω | Z ω i ∈ Set.Icc a b} = P (Zi ⁻¹' Set.Icc a b) := by rfl
      _ = P.map Zi (Set.Icc a b) := by
        symm
        exact Measure.map_apply_of_aemeasurable hZi isClosed_Icc.measurableSet
      _ = gaussianReal 0 v (Set.Icc a b) := by rw [hmap]
  rw [hprob]
  exact gaussianReal_interval_le_length_of_variance_ge_one 0 v hv' a b hab

/-- The finite Gaussian rectangle probability is Lipschitz in its deterministic shift, with a
modulus independent of all correlations, as soon as every marginal variance is at least one. -/
theorem finite_gaussian_rectangle_probability_shift_lipschitz
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (b : ι → ℝ) (hv : ∀ i, 1 ≤ gaussianVariance P (fun ω => Z ω i))
    (c d : ι → ℝ) :
    |(∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
      (∫ ω, gaussianRectangleIndicator Z b d ω ∂P)| ≤
        (Fintype.card ι : ℝ) * ‖c - d‖ := by
  classical
  have hPfinite : IsFiniteMeasure P := by
    refine ⟨?_⟩
    rw [hZ.1.measure_univ]
    exact ENNReal.one_lt_top
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := by
    exact (integrable_const_iff (μ := P) (c := (1 : ℝ))).2 (Or.inr hPfinite)
  have hrectAEM (e : ι → ℝ) :
      AEStronglyMeasurable (gaussianRectangleIndicator Z b e) P :=
    gaussianRectangleIndicator_aestronglyMeasurable P Z hZ b e
  have hrectBound (e : ι → ℝ) :
      ∀ᵐ ω ∂P, ‖gaussianRectangleIndicator Z b e ω‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    dsimp [gaussianRectangleIndicator]
    split_ifs <;> norm_num
  have hrectInt (e : ι → ℝ) :
      Integrable (gaussianRectangleIndicator Z b e) P :=
    hone.mono' (hrectAEM e) (hrectBound e)
  have hbandAEM (i : ι) :
      AEStronglyMeasurable (gaussianRectangleShiftBandIndicator Z b c d i) P :=
    gaussianRectangleShiftBandIndicator_aestronglyMeasurable P Z hZ b c d i
  have hbandBound (i : ι) :
      ∀ᵐ ω ∂P, ‖gaussianRectangleShiftBandIndicator Z b c d i ω‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    by_cases hi : Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))
    · change ‖Set.indicator {ω' | Z ω' i ∈ Set.Icc
        (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i))}
        (fun _ => (1 : ℝ)) ω‖ ≤ 1
      have hi' : ω ∈ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := hi
      rw [Set.indicator_of_mem hi']
      norm_num
    · change ‖Set.indicator {ω' | Z ω' i ∈ Set.Icc
        (min (b i - c i) (b i - d i)) (max (b i - c i) (b i - d i))}
        (fun _ => (1 : ℝ)) ω‖ ≤ 1
      have hi' : ω ∉ {ω' | Z ω' i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := hi
      rw [Set.indicator_of_notMem hi']
      norm_num
  have hbandInt (i : ι) :
      Integrable (gaussianRectangleShiftBandIndicator Z b c d i) P :=
    hone.mono' (hbandAEM i) (hbandBound i)
  have hbandNull (i : ι) : NullMeasurableSet
      {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} P :=
    (hZ.2.1 i).nullMeasurableSet_preimage isClosed_Icc.measurableSet
  have hbandIntegral (i : ι) :
      (∫ ω, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P) =
        P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := by
    let S : Set Ω := {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
      (max (b i - c i) (b i - d i))}
    calc
      (∫ ω, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P) =
          ∫ ω, Set.indicator S (fun _ => (1 : ℝ)) ω ∂P := by
            rfl
      _ = ∫ ω in S, (1 : ℝ) ∂P := integral_indicator₀ (hbandNull i)
      _ = P.real S := by rw [setIntegral_const]; simp
  have hbandProb (i : ι) :
      P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
        (max (b i - c i) (b i - d i))} ≤ |c i - d i| := by
    let lo : ℝ := min (b i - c i) (b i - d i)
    let hi : ℝ := max (b i - c i) (b i - d i)
    have hlen : hi - lo = |c i - d i| := by
      dsimp [hi, lo]
      rw [max_sub_min_eq_abs]
      congr 1
      ring
    have hprob := gaussian_coordinate_interval_probability_le_length_of_variance_ge_one
      P Z hZ i (hv i) lo hi min_le_max
    have hprob' : P {ω | Z ω i ∈ Set.Icc lo hi} ≤ ENNReal.ofReal (hi - lo) := hprob
    rw [hlen] at hprob'
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob'
    rw [ENNReal.toReal_ofReal (abs_nonneg (c i - d i))] at hreal
    change (P {ω | Z ω i ∈ Set.Icc lo hi}).toReal ≤ |c i - d i|
    exact hreal
  have hsumInt : Integrable
      (fun ω => ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω) P :=
    integrable_finsetSum Finset.univ (fun i _ => hbandInt i)
  have hsumIntegral :
      (∫ ω, ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P) =
        ∑ i, P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := by
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i _
      exact hbandIntegral i
    · intro i _
      exact hbandInt i
  have hsumBound :
      (∑ i, |c i - d i|) ≤ (Fintype.card ι : ℝ) * ‖c - d‖ := by
    calc
      (∑ i, |c i - d i|) ≤ ∑ i, ‖c - d‖ := by
        apply Finset.sum_le_sum
        intro i _
        simpa using norm_le_pi_norm (c - d) i
      _ = (Fintype.card ι : ℝ) * ‖c - d‖ := by simp
  have hEq :
      (∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
        (∫ ω, gaussianRectangleIndicator Z b d ω ∂P) =
          ∫ ω, gaussianRectangleIndicator Z b c ω -
            gaussianRectangleIndicator Z b d ω ∂P := by
    rw [integral_sub (hrectInt c) (hrectInt d)]
  calc
    |(∫ ω, gaussianRectangleIndicator Z b c ω ∂P) -
        (∫ ω, gaussianRectangleIndicator Z b d ω ∂P)| =
          ‖∫ ω, gaussianRectangleIndicator Z b c ω -
            gaussianRectangleIndicator Z b d ω ∂P‖ := by
              rw [hEq, Real.norm_eq_abs]
    _ ≤ ∫ ω, ‖gaussianRectangleIndicator Z b c ω -
          gaussianRectangleIndicator Z b d ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ∑ i, gaussianRectangleShiftBandIndicator Z b c d i ω ∂P :=
      integral_mono ((hrectInt c).sub (hrectInt d)).norm hsumInt
        (fun ω => by simpa [Real.norm_eq_abs] using
          gaussianRectangleShiftBandIndicator_pointwise Z b c d ω)
    _ = ∑ i, P.real {ω | Z ω i ∈ Set.Icc (min (b i - c i) (b i - d i))
          (max (b i - c i) (b i - d i))} := hsumIntegral
    _ ≤ ∑ i, |c i - d i| := Finset.sum_le_sum fun i _ => hbandProb i
    _ ≤ (Fintype.card ι : ℝ) * ‖c - d‖ := hsumBound

/-- Uniform convergence of every coordinate shift implies uniform convergence of finite Gaussian
rectangle probabilities, with a bound independent of the correlations and of the parameterized
Gaussian vectors. -/
theorem finite_gaussian_rectangle_probability_two_shift_tendsto_uniformly
    {Ω α ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Γ : Set ℝ) (S : Set α)
    (Z : α → Ω → ι → ℝ)
    (hZ : ∀ a ∈ S, IsCenteredJointlyGaussian P (Z a))
    (b : ι → ℝ)
    (hv : ∀ a ∈ S, ∀ i, 1 ≤ gaussianVariance P (fun ω => Z a ω i))
    (c : ℝ → ℝ → ℝ → α → ι → ℝ) (d : ℝ → α → ι → ℝ)
    (hshift : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i, |c ε ε' γ a i - d γ a i| < η) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |(∫ ω, gaussianRectangleIndicator (Z a) b (c ε ε' γ a) ω ∂P) -
            (∫ ω, gaussianRectangleIndicator (Z a) b (d γ a) ω ∂P)| < η := by
  intro η hη
  let η' : ℝ := η / ((Fintype.card ι : ℝ) + 1)
  have hη' : 0 < η' := by
    dsimp [η']
    positivity
  obtain ⟨δ, hδ, hcoord⟩ := hshift η' hη'
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
  have hnorm : ‖c ε ε' γ a - d γ a‖ ≤ η' := by
    rw [pi_norm_le_iff_of_nonneg (le_of_lt hη')]
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using
      (hcoord ε ε' hε hεcut hε' hε'cut γ hγ a ha i).le
  have hprob := finite_gaussian_rectangle_probability_shift_lipschitz
    P (Z a) (hZ a ha) b (hv a ha) (c ε ε' γ a) (d γ a)
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hcardη : (Fintype.card ι : ℝ) * η' < η := by
    dsimp [η']
    field_simp
    nlinarith
  calc
    _ ≤ (Fintype.card ι : ℝ) * ‖c ε ε' γ a - d γ a‖ := hprob
    _ ≤ (Fintype.card ι : ℝ) * η' :=
      mul_le_mul_of_nonneg_left hnorm hcard
    _ < η := hcardη

/-- The admissible coarse-variance estimate makes every coordinate above its uniform error plus
one have variance at least one. This supplies the only variance input to the finite-barrier
rectangle modulus. -/
theorem admissible_finite_coarse_variance_ge_one_of_large_scales
    {Ω α : Type*} [MeasurableSpace Ω] {n : ℕ}
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (scale : Fin n → ℕ) (center : α → Fin n → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ ε₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i, C + 1 ≤ (scale i : ℝ) → ∀ a ∈ S,
      1 ≤ gaussianVariance P
        (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) := by
  obtain ⟨C, hC, hvar⟩ := hY.coarseVarianceBound K hK hKU
  refine ⟨C, hC, ?_⟩
  intro i hlarge a ha
  have h := hvar (scale i) (hscale i) (center a i) (hcenter a ha i)
  have hlow := (abs_le.mp h).1
  linarith

/-- A finite good-barrier rectangle under the two-root tilt converges uniformly in its spatial
parameters when the coarse coordinates have variance at least one. The remaining coarse-barrier
tail is handled separately when passing from a fixed finite barrier to the full cutoff. -/
theorem admissible_finite_coarse_double_root_barrier_probability_tendsto_uniformly
    {Ω α : Type*} [MeasurableSpace Ω] {n : ℕ} [Nonempty (Fin n)]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (S : Set α) (rootX rootY : α → ℂ)
    (hrootX : ∀ a ∈ S, rootX a ∈ K) (hrootY : ∀ a ∈ S, rootY a ∈ K)
    (scale : Fin n → ℕ) (center : α → Fin n → ℂ)
    (hcenter : ∀ a ∈ S, ∀ i, center a i ∈ K)
    (hscale : ∀ i, Real.exp (-(scale i : ℝ)) ≤ ε₀)
    (hv : ∀ a ∈ S, ∀ i,
      1 ≤ gaussianVariance P
        (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i)))
    (b : Fin n → ℝ) (Γ : Set ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ, ∀ η : ℝ, 0 < η →
      ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε' : ℝ,
        0 < ε → ε ≤ min δ ε₀ → 0 < ε' → ε' ≤ min δ ε₀ →
        ∀ γ ∈ Γ, ∀ a ∈ S,
          |(∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) b
                (fun i => γ * gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                  (fun ω => Y ω ε (rootX a)) +
                  γ * gaussianCovariance P
                  (fun ω => Y ω (Real.exp (-(scale i : ℝ))) (center a i))
                  (fun ω => Y ω ε' (rootY a))) ω ∂P) -
            (∫ ω, gaussianRectangleIndicator
                (fun ω i => Y ω (Real.exp (-(scale i : ℝ))) (center a i)) b
                (fun i => γ * coarseKernel (scale i) (rootX a) (center a i) +
                  γ * coarseKernel (scale i) (rootY a) (center a i)) ω ∂P)| < η := by
  let q : α → Fin n → ℝ × ℂ := fun a i =>
    (Real.exp (-(scale i : ℝ)), center a i)
  let Z : α → Ω → Fin n → ℝ := fun a ω i => Y ω (q a i).1 (q a i).2
  have hZ : ∀ a ∈ S, IsCenteredJointlyGaussian P (Z a) := by
    intro a ha
    apply hY.gaussian n (q a)
    intro i
    exact ⟨Real.exp_pos _, hscale i⟩
  have hvar : ∀ a ∈ S, ∀ i,
      1 ≤ gaussianVariance P (fun ω => Z a ω i) := by
    intro a ha i
    simpa [Z, q] using hv a ha i
  let c : ℝ → ℝ → ℝ → α → Fin n → ℝ := fun ε ε' γ a i =>
    γ * gaussianCovariance P (fun ω => Z a ω i)
      (fun ω => Y ω ε (rootX a)) +
    γ * gaussianCovariance P (fun ω => Z a ω i)
      (fun ω => Y ω ε' (rootY a))
  obtain ⟨coarseKernel, hshift⟩ :=
    admissible_finite_coarse_double_root_shift_tendsto_uniformly
      P U dens ε₀ Y hY K hK hKU S rootX rootY hrootX hrootY
      scale center hcenter hscale Γ B hB hΓ
  let d : ℝ → α → Fin n → ℝ := fun γ a i =>
    γ * coarseKernel (scale i) (rootX a) (center a i) +
    γ * coarseKernel (scale i) (rootY a) (center a i)
  have hcoord : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε ε' : ℝ, 0 < ε → ε ≤ δ → 0 < ε' → ε' ≤ δ →
        ∀ γ ∈ Γ, ∀ a ∈ S, ∀ i, |c ε ε' γ a i - d γ a i| < η := by
    intro η hη
    obtain ⟨δ, hδ, hshift'⟩ := hshift η hη
    let δ' : ℝ := min δ ε₀
    have hδ' : 0 < δ' := lt_min hδ hY.cutoffPositive
    refine ⟨δ', hδ', ?_⟩
    intro ε ε' hε hεcut hε' hε'cut γ hγ a ha i
    have hεcut' : ε ≤ min δ ε₀ := by
      apply le_min
      · exact hεcut.trans (min_le_left _ _)
      · exact hεcut.trans (min_le_right _ _)
    have hε'cut' : ε' ≤ min δ ε₀ := by
      apply le_min
      · exact hε'cut.trans (min_le_left _ _)
      · exact hε'cut.trans (min_le_right _ _)
    have h := hshift' ε ε' hε hεcut' hε' hε'cut' γ hγ a ha i
    simpa [c, d, Z, q] using h
  have hprob := finite_gaussian_rectangle_probability_two_shift_tendsto_uniformly
    P Γ S Z hZ b hvar c d hcoord
  refine ⟨coarseKernel, ?_⟩
  intro η hη
  obtain ⟨δ, hδ, hprob'⟩ := hprob η hη
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ a ha
  have hεcut' : ε ≤ δ := hεcut.trans (min_le_left _ _)
  have hε'cut' : ε' ≤ δ := hε'cut.trans (min_le_left _ _)
  have h := hprob' ε ε' hε hεcut' hε' hε'cut' γ hγ a ha
  simpa [Z, q, c, d] using h

/-- The off-diagonal Wick cross-covariance factor converges uniformly on compact separated spatial
sets and on every bounded charge set. The compact-set exponential modulus is applied only after the
off-diagonal covariance limit of `DOZZ.IsAdmissibleLogRegularization` has supplied a uniform
bound. -/
theorem admissible_off_diagonal_wick_factor_tendsto_uniformly
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℝ) (hs : 0 < s)
    (S : Set (ℂ × ℂ)) (hS : IsCompact S)
    (hSxy : ∀ p ∈ S, p.1 ∈ K ∧ p.2 ∈ K ∧ s ≤ ‖p.1 - p.2‖)
    (Γ : Set ℝ) (B : ℝ)
    (hΓ : ∀ γ ∈ Γ, |γ| ≤ B) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H) (U ×ˢ U) ∧
      ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ ε ε' : ℝ, 0 < ε → ε ≤ min δ ε₀ → 0 < ε' → ε' ≤ min δ ε₀ →
          ∀ γ ∈ Γ, ∀ p ∈ S,
            |Real.exp (γ ^ 2 * gaussianCovariance P
                (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2)) -
              Real.exp (γ ^ 2 * (Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2))| < η := by
  obtain ⟨H, hH, hcov⟩ := hY.offDiagonalLimit
  refine ⟨H, hH, ?_⟩
  intro η hη
  let lim : ℂ × ℂ → ℝ := fun p => Real.log (1 / ‖p.1 - p.2‖) + H p.1 p.2
  have hsep (p : ℂ × ℂ) (hp : p ∈ S) : 0 < ‖p.1 - p.2‖ :=
    lt_of_lt_of_le hs (hSxy p hp).2.2
  have hdist : Continuous fun p : ℂ × ℂ => ‖p.1 - p.2‖ := by fun_prop
  have hinv : ContinuousOn (fun p : ℂ × ℂ => (‖p.1 - p.2‖)⁻¹) S :=
    hdist.continuousOn.inv₀ (fun p hp => ne_of_gt (hsep p hp))
  have harg : ContinuousOn (fun p : ℂ × ℂ => 1 / ‖p.1 - p.2‖) S := by
    simpa [one_div] using hinv
  have hargNe : ∀ p ∈ S, 1 / ‖p.1 - p.2‖ ∈ ({0} : Set ℝ)ᶜ := by
    intro p hp
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt (one_div_pos.mpr (hsep p hp))
  have hlog : ContinuousOn (fun p : ℂ × ℂ => Real.log (1 / ‖p.1 - p.2‖)) S :=
    ContinuousOn.comp' Real.continuousOn_log harg hargNe
  have hHsub : S ⊆ U ×ˢ U := by
    intro p hp
    exact Set.mem_prod.mpr ⟨hKU (hSxy p hp).1, hKU (hSxy p hp).2.1⟩
  have hH' : ContinuousOn (fun p : ℂ × ℂ => H p.1 p.2) S := by
    exact hH.mono hHsub
  have hlim : ContinuousOn lim S := by
    exact hlog.add hH'
  have habs : ContinuousOn (fun p => |lim p|) S := hlim.abs
  obtain ⟨R₀, hR₀⟩ := hS.bddAbove_image habs
  let R : ℝ := max 0 R₀
  have hR : 0 ≤ R := by dsimp [R]; exact le_max_left _ _
  have hlimBound (p : ℂ × ℂ) (hp : p ∈ S) : |lim p| ≤ R := by
    have hmem : |lim p| ∈ (fun p : ℂ × ℂ => |lim p|) '' S := ⟨p, hp, rfl⟩
    have h := hR₀ hmem
    exact h.trans (le_max_right 0 R₀)
  let D : Set ℝ := Set.Icc (-B) B
  let T : Set ℝ := Set.Icc (-(R + 1)) (R + 1)
  have hD : IsCompact D := isCompact_Icc
  have hT : IsCompact T := isCompact_Icc
  let E : ℝ × ℝ → ℝ := fun z => Real.exp (z.1 ^ 2 * z.2)
  have hE : Continuous E := by fun_prop
  have hET : IsCompact (D ×ˢ T) := hD.prod hT
  have hUC : UniformContinuousOn E (D ×ˢ T) :=
    hET.uniformContinuousOn_of_continuous hE.continuousOn
  obtain ⟨δE, hδE, hmod⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  let ηcov : ℝ := min δE 1
  have hηcov : 0 < ηcov := lt_min hδE one_pos
  have hηcovE : ηcov ≤ δE := min_le_left _ _
  have hηcovOne : ηcov ≤ 1 := min_le_right _ _
  obtain ⟨δ, hδ, hcov'⟩ := hcov K hK hKU s hs ηcov hηcov
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεcut hε' hε'cut γ hγ p hp
  have hpK := hSxy p hp
  have hcovErr :
      |gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2) - lim p| < ηcov :=
    hcov' ε ε' hε hεcut hε' hε'cut p.1 hpK.1 p.2 hpK.2.1 hpK.2.2
  have hgammaD : γ ∈ D := by
    change -B ≤ γ ∧ γ ≤ B
    exact abs_le.mp (hΓ γ hγ)
  have hlimD : lim p ∈ T := by
    change -(R + 1) ≤ lim p ∧ lim p ≤ R + 1
    have hbound := hlimBound p hp
    have hb := abs_le.mp hbound
    constructor <;> linarith [hR]
  have hcovD : gaussianCovariance P
      (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2) ∈ T := by
    change -(R + 1) ≤ gaussianCovariance P
        (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2) ∧
      gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2) ≤ R + 1
    have hb := abs_le.mp (hlimBound p hp)
    have hcovAbs : |gaussianCovariance P
        (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2)| ≤ R + 1 := by
      calc
        _ = |(gaussianCovariance P (fun ω => Y ω ε p.1)
              (fun ω => Y ω ε' p.2) - lim p) + lim p| := by
                congr 1
                ring
        _ ≤ |gaussianCovariance P (fun ω => Y ω ε p.1)
              (fun ω => Y ω ε' p.2) - lim p| + |lim p| := abs_add_le _ _
        _ ≤ R + 1 := by linarith [hlimBound p hp, hcovErr.le, hηcovOne]
    exact abs_le.mp hcovAbs
  have hpairDist :
      dist (γ, lim p) (γ, gaussianCovariance P
        (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2)) < δE := by
    have hsecond : dist (lim p) (gaussianCovariance P
        (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2)) < δE := by
      have h' := lt_of_lt_of_le hcovErr hηcovE
      simpa [Real.dist_eq, abs_sub_comm] using h'
    simpa [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using hsecond
  have hEclose := hmod (γ, lim p) (Set.mem_prod.mpr ⟨hgammaD, hlimD⟩)
    (γ, gaussianCovariance P (fun ω => Y ω ε p.1) (fun ω => Y ω ε' p.2))
    (Set.mem_prod.mpr ⟨hgammaD, hcovD⟩) hpairDist
  have hresult := hEclose
  simpa [E, lim, Real.dist_eq, abs_sub_comm] using hresult


end DOZZ.Proofs
