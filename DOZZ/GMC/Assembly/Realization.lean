/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCCountableTests
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.MetricSpace.Thickening
public import DOZZ.GMC.Assembly.CutoffIntegral
public import DOZZ.GMC.Construction.GMCPathwiseSummableIncrements
public import Mathlib.Analysis.SpecificLimits.Basic
public import DOZZ.GMC.Assembly.CircleIntensity
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! Chart test systems and almost sure limits of admissible cutoff integrals along a fast cutoff sequence, for every continuous test with compact support in the chart. -/

@[expose] public section

/-! ### Chart test systems

A countable system of continuous tests on an open planar chart.

A compact exhaustion of the chart carries countably many compactly supported continuous tests,
uniformly dense among the continuous tests supported in each exhausting set, together with
continuous mass-control cutoffs equal to one on each exhausting set. -/

open Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

/-- Countable continuous tests on an open chart with mass-control cutoffs. -/
structure ChartTestSystem (U : Set ℂ) where
  K : ℕ → Set ℂ
  compact : ∀ n, IsCompact (K n)
  subset : ∀ n, K n ⊆ U
  mono : ∀ n, K n ⊆ K (n + 1)
  cofinal : ∀ L, IsCompact L → L ⊆ U → ∃ n, L ⊆ K n
  test : ℕ × ℕ → BoundedContinuousFunction ℂ ℝ
  test_compact : ∀ i, HasCompactSupport (test i : ℂ → ℝ)
  test_support : ∀ i, tsupport (test i : ℂ → ℝ) ⊆ K i.1
  dense : ∀ n (g : C(ℂ, ℝ)), HasCompactSupport g → tsupport g ⊆ K n →
    ∀ δ : ℝ, 0 < δ → ∃ m, ∀ x, ‖test (n, m) x - g x‖ < δ
  mass : ℕ → BoundedContinuousFunction ℂ ℝ
  mass_nonneg : ∀ n x, 0 ≤ mass n x
  mass_le_one : ∀ n x, mass n x ≤ 1
  mass_eq_one : ∀ n, ∀ x ∈ K n, mass n x = 1
  mass_compact : ∀ n, HasCompactSupport (mass n : ℂ → ℝ)
  mass_support : ∀ n, tsupport (mass n : ℂ → ℝ) ⊆ U

/-- Every open chart carries a countable test system. -/
theorem exists_chartTestSystem (U : Set ℂ) (hU : IsOpen U) : Nonempty (ChartTestSystem U) := by
  obtain ⟨K, hKc, hKU, hKmono, -, hcof, f, hf, hdense⟩ :=
    DOZZ.Proofs.exists_countable_dense_admissible_tests U hU
  have hmass : ∀ n, ∃ χ : C(ℂ, ℝ), EqOn χ 1 (K n) ∧ HasCompactSupport χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧ tsupport χ ⊆ U := by
    intro n
    obtain ⟨δ, hδ, hδU⟩ := (hKc n).exists_cthickening_subset_open hU (hKU n)
    obtain ⟨χ, hχ1, hχ0, hχc, hχI⟩ := exists_continuous_one_zero_of_isCompact (hKc n)
      (Metric.isOpen_thickening (δ := δ) (E := K n)).isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (Metric.self_subset_thickening hδ (K n)))
    refine ⟨χ, hχ1, hχc, hχI, ?_⟩
    have hsupp : Function.support χ ⊆ Metric.thickening δ (K n) := by
      intro x hx
      by_contra hxt
      exact hx (hχ0 hxt)
    exact (closure_mono hsupp).trans
      ((Metric.closure_thickening_subset_cthickening δ (K n)).trans hδU)
  choose χ hχ1 hχc hχI hχU using hmass
  exact ⟨{
    K := K
    compact := hKc
    subset := hKU
    mono := hKmono
    cofinal := hcof
    test := f
    test_compact := fun i => (hf i.1 i.2).1
    test_support := fun i => (hf i.1 i.2).2.1
    dense := hdense
    mass := fun n => BoundedContinuousFunction.ofNormedAddCommGroup (χ n) (χ n).continuous 1
      (fun x => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hχI n x).1, (hχI n x).2])
    mass_nonneg := fun n x => (hχI n x).1
    mass_le_one := fun n x => (hχI n x).2
    mass_eq_one := fun n x hx => hχ1 n hx
    mass_compact := hχc
    mass_support := hχU }⟩

end DOZZ.Assembly

/-! ### Fast cutoff sequences

Almost sure limits of admissible cutoff integrals along a fast cutoff sequence.

For one subcritical charge, every test of a chart test system is `L¹` Cauchy in the cutoff. A
cutoff sequence growing fast enough makes the expected increments summable for every test, so
almost surely all tests converge along it simultaneously. Uniform density and the mass-control
cutoffs then give convergence for every continuous test supported in the chart. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

namespace ChartTestSystem

variable {U : Set ℂ}

/-- Index of all tests: dense tests and mass-control cutoffs. -/
abbrev Index := (ℕ × ℕ) ⊕ ℕ

/-- All tests of the system. -/
def allTest (T : ChartTestSystem U) : Index → BoundedContinuousFunction ℂ ℝ
  | .inl i => T.test i
  | .inr n => T.mass n

/-- A compact chart carrying each test. -/
def chart (T : ChartTestSystem U) : Index → Set ℂ
  | .inl i => T.K i.1
  | .inr n => tsupport (T.mass n : ℂ → ℝ)

theorem chart_compact (T : ChartTestSystem U) (i : Index) : IsCompact (T.chart i) := by
  cases i with
  | inl i => exact T.compact i.1
  | inr n => exact T.mass_compact n

theorem chart_subset (T : ChartTestSystem U) (i : Index) : T.chart i ⊆ U := by
  cases i with
  | inl i => exact T.subset i.1
  | inr n => exact T.mass_support n

theorem allTest_eq_zero (T : ChartTestSystem U) (i : Index) (x : ℂ) (hx : x ∉ T.chart i) :
    T.allTest i x = 0 := by
  cases i with
  | inl i => exact image_eq_zero_of_notMem_tsupport (fun h => hx (T.test_support i h))
  | inr n => exact image_eq_zero_of_notMem_tsupport hx

theorem abs_allTest_le (T : ChartTestSystem U) (i : Index) (x : ℂ) :
    |T.allTest i x| ≤ ‖T.allTest i‖ := by
  rw [← Real.norm_eq_abs]
  exact (T.allTest i).norm_coe_le_norm x

theorem K_subset_tsupport_mass (T : ChartTestSystem U) (n : ℕ) :
    T.K n ⊆ tsupport (T.mass n : ℂ → ℝ) := by
  intro x hx
  apply subset_tsupport
  rw [Function.mem_support, T.mass_eq_one n x hx]
  exact one_ne_zero

end ChartTestSystem

/-- The admissible cutoff integral is bounded in expectation by the test bound times the chart
reference mass. -/
theorem lintegral_ofReal_abs_admissibleCutoffIntegral_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (K : Set ℂ) (g r : ℝ)
    (hr : Real.exp (-r) ≤ ε₀) (L : ℝ) (f : ℂ → ℝ) (hf : Measurable f) (hfL : ∀ x, |f x| ≤ L)
    (hfK : ∀ x ∉ K, f x = 0) :
    ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y g r f ω| ∂P ≤
      ENNReal.ofReal L * logRegularizationReference U dens K := by
  refine le_trans (lintegral_mono fun ω => ?_) (lintegral_chartMass_le P U dens ε₀ Y hY K g r hr L
    (fun x => |f x|) (continuous_abs.measurable.comp hf) hfL)
  rw [← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  rw [← lintegral_cutoff_integrand_eq_chartMass P U dens Y K g r (fun x => |f x|)
    (fun x => abs_nonneg _) (fun x hx => by rw [hfK x hx, abs_zero]) ω]
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- Fast cutoff sequence built from Cauchy thresholds. -/
noncomputable def fastCutoff (R : ChartTestSystem.Index → ℕ → ℝ)
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) (j : ℕ) : ℝ :=
  c + j + ∑ k ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (k + 1), |R (e i) k|

theorem le_fastCutoff (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (c : ℝ) (hc : 0 ≤ c) (i k j : ℕ) (hik : i ≤ k) (hkj : k ≤ j) :
    R (e i) k ≤ fastCutoff R e c j := by
  unfold fastCutoff
  have hinner : |R (e i) k| ≤ ∑ i' ∈ Finset.range (k + 1), |R (e i') k| :=
    Finset.single_le_sum (f := fun i' => |R (e i') k|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (show i < k + 1 by omega))
  have houter : ∑ i' ∈ Finset.range (k + 1), |R (e i') k| ≤
      ∑ k' ∈ Finset.range (j + 1), ∑ i' ∈ Finset.range (k' + 1), |R (e i') k'| :=
    Finset.single_le_sum (f := fun k' => ∑ i' ∈ Finset.range (k' + 1), |R (e i') k'|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (show k < j + 1 by omega))
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith [le_abs_self (R (e i) k)]

theorem const_le_fastCutoff (R : ChartTestSystem.Index → ℕ → ℝ)
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) (j : ℕ) : c ≤ fastCutoff R e c j := by
  unfold fastCutoff
  have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (k + 1), |R (e i) k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem nat_le_fastCutoff (R : ChartTestSystem.Index → ℕ → ℝ)
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) (hc : 0 ≤ c) (j : ℕ) :
    (j : ℝ) ≤ fastCutoff R e c j := by
  unfold fastCutoff
  have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (k + 1), |R (e i) k| :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  linarith

theorem tendsto_fastCutoff (R : ChartTestSystem.Index → ℕ → ℝ)
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fastCutoff R e c) atTop atTop :=
  tendsto_atTop_mono (nat_le_fastCutoff R e c hc) tendsto_natCast_atTop_atTop

/-- Each test of a chart system has cutoff `L¹` Cauchy thresholds at every geometric accuracy. -/
theorem exists_test_cauchy_thresholds
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ R : ChartTestSystem.Index → ℕ → ℝ, ∀ i k r s, R i k ≤ r → R i k ≤ s →
      ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r (T.allTest i) ω -
        admissibleCutoffIntegral P U dens Y γ s (T.allTest i) ω| ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
  have h : ∀ i : ChartTestSystem.Index, ∀ k : ℕ, ∃ R : ℝ, ∀ r s, R ≤ r → R ≤ s →
      ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r (T.allTest i) ω -
        admissibleCutoffIntegral P U dens Y γ s (T.allTest i) ω| ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ k) := by
    intro i k
    obtain ⟨R, hR⟩ := admissibleCutoffIntegral_L1_uniform_cauchy P U dens ε₀ Y hY (T.chart i)
      (T.chart_compact i) (T.chart_subset i) {γ} isCompact_singleton
      (Set.singleton_subset_iff.mpr ⟨hγ, hγ2⟩) ‖T.allTest i‖ ((1 / 2 : ℝ) ^ k) (by positivity)
    exact ⟨R, fun r s hr hs => hR r s hr hs γ rfl _ (T.allTest i).continuous.measurable
      (T.abs_allTest_le i) (T.allTest_eq_zero i)⟩
  choose R hR using h
  exact ⟨R, hR⟩

end DOZZ.Assembly

/-! ### The good set

The full-measure good set of the fast cutoff sequence.

Along the fast cutoff sequence the expected increments of every test are summable, so almost
surely every test converges; the unit chart masses are finite almost surely. On this good set,
uniform density and the mass-control cutoffs give convergence for every continuous test with
compact support in the chart. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Along the fast cutoff sequence, almost surely every test converges. -/
theorem ae_tendsto_allTest_fastCutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ)
    (hR : ∀ i k r s, R i k ≤ r → R i k ≤ s →
      ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r (T.allTest i) ω -
        admissibleCutoffIntegral P U dens Y γ s (T.allTest i) ω| ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) (hc : 0 ≤ c) (hcut : Real.exp (-c) ≤ ε₀) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, ∃ L : ℝ, Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ
      (fastCutoff R e c j) (T.allTest (e i)) ω) atTop (𝓝 L) := by
  apply ae_forall_tendsto_of_summable_lintegral_abs_increments P
    (fun i j ω => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) (T.allTest (e i)) ω)
    (fun i j => admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ _ _
      (T.allTest (e i)).continuous.measurable)
  intro i
  set t := T.allTest (e i)
  have hcutj (j : ℕ) : Real.exp (-fastCutoff R e c j) ≤ ε₀ :=
    le_trans (Real.exp_le_exp.mpr (by linarith [const_le_fastCutoff R e c j])) hcut
  set B : ℝ≥0∞ := 2 * (ENNReal.ofReal ‖t‖ * logRegularizationReference U dens (T.chart (e i)))
    with hBdef
  have hσ := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY
    (T.chart (e i)) (T.chart_compact _) (T.chart_subset _)
  have hBfin : B ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hσ)
  have hterm (j : ℕ) : ∫⁻ ω, ENNReal.ofReal
      |admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j.succ) t ω -
        admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) t ω| ∂P ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ j) + Set.indicator {j : ℕ | j < i} (fun _ => B) j := by
    by_cases hj : i ≤ j
    · refine le_trans (hR (e i) j _ _ (le_fastCutoff R e c hc i j (j + 1) hj (by omega))
        (le_fastCutoff R e c hc i j j hj le_rfl)).le le_self_add
    · rw [Set.indicator_of_mem (show j ∈ {j : ℕ | j < i} from by
        simp only [Set.mem_ofPred_eq]; omega)]
      refine le_trans ?_ le_add_self
      have hmeas (k : ℕ) : Measurable (admissibleCutoffIntegral P U dens Y γ
          (fastCutoff R e c k) t) :=
        admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ _ _ t.continuous.measurable
      have hbound (k : ℕ) := lintegral_ofReal_abs_admissibleCutoffIntegral_le P U dens ε₀ Y hY
        (T.chart (e i)) γ _ (hcutj k) ‖t‖ t t.continuous.measurable (T.abs_allTest_le _)
        (T.allTest_eq_zero _)
      calc _ ≤ ∫⁻ ω, (ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ
              (fastCutoff R e c j.succ) t ω| + ENNReal.ofReal |admissibleCutoffIntegral P U dens Y
              γ (fastCutoff R e c j) t ω|) ∂P := by
            apply lintegral_mono
            intro ω
            beta_reduce
            rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (abs_sub _ _)
        _ = _ := lintegral_add_left (ENNReal.measurable_ofReal.comp
            (continuous_abs.measurable.comp (hmeas j.succ))) _
        _ ≤ ENNReal.ofReal ‖t‖ * logRegularizationReference U dens (T.chart (e i)) +
            ENNReal.ofReal ‖t‖ * logRegularizationReference U dens (T.chart (e i)) :=
            add_le_add (hbound j.succ) (hbound j)
        _ = B := by rw [hBdef]; ring
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hterm)
  rw [ENNReal.tsum_add]
  refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
      (summable_geometric_of_lt_one (by norm_num) (by norm_num))]
    exact ENNReal.ofReal_ne_top
  · rw [tsum_eq_sum (s := Finset.range i) (fun j hj => by
      rw [Set.indicator_of_notMem (show j ∉ {j : ℕ | j < i} from by
        simpa using hj)])]
    exact ENNReal.sum_ne_top.mpr fun j _ => by
      by_cases hj : j < i
      · rw [Set.indicator_of_mem (show j ∈ {j : ℕ | j < i} from hj)]; exact hBfin
      · rw [Set.indicator_of_notMem (show j ∉ {j : ℕ | j < i} from hj)]; exact ENNReal.zero_ne_top

/-- Samples along which every test converges on the fast sequence and every unit chart mass is
finite. -/
def realizationGoodSet {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (T : ChartTestSystem U) (γ : ℝ) (R : ChartTestSystem.Index → ℕ → ℝ)
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) : Set Ω :=
  {ω | (∀ i : ℕ, ∃ L : ℝ, Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ
      (fastCutoff R e c j) (T.allTest (e i)) ω) atTop (𝓝 L)) ∧
    ∀ (j : ℕ) (i : ChartTestSystem.Index),
      chartUnitMass P U dens (T.chart i) Y γ (fastCutoff R e c j) ω ≠ ⊤}

theorem realizationGoodSet_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index) (c : ℝ) :
    MeasurableSet (realizationGoodSet P U dens Y T γ R e c) := by
  have h1 : MeasurableSet {ω | ∀ i : ℕ, ∃ L : ℝ, Tendsto (fun j => admissibleCutoffIntegral P U
      dens Y γ (fastCutoff R e c j) (T.allTest (e i)) ω) atTop (𝓝 L)} := by
    have heq : {ω | ∀ i : ℕ, ∃ L : ℝ, Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ
        (fastCutoff R e c j) (T.allTest (e i)) ω) atTop (𝓝 L)} = ⋂ i : ℕ, {ω | ∃ L : ℝ,
          Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j)
            (T.allTest (e i)) ω) atTop (𝓝 L)} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iInter fun i => StronglyMeasurable.measurableSet_exists_tendsto
      (fun j => (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ _ _
        (T.allTest (e i)).continuous.measurable).stronglyMeasurable)
  have h2 : MeasurableSet {ω | ∀ (j : ℕ) (i : ChartTestSystem.Index),
      chartUnitMass P U dens (T.chart i) Y γ (fastCutoff R e c j) ω ≠ ⊤} := by
    have heq : {ω | ∀ (j : ℕ) (i : ChartTestSystem.Index),
        chartUnitMass P U dens (T.chart i) Y γ (fastCutoff R e c j) ω ≠ ⊤} =
        ⋂ j : ℕ, ⋂ i : ChartTestSystem.Index,
          {ω | chartUnitMass P U dens (T.chart i) Y γ (fastCutoff R e c j) ω ≠ ⊤} := by
      ext ω; simp
    rw [heq]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun i =>
      (wickEventMass_measurable P U dens ε₀ Y hY _ γ _ Set.univ MeasurableSet.univ _
        measurable_const) (measurableSet_singleton (⊤ : ℝ≥0∞)).compl
  exact h1.inter h2

theorem ae_mem_realizationGoodSet
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ)
    (hR : ∀ i k r s, R i k ≤ r → R i k ≤ s →
      ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r (T.allTest i) ω -
        admissibleCutoffIntegral P U dens Y γ s (T.allTest i) ω| ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (e : ℕ → ChartTestSystem.Index) (c : ℝ) (hc : 0 ≤ c) (hcut : Real.exp (-c) ≤ ε₀) :
    ∀ᵐ ω ∂P, ω ∈ realizationGoodSet P U dens Y T γ R e c := by
  have h1 := ae_tendsto_allTest_fastCutoff P U dens ε₀ Y hY T γ R hR e c hc hcut
  have h2 : ∀ᵐ ω ∂P, ∀ (j : ℕ) (i : ChartTestSystem.Index),
      chartUnitMass P U dens (T.chart i) Y γ (fastCutoff R e c j) ω ≠ ⊤ := by
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro i
    exact chartUnitMass_ne_top_ae P U dens ε₀ Y hY (T.chart i) (T.chart_compact i)
      (T.chart_subset i) γ _
      (le_trans (Real.exp_le_exp.mpr (by linarith [const_le_fastCutoff R e c j])) hcut)
  filter_upwards [h1, h2] with ω hω₁ hω₂ using ⟨hω₁, hω₂⟩

end DOZZ.Assembly

/-! ### Limits of all continuous tests

On the good set, every continuous test with compact support in the chart converges along
the fast cutoff sequence.

A continuous test supported in an exhausting compact is uniformly within `δ` of a dense test;
the difference is dominated by `δ` times the mass-control cutoff, whose cutoff integrals stay
bounded. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- On the good set, a continuous test supported in an exhausting compact differs from a nearby
dense test by at most `δ` times the mass-control cutoff integral. -/
theorem abs_admissibleCutoffIntegral_sub_le_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ r : ℝ)
    (ω : Ω) (n : ℕ)
    (hω : chartUnitMass P U dens (T.chart (.inr n)) Y γ r ω ≠ ⊤)
    (g h : ℂ → ℝ) (hg : Measurable g) (hh : Measurable h) (Lg Lh : ℝ)
    (hgL : ∀ x, |g x| ≤ Lg) (hhL : ∀ x, |h x| ≤ Lh)
    (hgK : ∀ x ∉ T.K n, g x = 0) (hhK : ∀ x ∉ T.K n, h x = 0)
    (δ : ℝ) (hδ : 0 ≤ δ) (hclose : ∀ x, |g x - h x| ≤ δ) :
    |admissibleCutoffIntegral P U dens Y γ r g ω - admissibleCutoffIntegral P U dens Y γ r h ω| ≤
      δ * admissibleCutoffIntegral P U dens Y γ r (T.mass n) ω := by
  set S := T.chart (.inr n)
  have hKS : T.K n ⊆ S := T.K_subset_tsupport_mass n
  have hgS : ∀ x ∉ S, g x = 0 := fun x hx => hgK x (fun h' => hx (hKS h'))
  have hhS : ∀ x ∉ S, h x = 0 := fun x hx => hhK x (fun h' => hx (hKS h'))
  have hχm : Measurable (T.mass n : ℂ → ℝ) := (T.mass n).continuous.measurable
  have hχS : ∀ x ∉ S, (T.mass n : ℂ → ℝ) x = 0 := T.allTest_eq_zero (.inr n)
  have hχL : ∀ x, |(T.mass n : ℂ → ℝ) x| ≤ 1 := fun x => by
    rw [abs_le]; constructor <;> linarith [T.mass_nonneg n x, T.mass_le_one n x]
  have hdiffm : Measurable (fun x => g x - h x) := hg.sub hh
  have hdiffL : ∀ x, |g x - h x| ≤ Lg + Lh := fun x =>
    (abs_sub _ _).trans (add_le_add (hgL x) (hhL x))
  have hdiffS : ∀ x ∉ S, g x - h x = 0 := fun x hx => by rw [hgS x hx, hhS x hx, sub_zero]
  have hsplit : admissibleCutoffIntegral P U dens Y γ r g ω =
      admissibleCutoffIntegral P U dens Y γ r (fun x => g x - h x) ω +
        admissibleCutoffIntegral P U dens Y γ r h ω := by
    rw [← admissibleCutoffIntegral_add P U dens ε₀ Y hY S γ r ω hω (Lg + Lh) Lh _ h hdiffm hh
      hdiffL hhL hdiffS hhS]
    congr 1
    funext x
    ring
  have hband (x : ℂ) : |g x - h x| ≤ δ * (T.mass n : ℂ → ℝ) x := by
    by_cases hx : x ∈ T.K n
    · rw [T.mass_eq_one n x hx, mul_one]; exact hclose x
    · rw [hgK x hx, hhK x hx, sub_zero, abs_zero]
      exact mul_nonneg hδ (T.mass_nonneg n x)
  have hδχm : Measurable (fun x => δ * (T.mass n : ℂ → ℝ) x) := hχm.const_mul δ
  have hδχL : ∀ x, |δ * (T.mass n : ℂ → ℝ) x| ≤ δ := fun x => by
    rw [abs_mul, abs_of_nonneg hδ]
    calc δ * |(T.mass n : ℂ → ℝ) x| ≤ δ * 1 := mul_le_mul_of_nonneg_left (hχL x) hδ
      _ = δ := mul_one δ
  have hδχS : ∀ x ∉ S, δ * (T.mass n : ℂ → ℝ) x = 0 := fun x hx => by rw [hχS x hx, mul_zero]
  have hnegm : Measurable (fun x => -δ * (T.mass n : ℂ → ℝ) x) := hχm.const_mul (-δ)
  have hnegL : ∀ x, |-δ * (T.mass n : ℂ → ℝ) x| ≤ δ := fun x => by
    rw [neg_mul, abs_neg]; exact hδχL x
  have hnegS : ∀ x ∉ S, -δ * (T.mass n : ℂ → ℝ) x = 0 := fun x hx => by rw [hχS x hx, mul_zero]
  have hup := admissibleCutoffIntegral_mono P U dens ε₀ Y hY S γ r ω hω (Lg + Lh) δ _ _ hdiffm
    hδχm hdiffL hδχL hdiffS hδχS (fun x => (le_abs_self _).trans (hband x))
  have hlow := admissibleCutoffIntegral_mono P U dens ε₀ Y hY S γ r ω hω δ (Lg + Lh) _ _ hnegm
    hdiffm hnegL hdiffL hnegS hdiffS (fun x => by
      have := (neg_abs_le (g x - h x)).trans' (neg_le_neg (hband x))
      linarith)
  rw [admissibleCutoffIntegral_smul] at hup hlow
  rw [hsplit, add_sub_cancel_right, abs_le]
  constructor <;> linarith

/-- On the good set, every continuous test with compact support in the chart converges along the
fast cutoff sequence. -/
theorem exists_tendsto_fastCutoff_of_mem_goodSet
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (R : ChartTestSystem.Index → ℕ → ℝ) (e : ℕ → ChartTestSystem.Index)
    (he : Function.Surjective e) (c : ℝ) (ω : Ω)
    (hω : ω ∈ realizationGoodSet P U dens Y T γ R e c)
    (g : ℂ → ℝ) (hg : Continuous g) (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    ∃ L : ℝ, Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) g ω)
      atTop (𝓝 L) := by
  obtain ⟨n, hn⟩ := T.cofinal (tsupport g) hgc hgU
  have hgK : ∀ x ∉ T.K n, g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
    (fun h => hx (hn h))
  obtain ⟨Lg, hLg⟩ := hg.bounded_above_of_compact_support hgc
  have hgL : ∀ x, |g x| ≤ Lg := fun x => by rw [← Real.norm_eq_abs]; exact hLg x
  -- convergence of the mass-control cutoff
  obtain ⟨i₀, hi₀⟩ := he (.inr n)
  obtain ⟨Lχ, hLχ⟩ := hω.1 i₀
  rw [hi₀] at hLχ
  have hχconv : Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j)
      (T.mass n) ω) atTop (𝓝 Lχ) := hLχ
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto _ hχconv).exists_norm_le
  have hBj (j : ℕ) : admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) (T.mass n) ω ≤
      B := (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hB _ ⟨j, rfl⟩)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ ⟨0, rfl⟩)
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  set δ : ℝ := ε / (4 * (B + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨m, hm⟩ := T.dense n ⟨g, hg⟩ hgc hn δ hδ
  set h := T.test (n, m)
  obtain ⟨i₁, hi₁⟩ := he (.inl (n, m))
  obtain ⟨Lh, hLh⟩ := hω.1 i₁
  rw [hi₁] at hLh
  have hhconv : Tendsto (fun j => admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j)
      h ω) atTop (𝓝 Lh) := hLh
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hhconv.cauchySeq (ε / 2) (by linarith)
  refine ⟨N, fun a ha b hb => ?_⟩
  have hhK : ∀ x ∉ T.K n, (h : ℂ → ℝ) x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport
    (fun h' => hx (T.test_support (n, m) h'))
  have hclose : ∀ x, |g x - h x| ≤ δ := fun x => by
    have := hm x
    rw [Real.norm_eq_abs, abs_sub_comm] at this
    exact this.le
  have happrox (j : ℕ) : |admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) g ω -
      admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) h ω| ≤ δ * B := by
    refine (abs_admissibleCutoffIntegral_sub_le_mass P U dens ε₀ Y hY T γ _ ω n (hω.2 j (.inr n))
      g h hg.measurable h.continuous.measurable Lg ‖h‖ hgL (T.abs_allTest_le (.inl (n, m)))
      hgK hhK δ hδ.le hclose).trans ?_
    exact mul_le_mul_of_nonneg_left (hBj j) hδ.le
  have hδB : δ * B < ε / 4 := by
    rw [hδdef]
    have h4 : 0 < 4 * (B + 1) := by positivity
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ h4 (by norm_num)]
    nlinarith
  have hvab := hN a ha b hb
  rw [Real.dist_eq] at hvab ⊢
  have h1 := happrox a
  have h2 := happrox b
  calc |admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) g ω -
        admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) g ω|
      ≤ |admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) g ω -
          admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) h ω| +
        |admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) h ω -
          admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) h ω| +
        |admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) h ω -
          admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) g ω| := by
        calc _ = |(admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) g ω -
                admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) h ω) +
              (admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c a) h ω -
                admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) h ω) +
              (admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) h ω -
                admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) g ω)| := by ring_nf
          _ ≤ _ := abs_add_three _ _ _
    _ < ε / 4 + ε / 2 + ε / 4 := by
        rw [abs_sub_comm (admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c b) h ω)]
        have := hvab
        linarith
    _ = ε := by ring

end DOZZ.Assembly
