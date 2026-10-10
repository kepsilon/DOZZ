/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFF.TorusLocalDistribution
import Mathlib.Analysis.Distribution.TestFunction

/-!
# DOZZ.GFF.EquatorDistribution

The local Fourier charts are assembled with a smooth locally finite partition into compactly
supported pieces. This avoids any choice of incompatible radius chart for a single test.
-/

@[expose] public section

open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Distributions ENNReal InnerProductSpace Topology

namespace DOZZ

/-- A nested cutoff which is one on the ball of radius `n + 2`. -/
noncomputable def equatorGlobalCutoff (n : ℕ) : ℂ → ℝ :=
  localTorusCutoff ((n : ℝ) + 1) (by positivity)

theorem equatorGlobalCutoff_contDiff (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ENat)) (equatorGlobalCutoff n) := by
  simpa [equatorGlobalCutoff] using
    (localTorusCutoff ((n : ℝ) + 1) (by positivity)).contDiff

theorem equatorGlobalCutoff_eq_one (n : ℕ) {z : ℂ}
    (hz : z ∈ closedBall 0 ((n : ℝ) + 2)) : equatorGlobalCutoff n z = 1 := by
  have hrad : (n : ℝ) + 2 = ((n : ℝ) + 1) + 1 := by ring
  rw [hrad] at hz
  exact localTorusCutoff_eq_one ((n : ℝ) + 1) (by positivity)
    hz

theorem equatorGlobalCutoff_eq_zero_of_not_mem (n : ℕ) {z : ℂ}
    (hz : z ∉ closedBall 0 ((n : ℝ) + 3)) : equatorGlobalCutoff n z = 0 := by
  have hrad : (n : ℝ) + 3 = ((n : ℝ) + 1) + 2 := by ring
  rw [hrad] at hz
  have hnotsupp : z ∉ tsupport (equatorGlobalCutoff n) := by
    simpa [equatorGlobalCutoff, localTorusCutoff_tsupport] using hz
  have hnotsupport : z ∉ Function.support (equatorGlobalCutoff n) := fun hs =>
    hnotsupp (subset_tsupport _ hs)
  by_contra hne
  exact hnotsupport (Function.mem_support.mpr hne)

/-- The `n`th member of a telescoping smooth partition: the first cutoff, followed by successive
differences. -/
noncomputable def equatorPartitionFunction (n : ℕ) : ℂ → ℝ :=
  if n = 0 then equatorGlobalCutoff 0
  else equatorGlobalCutoff n - equatorGlobalCutoff (n - 1)

@[simp]
theorem equatorPartitionFunction_zero : equatorPartitionFunction 0 = equatorGlobalCutoff 0 := by
  simp [equatorPartitionFunction]

theorem equatorPartitionFunction_succ (n : ℕ) :
    equatorPartitionFunction (n + 1) = equatorGlobalCutoff (n + 1) - equatorGlobalCutoff n := by
  simp [equatorPartitionFunction]

theorem equatorPartitionFunction_contDiff (n : ℕ) :
    ContDiff ℝ (↑(⊤ : ENat)) (equatorPartitionFunction n) := by
  unfold equatorPartitionFunction
  split_ifs
  · simpa [equatorGlobalCutoff] using
      (localTorusCutoff (1 : ℝ) (by norm_num)).contDiff
  · exact (equatorGlobalCutoff_contDiff n).sub (equatorGlobalCutoff_contDiff (n - 1))

theorem equatorPartitionFunction_eq_zero_of_not_mem (n : ℕ) {z : ℂ}
    (hz : z ∉ closedBall 0 ((n : ℝ) + 3)) : equatorPartitionFunction n z = 0 := by
  by_cases hn : n = 0
  · subst n
    rw [equatorPartitionFunction_zero]
    exact equatorGlobalCutoff_eq_zero_of_not_mem 0 (by simpa using hz)
  · rw [equatorPartitionFunction, ite_eq_right hn]
    have hcur := equatorGlobalCutoff_eq_zero_of_not_mem n hz
    have hprev : equatorGlobalCutoff (n - 1) z = 0 := by
      apply equatorGlobalCutoff_eq_zero_of_not_mem
      intro hzprev
      apply hz
      exact closedBall_subset_closedBall (by
        have hn' : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast Nat.sub_le n 1
        linarith) hzprev
    simp [hcur, hprev]

theorem equatorPartitionFunction_support_subset (n : ℕ) :
    Function.support (equatorPartitionFunction n) ⊆ closedBall 0 ((n : ℝ) + 3) := by
  apply Function.support_subset_iff'.2
  intro z hz
  exact equatorPartitionFunction_eq_zero_of_not_mem n hz


/-- The finite telescoping identity for the smooth partition. -/
theorem sum_equatorPartitionFunction_range (N : ℕ) (z : ℂ) :
    (∑ n ∈ Finset.range (N + 1), equatorPartitionFunction n z) =
      equatorGlobalCutoff N z := by
  induction N with
  | zero => simp [equatorPartitionFunction_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [equatorPartitionFunction_succ]
      rw [ih]
      rw [Pi.sub_apply]
      ring

/-- Multiplication by one member of the smooth partition, as a continuous map on tests. -/
noncomputable def equatorPartitionCLM (n : ℕ) : TestFn →L[ℝ] TestFn :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.lsmul ℝ ℝ)
    (equatorPartitionFunction_contDiff n)

@[simp]
theorem equatorPartitionCLM_apply (n : ℕ) (f : TestFn) :
    equatorPartitionCLM n f = fun z => f z * equatorPartitionFunction n z := by
  ext z
  simp [equatorPartitionCLM, TestFunction.bilinLeftCLM_apply]

theorem exists_nat_equatorPartition_tail_zero (f : TestFn) :
    ∃ N : ℕ, ∀ n ≥ N + 1, equatorPartitionCLM n f = 0 := by
  obtain ⟨R, hR, hball⟩ :=
    f.hasCompactSupport.isBounded.subset_ball_lt (0 : ℝ) (0 : ℂ)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R + 1 < N := exists_nat_gt (R + 1)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : N ≤ n := by omega
  have hnReal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hprevNat : N ≤ n - 1 := by omega
  have hprevReal : (N : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hprevNat
  ext z
  rw [equatorPartitionCLM_apply]
  by_cases hz : z ∈ tsupport f
  · have hzball : z ∈ ball (0 : ℂ) R := hball hz
    have hnorm : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hzball
    have hbase : z ∈ closedBall (0 : ℂ) ((N : ℝ) + 2) := by
      have hnormle : ‖z‖ ≤ (N : ℝ) + 2 := by linarith
      simpa [mem_closedBall, dist_eq_norm] using hnormle
    have hcur : equatorGlobalCutoff n z = 1 := by
      apply equatorGlobalCutoff_eq_one n
      exact closedBall_subset_closedBall (by linarith) hbase
    have hprev : equatorGlobalCutoff (n - 1) z = 1 := by
      apply equatorGlobalCutoff_eq_one (n - 1)
      exact closedBall_subset_closedBall (by linarith) hbase
    change f z * equatorPartitionFunction n z = 0
    rw [equatorPartitionFunction, ite_eq_right (by omega : n ≠ 0)]
    change f z * (equatorGlobalCutoff n z -
      equatorGlobalCutoff (n - 1) z) = 0
    rw [hcur, hprev]
    simp
  · have hfz : f z = 0 := by
      by_contra hne
      exact hz (Function.mem_support.mpr hne |> subset_tsupport f)
    simp [hfz]

theorem exists_nat_equatorPartition_zero_on_compact
    (K : TopologicalSpace.Compacts ℂ) :
    ∃ N : ℕ, ∀ n ≥ N + 1, ∀ z ∈ (K : Set ℂ),
      equatorPartitionFunction n z = 0 := by
  obtain ⟨R, hR, hball⟩ :=
    K.isCompact.isBounded.subset_ball_lt (0 : ℝ) (0 : ℂ)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R + 1 < N := exists_nat_gt (R + 1)
  refine ⟨N, fun n hn z hz => ?_⟩
  have hnN : N ≤ n := by omega
  have hnReal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hprevNat : N ≤ n - 1 := by omega
  have hprevReal : (N : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hprevNat
  have hzball : z ∈ ball (0 : ℂ) R := hball hz
  have hnorm : ‖z‖ < R := by simpa [mem_ball, dist_eq_norm] using hzball
  have hbase : z ∈ closedBall (0 : ℂ) ((N : ℝ) + 2) := by
    have hnormle : ‖z‖ ≤ (N : ℝ) + 2 := by linarith
    simpa [mem_closedBall, dist_eq_norm] using hnormle
  have hcur : equatorGlobalCutoff n z = 1 := by
    apply equatorGlobalCutoff_eq_one n
    exact closedBall_subset_closedBall (by linarith) hbase
  have hprev : equatorGlobalCutoff (n - 1) z = 1 := by
    apply equatorGlobalCutoff_eq_one (n - 1)
    exact closedBall_subset_closedBall (by linarith) hbase
  rw [equatorPartitionFunction, ite_eq_right (by omega : n ≠ 0), Pi.sub_apply, hcur, hprev]
  simp

/-- The local continuous distribution selected for a sample in the full-measure event. -/
noncomputable def equatorLocalChartCLM (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) : TestFn →L[ℝ] ℝ :=
  equatorLocalFourierDistributionCLM R ω
    (equatorHaarCommonCosEval_summable_of_good R ω hω)
    (equatorHaarCommonSinEval_summable_of_good R ω hω)

/-- The `n`th compactly supported local Fourier chart applied to the `n`th partition piece. -/
noncomputable def equatorDistributionTerm (n : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) : TestFn →L[ℝ] ℝ :=
  (equatorLocalChartCLM (n + 5) ω hω).comp (equatorPartitionCLM n)

@[simp]
theorem equatorDistributionTerm_apply (n : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) (f : TestFn) :
    equatorDistributionTerm n ω hω f =
      equatorLocalChartCLM (n + 5) ω hω (equatorPartitionCLM n f) := rfl

/-- A local Fourier evaluation of the zero test is zero. -/
@[simp]
theorem equatorLocalFourierEval_zero (R : ℕ)
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) :
    equatorLocalFourierEval R 0 ω = 0 := by
  unfold equatorLocalFourierEval
  have hzero : (fun s => equatorLocalFourierPartialEval R 0 s ω) = fun _ => 0 := by
    funext s
    simp [equatorLocalFourierPartialEval]
  rw [hzero]
  exact Filter.Tendsto.limUnder_eq tendsto_const_nhds

/-- Finite partial sums of the partitioned local chart evaluations. -/
noncomputable def equatorDistributionPartialSum
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N,
    equatorLocalFourierEval (n + 5) (equatorPartitionCLM n f) ω

/-- The scalar limit of the partitioned local evaluations. On the good event the series is
eventually constant for each test. -/
noncomputable def equatorDistributionSeriesEval
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) : ℝ :=
  limUnder atTop (equatorDistributionPartialSum ω f)

/-- The global test evaluation, set to zero on the exceptional null set. -/
noncomputable def equatorDistributionEval
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) : ℝ :=
  by classical
    exact if equatorHaarCommonGood ω then equatorDistributionSeriesEval ω f else 0

theorem measurable_equatorDistributionPartialSum
    (f : TestFn) (N : ℕ) :
    Measurable (fun ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2 =>
      equatorDistributionPartialSum ω f N) := by
  unfold equatorDistributionPartialSum
  apply Finset.measurable_fun_sum
  intro n hn
  exact measurable_equatorLocalFourierEval (n + 5) (equatorPartitionCLM n f)

theorem measurable_equatorDistributionSeriesEval (f : TestFn) :
    Measurable (equatorDistributionSeriesEval · f) := by
  have hstrong : ∀ N, StronglyMeasurable (fun ω =>
      equatorDistributionPartialSum ω f N) :=
    fun N => (measurable_equatorDistributionPartialSum f N).stronglyMeasurable
  exact (StronglyMeasurable.limUnder (l := atTop) hstrong).measurable

theorem measurable_equatorDistributionEval (f : TestFn) :
    Measurable (equatorDistributionEval · f) := by
  classical
  unfold equatorDistributionEval
  exact Measurable.ite measurableSet_equatorHaarCommonGood
    (measurable_equatorDistributionSeriesEval f) measurable_const

theorem equatorDistributionPartialSum_eventually_const_of_tail_zero
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) (N : ℕ)
    (hN : ∀ n ≥ N + 1, equatorPartitionCLM n f = 0) :
    ∀ᶠ m in atTop,
      equatorDistributionPartialSum ω f m =
        equatorDistributionPartialSum ω f (N + 1) := by
  apply Filter.eventually_atTop.2
  refine ⟨N + 1, fun m hm => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have htail : ∀ d : ℕ,
      equatorDistributionPartialSum ω f ((N + 1) + d) =
        equatorDistributionPartialSum ω f (N + 1) := by
    intro d
    induction d with
    | zero => rfl
    | succ d ih =>
        have hindex : (N + 1) + (d + 1) = ((N + 1) + d) + 1 := by omega
        rw [hindex]
        unfold equatorDistributionPartialSum at *
        rw [Finset.sum_range_succ, ih, hN ((N + 1) + d) (by omega)]
        simp
  exact htail d

theorem equatorDistributionPartialSum_eventually_const
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) :
    ∃ N : ℕ, ∀ᶠ m in atTop,
      equatorDistributionPartialSum ω f m =
        equatorDistributionPartialSum ω f (N + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_equatorPartition_tail_zero f
  exact ⟨N, equatorDistributionPartialSum_eventually_const_of_tail_zero ω f N hN⟩

theorem equatorDistributionPartialSum_tendsto
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) :
    Tendsto (equatorDistributionPartialSum ω f) atTop
      (𝓝 (equatorDistributionSeriesEval ω f)) := by
  obtain ⟨N, hconst⟩ := equatorDistributionPartialSum_eventually_const ω f
  have hconst' : (fun _ : ℕ => equatorDistributionPartialSum ω f (N + 1)) =ᶠ[atTop]
      equatorDistributionPartialSum ω f := hconst.mono fun _ h => h.symm
  have htendsto : Tendsto (equatorDistributionPartialSum ω f) atTop
      (𝓝 (equatorDistributionPartialSum ω f (N + 1))) :=
    tendsto_const_nhds.congr' hconst'
  have hlim := htendsto.limUnder_eq
  change Tendsto (equatorDistributionPartialSum ω f) atTop
    (𝓝 (limUnder atTop (equatorDistributionPartialSum ω f)))
  rw [hlim]
  exact htendsto

theorem equatorDistributionSeriesEval_eq_partialSum_of_tail_zero
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) (N : ℕ)
    (hN : ∀ n ≥ N + 1, equatorPartitionCLM n f = 0) :
    equatorDistributionSeriesEval ω f =
      equatorDistributionPartialSum ω f (N + 1) := by
  have hconst :=
    equatorDistributionPartialSum_eventually_const_of_tail_zero ω f N hN
  have hconst' : (fun _ : ℕ => equatorDistributionPartialSum ω f (N + 1)) =ᶠ[atTop]
      equatorDistributionPartialSum ω f := hconst.mono fun _ h => h.symm
  have htendsto : Tendsto (equatorDistributionPartialSum ω f) atTop
      (𝓝 (equatorDistributionPartialSum ω f (N + 1))) :=
    tendsto_const_nhds.congr' hconst'
  change limUnder atTop (equatorDistributionPartialSum ω f) = _
  exact htendsto.limUnder_eq

theorem equatorLocalFourierEval_eq_equatorLocalChartCLM
    (R : ℕ) (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) (f : TestFn) :
    equatorLocalFourierEval R f ω = equatorLocalChartCLM R ω hω f := by
  unfold equatorLocalChartCLM
  exact equatorLocalFourierEval_eq_distributionCLM_apply R f ω
    (equatorHaarCommonCosEval_summable_of_good R ω hω)
    (equatorHaarCommonSinEval_summable_of_good R ω hω)

theorem equatorDistributionPartialSum_add
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) (f g : TestFn) (N : ℕ) :
    equatorDistributionPartialSum ω (f + g) N =
      equatorDistributionPartialSum ω f N + equatorDistributionPartialSum ω g N := by
  unfold equatorDistributionPartialSum
  calc
    _ = ∑ n ∈ Finset.range N,
        (equatorLocalFourierEval (n + 5) (equatorPartitionCLM n f) ω +
          equatorLocalFourierEval (n + 5) (equatorPartitionCLM n g) ω) := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = equatorLocalChartCLM (n + 5) ω hω
            (equatorPartitionCLM n (f + g)) :=
          equatorLocalFourierEval_eq_equatorLocalChartCLM (n + 5) ω hω _
        _ = equatorLocalChartCLM (n + 5) ω hω
            (equatorPartitionCLM n f + equatorPartitionCLM n g) := by
          rw [(equatorPartitionCLM n).map_add]
        _ = equatorLocalChartCLM (n + 5) ω hω (equatorPartitionCLM n f) +
            equatorLocalChartCLM (n + 5) ω hω (equatorPartitionCLM n g) := by
          rw [(equatorLocalChartCLM (n + 5) ω hω).map_add]
        _ = _ := by
          rw [← equatorLocalFourierEval_eq_equatorLocalChartCLM (n + 5) ω hω _,
            ← equatorLocalFourierEval_eq_equatorLocalChartCLM (n + 5) ω hω _]
    _ = _ := rfl
    _ = _ := by rw [Finset.sum_add_distrib]

theorem equatorDistributionPartialSum_smul
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (hω : equatorHaarCommonGood ω) (c : ℝ) (f : TestFn) (N : ℕ) :
    equatorDistributionPartialSum ω (c • f) N =
      c • equatorDistributionPartialSum ω f N := by
  unfold equatorDistributionPartialSum
  calc
    _ = ∑ n ∈ Finset.range N,
        c • equatorLocalFourierEval (n + 5) (equatorPartitionCLM n f) ω := by
      apply Finset.sum_congr rfl
      intro n hn
      calc
        _ = equatorLocalChartCLM (n + 5) ω hω
            (equatorPartitionCLM n (c • f)) :=
          equatorLocalFourierEval_eq_equatorLocalChartCLM (n + 5) ω hω _
        _ = equatorLocalChartCLM (n + 5) ω hω
            (c • equatorPartitionCLM n f) := by
          rw [(equatorPartitionCLM n).map_smul]
        _ = c • equatorLocalChartCLM (n + 5) ω hω
            (equatorPartitionCLM n f) := by
          rw [(equatorLocalChartCLM (n + 5) ω hω).map_smul]
        _ = _ := by
          rw [← equatorLocalFourierEval_eq_equatorLocalChartCLM (n + 5) ω hω _]
    _ = _ := by rw [Finset.smul_sum]

theorem equatorDistributionEval_add
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (f g : TestFn) :
    equatorDistributionEval ω (f + g) =
      equatorDistributionEval ω f + equatorDistributionEval ω g := by
  classical
  by_cases hω : equatorHaarCommonGood ω
  · have hf := equatorDistributionPartialSum_tendsto ω f
    have hg := equatorDistributionPartialSum_tendsto ω g
    have hfg := equatorDistributionPartialSum_tendsto ω (f + g)
    have hlim := hf.add hg
    have hcongr : (fun N => equatorDistributionPartialSum ω (f + g) N) =ᶠ[atTop]
        fun N => equatorDistributionPartialSum ω f N +
          equatorDistributionPartialSum ω g N :=
      Filter.Eventually.of_forall fun N =>
        equatorDistributionPartialSum_add ω hω f g N
    have hlim' := hlim.congr' hcongr.symm
    have hEq := tendsto_nhds_unique hfg hlim'
    simpa [equatorDistributionEval, hω] using hEq
  · simp [equatorDistributionEval, hω]

theorem equatorDistributionEval_smul
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2)
    (c : ℝ) (f : TestFn) :
    equatorDistributionEval ω (c • f) =
      c • equatorDistributionEval ω f := by
  classical
  by_cases hω : equatorHaarCommonGood ω
  · have hf := equatorDistributionPartialSum_tendsto ω f
    have hcf := equatorDistributionPartialSum_tendsto ω (c • f)
    have hlim := hf.const_smul c
    have hcongr : (fun N => equatorDistributionPartialSum ω (c • f) N) =ᶠ[atTop]
        fun N => c • equatorDistributionPartialSum ω f N :=
      Filter.Eventually.of_forall fun N =>
        equatorDistributionPartialSum_smul ω hω c f N
    have hlim' := hlim.congr' hcongr.symm
    have hEq := tendsto_nhds_unique hcf hlim'
    simpa [equatorDistributionEval, hω] using hEq
  · simp [equatorDistributionEval, hω]

theorem equatorPartitionCLM_zero_of_supportedIn
    (K : TopologicalSpace.Compacts ℂ) (hK : (K : Set ℂ) ⊆ Set.univ)
    (f : GFFLocalTest K) (n : ℕ)
    (hcut : ∀ z ∈ (K : Set ℂ), equatorPartitionFunction n z = 0) :
    equatorPartitionCLM n (TestFunction.ofSupportedIn hK f) = 0 := by
  ext z
  rw [equatorPartitionCLM_apply]
  by_cases hz : z ∈ (K : Set ℂ)
  · change (TestFunction.ofSupportedIn hK f) z *
      equatorPartitionFunction n z = (0 : ℝ)
    rw [hcut z hz]
    simp
  · have hfz : f z = 0 := f.zero_on_compl hz
    simp [hfz]

/-- The global random distribution on the common full-measure event. -/
noncomputable def equatorDistributionCLM
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) : Distr := by
  classical
  refine TestFunction.mkCLM ℝ (equatorDistributionEval ω) ?_ ?_ ?_
  · exact equatorDistributionEval_add ω
  · exact equatorDistributionEval_smul ω
  · intro K hK
    by_cases hω : equatorHaarCommonGood ω
    · obtain ⟨N, hcut⟩ := exists_nat_equatorPartition_zero_on_compact K
      have hfinite (f : GFFLocalTest K) :
          equatorDistributionEval ω (TestFunction.ofSupportedIn hK f) =
            ∑ n ∈ Finset.range (N + 1),
              equatorDistributionTerm n ω hω (TestFunction.ofSupportedIn hK f) := by
        have htail (n : ℕ) (hn : N + 1 ≤ n) :
            equatorPartitionCLM n (TestFunction.ofSupportedIn hK f) = 0 :=
          equatorPartitionCLM_zero_of_supportedIn K hK f n (hcut n hn)
        have hseries := equatorDistributionSeriesEval_eq_partialSum_of_tail_zero
          ω (TestFunction.ofSupportedIn hK f) N htail
        simp only [equatorDistributionEval, ite_eq_left hω]
        rw [hseries]
        unfold equatorDistributionPartialSum
        apply Finset.sum_congr rfl
        intro n hn
        calc
          _ = equatorLocalChartCLM (n + 5) ω hω
              (equatorPartitionCLM n (TestFunction.ofSupportedIn hK f)) :=
            equatorLocalFourierEval_eq_equatorLocalChartCLM (n + 5) ω hω _
          _ = equatorDistributionTerm n ω hω (TestFunction.ofSupportedIn hK f) := rfl
      have hfun :
          (fun f : GFFLocalTest K =>
              equatorDistributionEval ω (TestFunction.ofSupportedIn hK f)) =
            fun f => ∑ n ∈ Finset.range (N + 1),
              equatorDistributionTerm n ω hω (TestFunction.ofSupportedIn hK f) := by
        funext f
        exact hfinite f
      change Continuous (fun f : GFFLocalTest K =>
        equatorDistributionEval ω (TestFunction.ofSupportedIn hK f))
      rw [hfun]
      exact continuous_finsetSum _ fun n hn =>
        ((equatorDistributionTerm n ω hω).comp
          (TestFunction.ofSupportedInCLM ℝ hK)).continuous
    · have hzero : (fun f : GFFLocalTest K =>
          equatorDistributionEval ω (TestFunction.ofSupportedIn hK f)) = fun _ => 0 := by
        funext f
        simp [equatorDistributionEval, hω]
      change Continuous (fun f : GFFLocalTest K =>
        equatorDistributionEval ω (TestFunction.ofSupportedIn hK f))
      rw [hzero]
      exact continuous_const

/-- The samplewise distribution-valued equator field. -/
noncomputable def equatorGFFDistribution :
    GaussianFields.ScaleSpaceWhiteNoiseSpace 2 → Distr :=
  equatorDistributionCLM

@[simp]
theorem equatorGFFDistribution_apply
    (ω : GaussianFields.ScaleSpaceWhiteNoiseSpace 2) (f : TestFn) :
    equatorGFFDistribution ω f = equatorDistributionEval ω f := rfl

theorem measurable_equatorGFFDistribution_apply (f : TestFn) :
    Measurable (fun ω => equatorGFFDistribution ω f) := by
  simpa using measurable_equatorDistributionEval f

end DOZZ

end
