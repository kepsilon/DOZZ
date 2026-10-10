/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.AdmissibleCircleTestFatou
public import DOZZ.GMC.Construction.ReferenceMeasureFinite
public import DOZZ.GMC.Construction.FiniteMeasureTotalize
public import DOZZ.GMC.Construction.ReferenceMeasureTight
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Construction.CircleCutoffTestMass
public import DOZZ.GMC.CircleAverageCutoffIntensity
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! An admissible whole-plane circle-chaos version has finite expected total mass. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Distributions CompactlySupported

noncomputable section

namespace DOZZ.Proofs

private def massCutoffFun (n : ℕ) : ℂ → ℝ :=
  fun x => max 0 (min 1 ((n : ℝ) + 1 - ‖x‖))

private theorem massCutoffFun_continuous (n : ℕ) : Continuous (massCutoffFun n) := by
  change Continuous (fun x : ℂ => max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)))
  fun_prop

private theorem massCutoffFun_support (n : ℕ) :
    Function.support (massCutoffFun n) ⊆ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) := by
  intro x hx
  change massCutoffFun n x ≠ 0 at hx
  have hfx : massCutoffFun n x ≠ 0 := hx
  by_contra hout
  have hn : (n : ℝ) + 1 - ‖x‖ ≤ 0 := by
    have hxnorm : dist x (0 : ℂ) = ‖x‖ := by simp
    rw [Metric.mem_closedBall, hxnorm] at hout
    linarith
  have hzero : massCutoffFun n x = 0 := by
    dsimp [massCutoffFun]
    rw [max_eq_left (le_trans (min_le_right _ _) hn)]
  exact hfx hzero

private def massCutoffCc (n : ℕ) : C_c(ℂ, ℝ) := by
  let f : C(ℂ, ℝ) := ⟨massCutoffFun n, massCutoffFun_continuous n⟩
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) (massCutoffFun_support n)
  exact ⟨f, hcompact⟩

private def massCutoff (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (massCutoffCc n).toBoundedContinuousFunction

private theorem massCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (massCutoff n : ℂ → ℝ) := by
  exact (massCutoffCc n).hasCompactSupport

private theorem massCutoff_nonneg (n : ℕ) (x : ℂ) : 0 ≤ massCutoff n x := by
  simp [massCutoff, massCutoffCc, massCutoffFun,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction]

private theorem massCutoff_le_one (n : ℕ) (x : ℂ) : massCutoff n x ≤ 1 := by
  simp only [massCutoff, massCutoffCc,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction]
  change max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) ≤ 1
  exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

private theorem massCutoff_eq_one_of_mem_closedBall (n : ℕ) (x : ℂ)
    (hx : x ∈ Metric.closedBall (0 : ℂ) (n : ℝ)) : massCutoff n x = 1 := by
  have hnorm : ‖x‖ ≤ (n : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have harg : 1 ≤ (n : ℝ) + 1 - ‖x‖ := by linarith
  simp [massCutoff, massCutoffCc, massCutoffFun,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction, min_eq_left harg]

private theorem massCutoff_zero_of_not_mem_closedBall (n : ℕ) (x : ℂ)
    (hx : x ∉ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1)) : massCutoff n x = 0 := by
  have hnorm : (n : ℝ) + 1 < ‖x‖ := by
    have hnot : ¬ ‖x‖ ≤ (n : ℝ) + 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact lt_of_not_ge hnot
  have harg : (n : ℝ) + 1 - ‖x‖ ≤ 0 := by linarith
  simp [massCutoff, massCutoffCc, massCutoffFun,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction,
    max_eq_left (le_trans (min_le_right _ _) harg)]

private def cutoffTest (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) :
    BoundedContinuousFunction ℂ ℝ := f * massCutoff R

private theorem cutoffTest_hasCompactSupport (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) :
    HasCompactSupport (cutoffTest f R : ℂ → ℝ) := by
  let g : ℂ → ℝ := fun x => f x * massCutoff R x
  have hgcont : Continuous g := by
    dsimp [g]
    exact f.continuous.mul (massCutoff R).continuous
  have hgsupport : Function.support g ⊆ Metric.closedBall (0 : ℂ) ((R : ℝ) + 1) := by
    intro x hx
    change g x ≠ 0 at hx
    by_contra hout
    have hzero : massCutoff R x = 0 := massCutoff_zero_of_not_mem_closedBall R x hout
    exact hx (by simp [g, hzero])
  exact HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℂ) ((R : ℝ) + 1)) (by simpa [g, cutoffTest] using hgsupport)

/-- A bounded continuous test changes by at most its sup norm times the mass outside the radius-R
disk when cut off by the compact radial exhaustion. -/
private theorem circleIntegral_cutoff_error_le
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (f : BoundedContinuousFunction ℂ ℝ) (R : ℕ) :
    ‖∫ x, f x ∂μ - ∫ x, cutoffTest f R x ∂μ‖ ≤
      ‖f‖ * (μ (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ).toReal := by
  classical
  let tail : Set ℂ := (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ
  have htail : MeasurableSet tail :=
    (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (R : ℝ))).measurableSet.compl
  have hfmem : MemLp (fun x => f x) 1 μ :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (ae_of_all _ f.norm_coe_le_norm)
  have hfint : Integrable (fun x => f x) μ := hfmem.integrable (by norm_num)
  have hgf : Measurable (fun x : ℂ => cutoffTest f R x) :=
    (cutoffTest f R).continuous.measurable
  have hgmem : MemLp (fun x => cutoffTest f R x) 1 μ :=
    MemLp.of_bound hgf.aestronglyMeasurable ‖cutoffTest f R‖
      (ae_of_all _ (cutoffTest f R).norm_coe_le_norm)
  have hgint : Integrable (fun x => cutoffTest f R x) μ := hgmem.integrable (by norm_num)
  let d : ℂ → ℝ := fun x => f x - cutoffTest f R x
  have hdint : Integrable d μ := hfint.sub hgint
  have htailConst : Integrable (tail.indicator (fun _ : ℂ => ‖f‖)) μ := by
    have hcLp : MemLp (fun _ : ℂ => ‖f‖) 1 μ :=
      MemLp.of_bound (aestronglyMeasurable_const : AEStronglyMeasurable
        (fun _ : ℂ => ‖f‖) μ) ‖f‖ (ae_of_all _ fun _ => by simp)
    have hc : Integrable (fun _ : ℂ => ‖f‖) μ := hcLp.integrable (by norm_num)
    exact hc.indicator htail
  have hpoint : ∀ x, ‖d x‖ ≤ tail.indicator (fun _ : ℂ => ‖f‖) x := by
    intro x
    by_cases hx : x ∈ tail
    · have hχnonneg : 0 ≤ massCutoff R x := massCutoff_nonneg R x
      have hχle : massCutoff R x ≤ 1 := massCutoff_le_one R x
      have habs : |1 - massCutoff R x| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have hdeq : d x = f x * (1 - massCutoff R x) := by
        change f x - f x * massCutoff R x = f x * (1 - massCutoff R x)
        ring
      rw [hdeq, Real.norm_eq_abs, abs_mul]
      simp [Set.indicator, hx]
      calc
        |f x| * |1 - massCutoff R x| ≤ |f x| := by
          simpa using mul_le_mul_of_nonneg_left habs (abs_nonneg (f x))
        _ ≤ ‖f‖ := by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
    · have hxball : x ∈ Metric.closedBall (0 : ℂ) (R : ℝ) := by
        simpa [tail, Set.mem_compl_iff] using hx
      have hχ := massCutoff_eq_one_of_mem_closedBall R x hxball
      have hdzero : d x = 0 := by simp [d, cutoffTest, hχ]
      simp [Set.indicator, hx, hdzero]
  calc
    ‖∫ x, f x ∂μ - ∫ x, cutoffTest f R x ∂μ‖ = ‖∫ x, d x ∂μ‖ := by
      rw [integral_sub hfint hgint]
    _ ≤ ∫ x, ‖d x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, tail.indicator (fun _ : ℂ => ‖f‖) x ∂μ :=
      integral_mono hdint.norm htailConst hpoint
    _ = ‖f‖ * (μ tail).toReal := by
      rw [integral_indicator_const ‖f‖ htail]
      rw [Measure.real_def]
      simp [tail, smul_eq_mul]
      ring

private theorem massCutoff_mono (x : ℂ) : Monotone fun n => massCutoff n x := by
  intro n m hnm
  simp only [massCutoff, massCutoffCc,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction]
  change max 0 (min 1 ((n : ℝ) + 1 - ‖x‖)) ≤
    max 0 (min 1 ((m : ℝ) + 1 - ‖x‖))
  exact max_le_max le_rfl (min_le_min le_rfl (by
    have hcast : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
    linarith))

private theorem massCutoff_tendsto_one (x : ℂ) :
    Tendsto (fun n : ℕ => massCutoff n x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  have hEvent : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 - ‖x‖ ≥ 1 := by
    exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
      have hnorm : ‖x‖ < (N : ℝ) := by exact_mod_cast hN
      have hnReal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hle : ‖x‖ ≤ (n : ℝ) := le_trans hnorm.le hnReal
      have hnonneg : 0 ≤ (n : ℝ) - ‖x‖ := sub_nonneg.mpr hle
      linarith⟩
  have hEq : ∀ᶠ n : ℕ in atTop, massCutoff n x = 1 := by
    filter_upwards [hEvent] with n hn
    simp [massCutoff, massCutoffCc,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction, massCutoffFun, hn]
  have hEq' : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] fun n => massCutoff n x :=
    hEq.mono fun _ hn => hn.symm
  exact tendsto_const_nhds.congr' hEq'

private theorem massCutoff_lintegral_tendsto (μ : Measure ℂ) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂μ) atTop
      (𝓝 (μ Set.univ)) := by
  have hmeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (massCutoff n x)) μ := by
    exact (ENNReal.measurable_ofReal.comp (massCutoff n).continuous.measurable).aemeasurable
  have hmono : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (massCutoff n x) :=
    ae_of_all _ fun x n m hnm => ENNReal.ofReal_le_ofReal (massCutoff_mono x hnm)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ENNReal.ofReal (massCutoff n x)) atTop
      (𝓝 (1 : ℝ≥0∞)) := by
    filter_upwards [] with x
    simpa using ENNReal.tendsto_ofReal (massCutoff_tendsto_one x)
  have h := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim
  simpa using h

private def tailInnerFun (R : ℕ) (x : ℂ) : ℝ :=
  max 0 (min 1 (‖x‖ - (R : ℝ)))

private theorem tailInnerFun_continuous (R : ℕ) : Continuous (tailInnerFun R) := by
  change Continuous (fun x : ℂ => max 0 (min 1 (‖x‖ - (R : ℝ))))
  fun_prop

private theorem tailInnerFun_nonneg (R : ℕ) (x : ℂ) : 0 ≤ tailInnerFun R x :=
  le_max_left _ _

private theorem tailInnerFun_le_one (R : ℕ) (x : ℂ) : tailInnerFun R x ≤ 1 := by
  dsimp [tailInnerFun]
  exact max_le_iff.mpr ⟨by norm_num, min_le_left _ _⟩

private def tailTestFun (R n : ℕ) (x : ℂ) : ℝ :=
  tailInnerFun R x * massCutoffFun n x

private theorem tailTestFun_continuous (R n : ℕ) : Continuous (tailTestFun R n) := by
  exact (tailInnerFun_continuous R).mul (massCutoffFun_continuous n)

private theorem tailTestFun_support (R n : ℕ) :
    Function.support (tailTestFun R n) ⊆ Metric.closedBall (0 : ℂ) ((n : ℝ) + 1) := by
  intro x hx
  change tailTestFun R n x ≠ 0 at hx
  by_contra hout
  have hcut : massCutoffFun n x = 0 := by
    by_contra hne
    apply hout
    exact massCutoffFun_support n (by change massCutoffFun n x ≠ 0; exact hne)
  have hzero : tailTestFun R n x = 0 := by simp [tailTestFun, hcut]
  exact hx hzero

private def tailTestCc (R n : ℕ) : C_c(ℂ, ℝ) := by
  let f : C(ℂ, ℝ) := ⟨tailTestFun R n, tailTestFun_continuous R n⟩
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) (tailTestFun_support R n)
  exact ⟨f, hcompact⟩

private def tailTest (R n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (tailTestCc R n).toBoundedContinuousFunction

private theorem tailTest_hasCompactSupport (R n : ℕ) :
    HasCompactSupport (tailTest R n : ℂ → ℝ) := (tailTestCc R n).hasCompactSupport

private theorem tailTest_nonneg (R n : ℕ) (x : ℂ) : 0 ≤ tailTest R n x := by
  change 0 ≤ tailInnerFun R x * massCutoffFun n x
  exact mul_nonneg (tailInnerFun_nonneg R x) (massCutoff_nonneg n x)

private theorem tailTest_le_inner (R n : ℕ) (x : ℂ) :
    tailTest R n x ≤ tailInnerFun R x := by
  simp only [tailTest, tailTestCc, CompactlySupportedContinuousMap.toBoundedContinuousFunction]
  change tailInnerFun R x * massCutoffFun n x ≤ tailInnerFun R x
  have hleft := tailInnerFun_nonneg R x
  have hcut := massCutoff_le_one n x
  have hnonneg := massCutoff_nonneg n x
  have hcut' : massCutoffFun n x ≤ 1 := by
    simpa [massCutoff, massCutoffCc,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction] using hcut
  have hnonneg' : 0 ≤ massCutoffFun n x := by
    simpa [massCutoff, massCutoffCc,
      CompactlySupportedContinuousMap.toBoundedContinuousFunction] using hnonneg
  linarith only [mul_nonneg hleft (sub_nonneg.mpr hcut')]

private theorem tailTest_mono (R : ℕ) (x : ℂ) :
    Monotone fun n => tailTest R n x := by
  intro n m hnm
  simp only [tailTest, tailTestCc,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction]
  change tailInnerFun R x * massCutoffFun n x ≤
    tailInnerFun R x * massCutoffFun m x
  exact mul_le_mul_of_nonneg_left (massCutoff_mono x hnm) (tailInnerFun_nonneg R x)

private theorem tailTest_tendsto_inner (R : ℕ) (x : ℂ) :
    Tendsto (fun n : ℕ => tailTest R n x) atTop (𝓝 (tailInnerFun R x)) := by
  have hconst : Tendsto (fun _ : ℕ => tailInnerFun R x) atTop (𝓝 (tailInnerFun R x)) :=
    tendsto_const_nhds
  have h := hconst.mul (massCutoff_tendsto_one x)
  simpa [tailTest, tailTestCc, tailTestFun,
    massCutoff, massCutoffCc, massCutoffFun,
    CompactlySupportedContinuousMap.toBoundedContinuousFunction] using h

private theorem tailTest_lintegral_tendsto (R : ℕ) (μ : Measure ℂ) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (tailTest R n x) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (tailInnerFun R x) ∂μ)) := by
  have hmeas (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal (tailTest R n x)) μ :=
    (ENNReal.measurable_ofReal.comp (tailTest R n).continuous.measurable).aemeasurable
  have hmono : ∀ᵐ x ∂μ, Monotone fun n => ENNReal.ofReal (tailTest R n x) :=
    ae_of_all _ fun x n m hnm => ENNReal.ofReal_le_ofReal (tailTest_mono R x hnm)
  have hlim : ∀ᵐ x ∂μ,
      Tendsto (fun n => ENNReal.ofReal (tailTest R n x)) atTop
        (𝓝 (ENNReal.ofReal (tailInnerFun R x))) := by
    filter_upwards [] with x
    exact ENNReal.tendsto_ofReal (tailTest_tendsto_inner R x)
  exact lintegral_tendsto_of_tendsto_of_monotone hmeas hmono hlim

private theorem tailInner_zero_of_mem_closedBall (R : ℕ) (x : ℂ)
    (hx : x ∈ Metric.closedBall (0 : ℂ) (R : ℝ)) : tailInnerFun R x = 0 := by
  have hnorm : ‖x‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hsub : ‖x‖ - (R : ℝ) ≤ 0 := sub_nonpos.mpr hnorm
  dsimp [tailInnerFun]
  rw [max_eq_left (le_trans (min_le_right _ _) hsub)]

private theorem tailInner_one_of_mem_compl_closedBall (R : ℕ) (x : ℂ)
    (hx : x ∈ (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ) : tailInnerFun R x = 1 := by
  have hnorm : (R : ℝ) + 1 < ‖x‖ := by
    have hnot : ¬ ‖x‖ ≤ (R : ℝ) + 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    exact lt_of_not_ge hnot
  have hsub : 1 ≤ ‖x‖ - (R : ℝ) := by linarith
  dsimp [tailInnerFun]
  rw [min_eq_left hsub]
  simp

/-- Fatou's compact-test bound controls total expected mass for an admissible whole-plane
circle-chaos version. -/
theorem admissibleCircleVersion_expected_total_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) :
    ∫⁻ ω, M ω Set.univ ∂P ≤ gmcReferenceMeasure Set.univ := by
  classical
  let A : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂M ω
  have hAmeas (n : ℕ) : Measurable (A n) := by
    exact (Measure.measurable_lintegral
      ((ENNReal.measurable_ofReal.comp (massCutoff n).continuous.measurable)))
      |>.comp hM.1
  have hABound (n : ℕ) : ∫⁻ ω, A n ω ∂P ≤ gmcReferenceMeasure Set.univ := by
    have htest := admissibleCircleVersion_expected_test_le P X hX Xc hXc γ M hM
      (massCutoff n) (massCutoff_nonneg n) (massCutoff_hasCompactSupport n)
    have hconv : ∀ ω,
        ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂M ω =
          ENNReal.ofReal (∫ x, massCutoff n x ∂M ω) := by
      intro ω
      have hlocal : IsFiniteMeasureOnCompacts (M ω) := ⟨fun K hK =>
        hM.2.2.1 ω K hK (Set.subset_univ K)⟩
      have hi : Integrable (fun x => massCutoff n x) (M ω) :=
        @Continuous.integrable_of_hasCompactSupport ℂ ℝ _ _ _ (M ω) inferInstance
          (massCutoff n) hlocal (massCutoff n).continuous (massCutoff_hasCompactSupport n)
      have hnonneg : 0 ≤ᵐ[M ω] fun x => massCutoff n x :=
        ae_of_all _ (massCutoff_nonneg n)
      have hlin := ofReal_integral_eq_lintegral_ofReal hi hnonneg
      exact hlin.symm
    calc
      ∫⁻ ω, A n ω ∂P =
          ∫⁻ ω, ENNReal.ofReal (∫ x, massCutoff n x ∂M ω) ∂P := by
            apply lintegral_congr_ae
            exact ae_of_all _ hconv
      _ ≤ ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂gmcReferenceMeasure := htest
      _ ≤ gmcReferenceMeasure Set.univ := by
            calc
              ∫⁻ x, ENNReal.ofReal (massCutoff n x) ∂gmcReferenceMeasure ≤
                  ∫⁻ x, (1 : ℝ≥0∞) ∂gmcReferenceMeasure := by
                    apply lintegral_mono
                    intro x
                    simpa using ENNReal.ofReal_le_ofReal (massCutoff_le_one n x)
              _ = gmcReferenceMeasure Set.univ := by simp
  have hAmono : ∀ᵐ ω ∂P, Monotone fun n => A n ω := by
    apply ae_of_all
    intro ω n m hnm
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (massCutoff_mono x hnm)
  have hAlim : ∀ᵐ ω ∂P,
      Tendsto (fun n => A n ω) atTop (𝓝 (M ω Set.univ)) := by
    apply ae_of_all
    intro ω
    exact massCutoff_lintegral_tendsto (M ω)
  have hlim := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hAmeas n).aemeasurable) hAmono hAlim
  have hbound : ∀ n, ∫⁻ ω, A n ω ∂P ≤ gmcReferenceMeasure Set.univ := hABound
  exact le_of_tendsto' hlim hbound

/-- An admissible whole-plane circle-chaos version is finite almost surely. -/
theorem admissibleCircleVersion_finite_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) :
    ∀ᵐ ω ∂P, IsFiniteMeasure (M ω) := by
  have htotal := admissibleCircleVersion_expected_total_le P X hX Xc hXc γ M hM
  have hEfin : (∫⁻ ω, M ω Set.univ ∂P) < ∞ := by
    exact lt_of_le_of_lt htotal (lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top)
  have hmassMeas : Measurable (fun ω => M ω Set.univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp hM.1
  filter_upwards [ae_lt_top hmassMeas (ne_of_lt hEfin)] with ω hω
  exact ⟨hω⟩

/-- Expected mass outside a growing disk for an admissible whole-plane version is bounded by the
reference tail, uniformly with a one-unit exhaustion offset. -/
theorem admissibleCircleVersion_expected_tail_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) (R : ℕ) :
    ∫⁻ ω, M ω (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ ∂P ≤
      gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ := by
  classical
  let tail : Set ℂ := (Metric.closedBall (0 : ℂ) (R : ℝ))ᶜ
  let tailLarge : Set ℂ := (Metric.closedBall (0 : ℂ) ((R : ℝ) + 1))ᶜ
  have htail : MeasurableSet tail := by
    exact (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (R : ℝ))).measurableSet.compl
  have htailLarge : MeasurableSet tailLarge := by
    exact (Metric.isClosed_closedBall (x := (0 : ℂ)) (ε := (R : ℝ) + 1)).measurableSet.compl
  let A : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ x, ENNReal.ofReal (tailTest R n x) ∂M ω
  let B : Ω → ℝ≥0∞ := fun ω => ∫⁻ x, ENNReal.ofReal (tailInnerFun R x) ∂M ω
  have hAmeas (n : ℕ) : Measurable (A n) := by
    exact (Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp (tailTest R n).continuous.measurable)).comp hM.1
  have hABound (n : ℕ) : ∫⁻ ω, A n ω ∂P ≤ gmcReferenceMeasure tail := by
    have htest := admissibleCircleVersion_expected_test_le P X hX Xc hXc γ M hM
      (tailTest R n) (tailTest_nonneg R n) (tailTest_hasCompactSupport R n)
    have hconv : ∀ ω, A n ω =
        ENNReal.ofReal (∫ x, tailTest R n x ∂M ω) := by
      intro ω
      have hlocal : IsFiniteMeasureOnCompacts (M ω) := ⟨fun K hK =>
        hM.2.2.1 ω K hK (Set.subset_univ K)⟩
      have hi : Integrable (fun x => tailTest R n x) (M ω) :=
        @Continuous.integrable_of_hasCompactSupport ℂ ℝ _ _ _ (M ω) inferInstance
          (tailTest R n) hlocal (tailTest R n).continuous (tailTest_hasCompactSupport R n)
      have hnonneg : 0 ≤ᵐ[M ω] fun x => tailTest R n x :=
        ae_of_all _ (tailTest_nonneg R n)
      exact (ofReal_integral_eq_lintegral_ofReal hi hnonneg).symm
    have hcompare (x : ℂ) :
        ENNReal.ofReal (tailTest R n x) ≤ tail.indicator (fun _ => (1 : ℝ≥0∞)) x := by
      by_cases hx : x ∈ tail
      · simpa [Set.indicator, hx] using ENNReal.ofReal_le_ofReal
          (tailTest_le_inner R n x |>.trans (tailInnerFun_le_one R x))
      · have hball : x ∈ Metric.closedBall (0 : ℂ) (R : ℝ) := by
          simpa [tail, Set.mem_compl_iff] using hx
        have hinner := tailInner_zero_of_mem_closedBall R x hball
        have hzero : tailTest R n x = 0 := by
          have hle := tailTest_le_inner R n x
          rw [hinner] at hle
          exact le_antisymm hle (tailTest_nonneg R n x)
        simp [Set.indicator, hx, hzero]
    calc
      ∫⁻ ω, A n ω ∂P =
          ∫⁻ ω, ENNReal.ofReal (∫ x, tailTest R n x ∂M ω) ∂P := by
            apply lintegral_congr_ae
            exact ae_of_all _ hconv
      _ ≤ ∫⁻ x, ENNReal.ofReal (tailTest R n x) ∂gmcReferenceMeasure := htest
      _ ≤ ∫⁻ x, tail.indicator (fun _ => (1 : ℝ≥0∞)) x ∂gmcReferenceMeasure :=
          lintegral_mono hcompare
      _ = gmcReferenceMeasure tail := by
          rw [lintegral_indicator_const htail]
          simp [tail]
  have hAmono : ∀ᵐ ω ∂P, Monotone fun n => A n ω := by
    apply ae_of_all
    intro ω n m hnm
    exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (tailTest_mono R x hnm)
  have hAlim : ∀ᵐ ω ∂P, Tendsto (fun n => A n ω) atTop (𝓝 (B ω)) := by
    apply ae_of_all
    intro ω
    exact tailTest_lintegral_tendsto R (M ω)
  have houter := lintegral_tendsto_of_tendsto_of_monotone
    (fun n => (hAmeas n).aemeasurable) hAmono hAlim
  have hBbound : ∫⁻ ω, B ω ∂P ≤ gmcReferenceMeasure tail :=
    le_of_tendsto' houter hABound
  have hpoint (ω : Ω) : M ω tailLarge ≤ B ω := by
    have hcompare (x : ℂ) :
        tailLarge.indicator (fun _ => (1 : ℝ≥0∞)) x ≤
          ENNReal.ofReal (tailInnerFun R x) := by
      by_cases hx : x ∈ tailLarge
      · have hone := tailInner_one_of_mem_compl_closedBall R x (by simpa [tailLarge] using hx)
        simp [Set.indicator, hx, hone]
      · simp [Set.indicator, hx]
    calc
      M ω tailLarge = ∫⁻ x, tailLarge.indicator (fun _ => (1 : ℝ≥0∞)) x ∂M ω := by
        rw [lintegral_indicator_const htailLarge]
        simp [tailLarge]
      _ ≤ B ω := lintegral_mono hcompare
  calc
    ∫⁻ ω, M ω tailLarge ∂P ≤ ∫⁻ ω, B ω ∂P := lintegral_mono hpoint
    _ ≤ gmcReferenceMeasure tail := hBbound

/-- An admissible whole-plane circle version, after modification on one null set, satisfies the
global bounded-continuous-test convergence predicate `IsGMCOf`. -/
theorem admissibleCircleVersion_to_IsGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M) :
    ∃ N : Ω → Measure ℂ,
      (∀ ω, IsFiniteMeasure (N ω)) ∧ IsGMCOf P X γ N ∧ ∀ᵐ ω ∂P, N ω = M ω := by
  classical
  have hMfinite := admissibleCircleVersion_finite_ae P X hX Xc hXc γ M hM
  obtain ⟨N, hNmeas, hNfinite, hNM⟩ :=
    exists_everywhere_finite_measure_version P M hM.1 hMfinite
  have hNtail (n : ℕ) :
      ∫⁻ ω, N ω (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1))ᶜ ∂P ≤
        gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ := by
    calc
      ∫⁻ ω, N ω (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1))ᶜ ∂P =
          ∫⁻ ω, M ω (Metric.closedBall (0 : ℂ) ((n : ℝ) + 1))ᶜ ∂P := by
            apply lintegral_congr_ae
            filter_upwards [hNM] with ω hω
            rw [hω]
      _ ≤ gmcReferenceMeasure (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ :=
        admissibleCircleVersion_expected_tail_le P X hX Xc hXc γ M hM n
  have hGlobal : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂N ω) := by
    intro f
    apply (tendstoInMeasure_iff_norm).2
    intro ε hε
    let B : ℝ := ‖f‖ + 1
    let q : ℝ≥0∞ := ENNReal.ofReal (ε / (3 * B))
    have hB : 0 < B := by dsimp [B]; linarith [norm_nonneg f]
    have hqpos : 0 < q := ENNReal.ofReal_pos.mpr (div_pos hε (by positivity))
    have hq0 : q ≠ 0 := ne_of_gt hqpos
    have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
    let tail : ℕ → Set ℂ := fun n =>
      (Metric.closedBall (0 : ℂ) ((n + 1 : ℕ) : ℝ))ᶜ
    let referenceTail : ℕ → Set ℂ := fun n => (Metric.closedBall (0 : ℂ) (n : ℝ))ᶜ
    let cutoffTail : ℕ → ℝ → Ω → ℝ≥0∞ := fun n r ω =>
      regularizedGMC P Xc γ r ω (tail n)
    have htailSubset (n : ℕ) : tail n ⊆ referenceTail n := by
      intro x hx
      have hlarge : (n : ℝ) + 1 < ‖x‖ := by
        have hnot : ¬ ‖x‖ ≤ ((n + 1 : ℕ) : ℝ) := by
          simpa [tail, Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff] using hx
        have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
          norm_num [Nat.cast_add]
        have hnot' : ¬ ‖x‖ ≤ (n : ℝ) + 1 := by simpa [hcast] using hnot
        exact lt_of_not_ge hnot'
      have hlarge' : (n : ℝ) < ‖x‖ := by linarith
      simpa [referenceTail, Metric.mem_closedBall, dist_zero_right, Set.mem_compl_iff] using
        (not_le_of_gt hlarge')
    have hcutMeas (n : ℕ) (r : ℝ) : Measurable (cutoffTail n r) := by
      exact (Measure.measurable_coe
        ((Metric.isClosed_closedBall (x := (0 : ℂ))
          (ε := ((n + 1 : ℕ) : ℝ))).measurableSet.compl)).comp
          (regularizedGMC_measurable P X hX Xc hXc γ r)
    have hcutExp (n : ℕ) (r : ℝ) :
        ∫⁻ ω, cutoffTail n r ω ∂P = gmcReferenceMeasure (tail n) := by
      exact regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r (tail n)
        ((Metric.isClosed_closedBall (x := (0 : ℂ))
          (ε := ((n + 1 : ℕ) : ℝ))).measurableSet.compl)
    have hrefReference : Tendsto (fun n : ℕ => gmcReferenceMeasure (referenceTail n))
        atTop (𝓝 0) := by
      simpa [referenceTail] using gmcReferenceMeasure_compl_closedBall_tendsto_zero
    have hprobCore (n : ℕ) : Tendsto
        (fun r : ℝ => P {ω | ε / 3 ≤ ‖
          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
          (∫ x, cutoffTest f (n + 1) x ∂N ω)‖}) atTop (𝓝 0) := by
      let fc := cutoffTest f (n + 1)
      have hfc : HasCompactSupport (fc : ℂ → ℝ) := cutoffTest_hasCompactSupport f (n + 1)
      have hMlim := hM.2.2.2 fc hfc (Set.subset_univ _)
      have hcut : ∀ r : ℝ,
          (fun ω => regularizedLogChaosTestMass P Set.univ
            (fun x => normPlus x ^ (-4 : ℝ))
            (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω fc) =ᵐ[P]
            fun ω => ∫ x, fc x ∂regularizedGMC P Xc γ r ω := by
        intro r
        exact Filter.Eventually.of_forall fun ω =>
          (circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r ω fc)
      have hcoreM : TendstoInMeasure P
          (fun r ω => ∫ x, fc x ∂regularizedGMC P Xc γ r ω) atTop
          (fun ω => ∫ x, fc x ∂M ω) := by
        exact TendstoInMeasure.congr hcut
          (Filter.Eventually.of_forall fun _ => rfl) hMlim
      have hcoreN : TendstoInMeasure P
          (fun r ω => ∫ x, fc x ∂regularizedGMC P Xc γ r ω) atTop
          (fun ω => ∫ x, fc x ∂N ω) :=
        tendstoInMeasure_integral_after_ae_measure_change
          (fun r ω => ∫ x, fc x ∂regularizedGMC P Xc γ r ω) M N fc hNM hcoreM
      simpa [fc, norm_sub_rev] using (tendstoInMeasure_iff_norm.mp hcoreN (ε / 3) (by positivity))
    have hboundError (n : ℕ) (r : ℝ) :
        P {ω | ε / 3 ≤ ‖
          (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖} ≤
          gmcReferenceMeasure (referenceTail n) / q := by
      have hIncl : ∀ᵐ ω ∂P,
          ω ∈ {ω | ε / 3 ≤ ‖
              (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
              (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖} →
          ω ∈ {ω | q ≤ cutoffTail n r ω} := by
        filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hfinite hω
        have herr := @circleIntegral_cutoff_error_le
          (regularizedGMC P Xc γ r ω) hfinite f (n + 1)
        have hreal : ε / (3 * B) ≤ (cutoffTail n r ω).toReal := by
          have hlarge : ε / 3 ≤ ‖f‖ * (cutoffTail n r ω).toReal := by
            exact hω.trans (by simpa [cutoffTail, tail] using herr)
          apply (div_le_iff₀ (by positivity)).2
          dsimp [B]
          have ht : 0 ≤ (cutoffTail n r ω).toReal := ENNReal.toReal_nonneg
          linarith only [hlarge, ht]
        have htailtop : cutoffTail n r ω ≠ ∞ := by
          exact measure_ne_top _ _
        exact (ENNReal.ofReal_le_iff_le_toReal htailtop).2 hreal
      calc
        P {ω | ε / 3 ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
            (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖} ≤
            P {ω | q ≤ cutoffTail n r ω} := measure_mono_ae hIncl
        _ ≤ (∫⁻ ω, cutoffTail n r ω ∂P) / q :=
            meas_ge_le_lintegral_div (hcutMeas n r).aemeasurable hq0 hqtop
        _ = gmcReferenceMeasure (tail n) / q := by rw [hcutExp]
        _ ≤ gmcReferenceMeasure (referenceTail n) / q := by
          apply ENNReal.div_le_div_right
          exact measure_mono (htailSubset n)
    have hboundLimitError (n : ℕ) :
        P {ω | ε / 3 ≤ ‖
          (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖} ≤
          gmcReferenceMeasure (referenceTail n) / q := by
      have hNtail' : ∫⁻ ω, N ω (tail n) ∂P ≤
          gmcReferenceMeasure (referenceTail n) := by
        simpa [tail, referenceTail, Nat.cast_add, Nat.cast_one] using hNtail n
      have hIncl : ∀ᵐ ω ∂P,
          ω ∈ {ω | ε / 3 ≤ ‖
              (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖} →
          ω ∈ {ω | q ≤ N ω (tail n)} := by
        filter_upwards [] with ω
        intro hω
        have herr := @circleIntegral_cutoff_error_le (N ω) (hNfinite ω) f (n + 1)
        have herr' : ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) -
            (∫ x, f x ∂N ω)‖ ≤ ‖f‖ * (N ω (tail n)).toReal := by
          simpa only [norm_sub_rev, tail, Nat.cast_add, Nat.cast_one] using herr
        have hreal : ε / (3 * B) ≤ (N ω (tail n)).toReal := by
          have hlarge : ε / 3 ≤ ‖f‖ * (N ω (tail n)).toReal := by
            exact hω.trans (by simpa [tail] using herr')
          apply (div_le_iff₀ (by positivity)).2
          dsimp [B]
          have ht : 0 ≤ (N ω (tail n)).toReal := ENNReal.toReal_nonneg
          linarith only [hlarge, ht]
        exact (ENNReal.ofReal_le_iff_le_toReal
          (measure_ne_top (N ω) (tail n))).2 hreal
      calc
            P {ω | ε / 3 ≤ ‖
              (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖} ≤
            P {ω | q ≤ N ω (tail n)} := measure_mono_ae hIncl
        _ ≤ (∫⁻ ω, N ω (tail n) ∂P) / q :=
            meas_ge_le_lintegral_div
              ((Measure.measurable_coe
                ((Metric.isClosed_closedBall (x := (0 : ℂ))
                  (ε := ((n + 1 : ℕ) : ℝ))).measurableSet.compl)).comp
                hNmeas).aemeasurable hq0 hqtop
        _ ≤ gmcReferenceMeasure (referenceTail n) / q := by
          simpa [referenceTail] using (ENNReal.div_le_div_right hNtail' q)
    have hEventBound (n : ℕ) (r : ℝ) :
        P {ω | ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖} ≤
          gmcReferenceMeasure (referenceTail n) / q +
            P {ω | ε / 3 ≤ ‖
              (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
              (∫ x, cutoffTest f (n + 1) x ∂N ω)‖} +
            gmcReferenceMeasure (referenceTail n) / q := by
      let E₁ : Set Ω := {ω | ε / 3 ≤ ‖
        (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
        (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖}
      let E₂ : Set Ω := {ω | ε / 3 ≤ ‖
        (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
        (∫ x, cutoffTest f (n + 1) x ∂N ω)‖}
      let E₃ : Set Ω := {ω | ε / 3 ≤ ‖
        (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖}
      have hsubset :
          {ω | ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖} ⊆
            E₁ ∪ (E₂ ∪ E₃) := by
        intro ω hω
        by_contra hnot
        have hnot₁ : ω ∉ E₁ := fun h => hnot (Or.inl h)
        have hnot₂ : ω ∉ E₂ := fun h => hnot (Or.inr (Or.inl h))
        have hnot₃ : ω ∉ E₃ := fun h => hnot (Or.inr (Or.inr h))
        have h₁ : ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) -
            (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖ < ε / 3 :=
          lt_of_not_ge (by simpa [E₁] using hnot₁)
        have h₂ : ‖
            (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
            (∫ x, cutoffTest f (n + 1) x ∂N ω)‖ < ε / 3 := by
          exact lt_of_not_ge (by simpa [E₂] using hnot₂)
        have h₃ : ‖
            (∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ < ε / 3 :=
          lt_of_not_ge (by simpa [E₃] using hnot₃)
        have hsum :
            ‖(∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖ +
              ‖(∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                (∫ x, cutoffTest f (n + 1) x ∂N ω)‖ +
              ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ < ε := by
          linarith only [h₁, h₂, h₃]
        have htriangle :
            ‖(∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖ ≤
              ‖(∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                  (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)‖ +
              ‖(∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                  (∫ x, cutoffTest f (n + 1) x ∂N ω)‖ +
              ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ := by
          calc
            _ = ‖((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                  (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)) +
                  ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                    (∫ x, cutoffTest f (n + 1) x ∂N ω)) +
                  ((∫ x, cutoffTest f (n + 1) x ∂N ω) -
                    (∫ x, f x ∂N ω))‖ := by congr 1; ring
            _ ≤ _ := by
              calc
                _ ≤ ‖((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                    (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)) +
                    ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                      (∫ x, cutoffTest f (n + 1) x ∂N ω))‖ +
                    ‖(∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω)‖ :=
                      norm_add_le
                        (((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω)) +
                          ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                            (∫ x, cutoffTest f (n + 1) x ∂N ω)))
                        ((∫ x, cutoffTest f (n + 1) x ∂N ω) - (∫ x, f x ∂N ω))
                _ ≤ _ := by
                  exact add_le_add
                    (norm_add_le
                      ((∫ x, f x ∂regularizedGMC P Xc γ r ω) -
                        (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω))
                      ((∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
                        (∫ x, cutoffTest f (n + 1) x ∂N ω)))
                    (le_refl _)
        have hmain : ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖ := by
          simpa only [Set.mem_ofPred_eq] using hω
        exact (not_lt_of_ge hmain) (lt_of_le_of_lt htriangle hsum)
      have hmeasE (s t : Set Ω) : P (s ∪ t) ≤ P s + P t := measure_union_le _ _
      calc
        P {ω | ε ≤ ‖
            (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖} ≤
            P (E₁ ∪ (E₂ ∪ E₃)) := measure_mono hsubset
        _ ≤ P E₁ + P (E₂ ∪ E₃) := hmeasE _ _
        _ ≤ P E₁ + P E₂ + P E₃ := by
          calc
            _ ≤ P E₁ + (P E₂ + P E₃) :=
              add_le_add (le_refl _) (hmeasE E₂ E₃)
            _ = P E₁ + P E₂ + P E₃ := by rw [add_assoc]
        _ ≤ gmcReferenceMeasure (referenceTail n) / q + P E₂ +
            gmcReferenceMeasure (referenceTail n) / q := by
          grw [hboundError n r, hboundLimitError n]
    have hCoreTend (n : ℕ) : Tendsto (fun r : ℝ => P {ω | ε / 3 ≤ ‖
          (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
          (∫ x, cutoffTest f (n + 1) x ∂N ω)‖}) atTop (𝓝 0) :=
      hprobCore n
    have hTailDiv : Tendsto (fun n : ℕ => gmcReferenceMeasure (referenceTail n) / q)
        atTop (𝓝 0) := by
      have ht := ENNReal.Tendsto.div_const (b := q) hrefReference (Or.inr hq0)
      simpa using ht
    have hSum (n : ℕ) :
        Tendsto (fun r : ℝ => gmcReferenceMeasure (referenceTail n) / q +
          P {ω | ε / 3 ≤ ‖
            (∫ x, cutoffTest f (n + 1) x ∂regularizedGMC P Xc γ r ω) -
            (∫ x, cutoffTest f (n + 1) x ∂N ω)‖} +
          gmcReferenceMeasure (referenceTail n) / q) atTop
          (𝓝 (gmcReferenceMeasure (referenceTail n) / q + 0 +
            gmcReferenceMeasure (referenceTail n) / q)) := by
      exact (tendsto_const_nhds.add (hCoreTend n)).add tendsto_const_nhds
    have hSumZero : Tendsto
        (fun n : ℕ => gmcReferenceMeasure (referenceTail n) / q + 0 +
          gmcReferenceMeasure (referenceTail n) / q)
        atTop (𝓝 0) := by
      have hzero : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0) := tendsto_const_nhds
      have h := (hTailDiv.add hzero).add hTailDiv
      simpa using h
    have hFinal : Tendsto (fun r : ℝ => P {ω | ε ≤ ‖
          (∫ x, f x ∂regularizedGMC P Xc γ r ω) - (∫ x, f x ∂N ω)‖}) atTop (𝓝 0) := by
      refine ENNReal.tendsto_nhds_zero.2 fun δ hδ => ?_
      have hδnhds : Set.Iio δ ∈ 𝓝 (0 : ℝ≥0∞) :=
        ENNReal.nhds_zero_basis.mem_iff.mpr ⟨δ, hδ, Set.Subset.rfl⟩
      have hsmallEvent := hSumZero.eventually hδnhds
      obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hsmallEvent
      have hn' : gmcReferenceMeasure (referenceTail n) / q + 0 +
          gmcReferenceMeasure (referenceTail n) / q < δ := hn n (Nat.le_refl n)
      have hcoreEvent := hSum n
      have heventually := hcoreEvent.eventually (Iio_mem_nhds hn')
      filter_upwards [heventually] with r hr
      exact le_of_lt (lt_of_le_of_lt (hEventBound n r) hr)
    exact hFinal
  refine ⟨N, hNfinite, ⟨hNfinite, ⟨Xc, hXc, hGlobal⟩⟩, hNM⟩

end DOZZ.Proofs
