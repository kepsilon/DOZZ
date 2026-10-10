/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.RealizationMeasure
public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion
public import DOZZ.GMC.Construction.AdmissibleCircleFiniteMass
public import DOZZ.GMC.Construction.CircleAverageJointVersion
public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import DOZZ.GMC.Assembly.CircleUniformL1
public import DOZZ.GMC.AdmissibleGMCDetermines
public import DOZZ.GMC.Construction.L1CauchyMeasureLimit

/-! Existence of admissible GMC versions (proof of `DOZZ.admissibleLogRegularization_GMC_exists`),
existence of the circle GMC (proof of `DOZZ.equatorGFF_circle_average_GMC_exists`), and uniqueness
for compatible regularizations (proof of `DOZZ.admissibleLogRegularization_GMC_unique_ae`). -/

@[expose] public section

/-! ### Admissible GMC existence

Existence of an admissible GMC version for every admissible logarithmic regularization.

The realized random measure is measurable, carried by the chart and finite on its compact
subsets. For a continuous test with compact support in the chart, the cutoff integrals are `L¹`
Cauchy and converge almost surely along the fast cutoff sequence to its integral against the
realized measure; Fatou upgrades this to `L¹` convergence along every cutoff, hence convergence
in measure. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Convergence in expected absolute value implies convergence in measure. -/
theorem tendstoInMeasure_of_tendsto_lintegral_ofReal_abs {Ω ι : Type*} [MeasurableSpace Ω]
    {l : Filter ι} (P : Measure Ω) (F : ι → Ω → ℝ) (G : Ω → ℝ)
    (hF : ∀ i, AEStronglyMeasurable (F i) P) (hG : AEStronglyMeasurable G P)
    (h : Tendsto (fun i => ∫⁻ ω, ENNReal.ofReal |F i ω - G ω| ∂P) l (𝓝 0)) :
    TendstoInMeasure P F l G := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
  have heq : (fun i => eLpNorm (F i - G) 1 P) =
      fun i => ∫⁻ ω, ENNReal.ofReal |F i ω - G ω| ∂P := by
    funext i
    rw [eLpNorm_one_eq_lintegral_enorm ((hF i).sub hG)]
    simp only [Pi.sub_apply, Real.enorm_eq_ofReal_abs]
  rw [heq]
  exact h

section Exists

variable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (T : ChartTestSystem U) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (R : ChartTestSystem.Index → ℕ → ℝ)
    (hR : ∀ i k r s, R i k ≤ r → R i k ≤ s →
      ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r (T.allTest i) ω -
        admissibleCutoffIntegral P U dens Y γ s (T.allTest i) ω| ∂P <
          ENNReal.ofReal ((1 / 2 : ℝ) ^ k))
    (e : ℕ → ChartTestSystem.Index) (he : Function.Surjective e) (c : ℝ) (hc : 0 ≤ c)
    (hcut : Real.exp (-c) ≤ ε₀)

include hγ hγ2 hR hc hcut in
/-- Cutoff integrals of a continuous test with compact support in the chart converge in `L¹(P)`
to its integral against the realized measure. -/
theorem tendsto_lintegral_abs_sub_realizationMeasure (f : ℂ → ℝ) (hf : Continuous f)
    (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
      ∫ x, f x ∂realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω| ∂P) atTop (𝓝 0) := by
  obtain ⟨Lf, hLf⟩ := hf.bounded_above_of_compact_support hfc
  have hfL : ∀ x, |f x| ≤ Lf := fun x => by rw [← Real.norm_eq_abs]; exact hLf x
  have hfK : ∀ x ∉ tsupport f, f x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hgood := ae_mem_realizationGoodSet P U dens ε₀ Y hY T γ R hR e c hc hcut
  have hFm (r : ℝ) : Measurable (admissibleCutoffIntegral P U dens Y γ r f) :=
    admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r f hf.measurable
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun _ => hεtop ▸ le_top
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨R₀, hR₀⟩ := admissibleCutoffIntegral_L1_uniform_cauchy P U dens ε₀ Y hY (tsupport f) hfc
    hfU {γ} isCompact_singleton (Set.singleton_subset_iff.mpr ⟨hγ, hγ2⟩) Lf ε.toReal hεr
  filter_upwards [eventually_ge_atTop R₀] with r hr
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
      admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f ω|) atTop
      (𝓝 (ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
        ∫ x, f x ∂realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω|)) := by
    filter_upwards [hgood] with ω hω
    rw [integral_realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω hω f hf hfc hfU]
    have h := tendsto_realizationLimit P U dens ε₀ Y hY T γ R e he c ω hω f hf hfc hfU
    exact ENNReal.continuous_ofReal.tendsto _ |>.comp
      ((continuous_abs.tendsto _).comp (tendsto_const_nhds.sub h))
  calc ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
        ∫ x, f x ∂realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω| ∂P
      = ∫⁻ ω, liminf (fun j => ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
          admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f ω|) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hlim] with ω hω
        exact hω.liminf_eq.symm
    _ ≤ liminf (fun j => ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
          admissibleCutoffIntegral P U dens Y γ (fastCutoff R e c j) f ω| ∂P) atTop :=
        lintegral_liminf_le fun j => ENNReal.measurable_ofReal.comp
          (continuous_abs.measurable.comp ((hFm r).sub (hFm _)))
    _ ≤ ε := by
        apply liminf_le_of_frequently_le'
        apply Eventually.frequently
        filter_upwards [(tendsto_fastCutoff R e c hc).eventually (eventually_ge_atTop R₀)]
          with j hj
        have h := hR₀ r (fastCutoff R e c j) hr hj γ rfl f hf.measurable hfL hfK
        rw [ENNReal.ofReal_toReal hεtop] at h
        exact h.le

include hγ hγ2 hR hc hcut in
/-- The realized random measure is an admissible GMC version. -/
theorem realizationMeasure_isAdmissibleGMCVersion :
    IsAdmissibleGMCVersion P U dens Y γ
      (fun ω => realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω) := by
  refine ⟨measurable_realizationMeasure P U hU dens ε₀ Y hY T γ R e he c,
    realizationMeasure_compl P U hU dens ε₀ Y hY T γ R e he c,
    fun ω K hK hKU => realizationMeasure_lt_top_of_isCompact P U hU dens ε₀ Y hY T γ R e he c ω K
      hK hKU, ?_⟩
  intro f hfc hfU
  have hgood := ae_mem_realizationGoodSet P U dens ε₀ Y hY T γ R hR e c hc hcut
  have hG : AEStronglyMeasurable (fun ω => ∫ x, f x ∂realizationMeasure P U hU dens ε₀ Y hY T γ R
      e he c ω) P := by
    refine (measurable_indicator_realizationLimit P U dens ε₀ Y hY T γ R e he c f f.continuous
      hfc hfU).aestronglyMeasurable.congr ?_
    filter_upwards [hgood] with ω hω
    rw [Set.indicator_of_mem hω, integral_realizationMeasure P U hU dens ε₀ Y hY T γ R e he c ω hω
      f f.continuous hfc hfU]
  apply tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P _ _ (fun r =>
    (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r f
      f.continuous.measurable).aestronglyMeasurable) hG
  exact tendsto_lintegral_abs_sub_realizationMeasure P U hU dens ε₀ Y hY T γ hγ hγ2 R hR e he c
    hc hcut f f.continuous hfc hfU

end Exists

end DOZZ.Assembly

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- The GMC construction from an admissible regularization gives a measurable admissible version
carried by the chart for every `0 < γ < 2`. -/
theorem admissibleLogRegularization_GMC_exists
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ M : Ω → Measure ℂ, IsAdmissibleGMCVersion P U dens Y γ M := by
  have : IsProbabilityMeasure P := admissibleLogRegularization_isProbabilityMeasure P U dens ε₀ Y hY
  have hU : IsOpen U := hY.openChart
  obtain ⟨T⟩ := exists_chartTestSystem U hU
  obtain ⟨R, hR⟩ := exists_test_cauchy_thresholds P U dens ε₀ Y hY T γ hγ hγ2
  obtain ⟨e, he⟩ := exists_surjective_nat ChartTestSystem.Index
  have hcut : Real.exp (-|Real.log ε₀|) ≤ ε₀ := by
    calc Real.exp (-|Real.log ε₀|) ≤ Real.exp (Real.log ε₀) :=
          Real.exp_le_exp.mpr (by linarith [neg_abs_le (Real.log ε₀)])
      _ = ε₀ := Real.exp_log hY.cutoffPositive
  exact ⟨_, realizationMeasure_isAdmissibleGMCVersion P U hU dens ε₀ Y hY T γ hγ hγ2 R hR e he
    |Real.log ε₀| (abs_nonneg _) hcut⟩

end DOZZ.Proofs

/-! ### Circle GMC existence

Existence of a circle-average process and a circle GMC for every equator GFF.

The supplied field has a jointly measurable circle-average witness. Its circle regularization is
admissible on the whole plane, so the admissible construction gives a measurable whole-plane
version; modified on one null set it satisfies the `IsGMCOf` predicate. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- For every equator GFF and every `0 < γ < 2`, there are a circle-average process and a finite
random measure satisfying the `IsGMCOf` predicate. See [KRV, (circleav), (Meps1) and (law)]. -/
theorem equatorGFF_circle_average_GMC_exists
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, ∃ M : Ω → Measure ℂ,
      IsCircleAverage P X Xc ∧ IsGMCOf P X γ M := by
  obtain ⟨Xc, hXc⟩ := exists_equatorGFF_circle_average_witness X hX
  obtain ⟨M, hM⟩ := admissibleLogRegularization_GMC_exists P Set.univ circleDensity 1
    (circleRegularization Xc) (circleRegularization_admissible P X hX Xc hXc) γ hγ hγ2
  obtain ⟨N, -, hN, -⟩ := admissibleCircleVersion_to_IsGMCOf P X hX γ Xc hXc M hM
  exact ⟨Xc, N, hXc, hN⟩

end DOZZ.Proofs

/-! ### Interleaved regularizations

Interleaving two compatible admissible regularizations.

At cutoffs whose logarithmic scale is a natural number or has even integer part the interleaved
family uses the first regularization; at the remaining cutoffs it uses the second. Coarse scales are
therefore always taken from the first family, and compatibility makes the interleaved family
admissible. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

/-- Cutoffs at which the interleaved regularization uses the second family. -/
def secondScale (ε : ℝ) : Prop :=
  Odd ⌊Real.log (1 / ε)⌋ ∧ ∀ k : ℕ, Real.log (1 / ε) ≠ k

open Classical in
/-- The interleaved regularization. -/
noncomputable def interleavedRegularization {Ω : Type*} (Y Z : Ω → ℝ → ℂ → ℝ) :
    Ω → ℝ → ℂ → ℝ :=
  fun ω ε x => if secondScale ε then Z ω ε x else Y ω ε x

theorem log_one_div_exp_neg (r : ℝ) : Real.log (1 / Real.exp (-r)) = r := by
  rw [one_div, Real.log_inv, Real.log_exp, neg_neg]

theorem not_secondScale_exp_neg_nat (k : ℕ) : ¬ secondScale (Real.exp (-(k : ℝ))) := by
  rintro ⟨-, h⟩
  exact h k (log_one_div_exp_neg _)

theorem secondScale_exp_neg_odd_half (j : ℕ) :
    secondScale (Real.exp (-(2 * (j : ℝ) + 3 / 2))) := by
  rw [secondScale, log_one_div_exp_neg]
  constructor
  · have hfloor : ⌊2 * (j : ℝ) + 3 / 2⌋ = 2 * (j : ℤ) + 1 := by
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hfloor]
    exact ⟨j, by ring⟩
  · intro k hk
    have h2 : (2 : ℝ) * (k - 2 * j) = 3 := by linarith
    have h2' : (2 : ℤ) * ((k : ℤ) - 2 * j) = 3 := by exact_mod_cast h2
    omega

theorem interleaved_of_not_secondScale {Ω : Type*} (Y Z : Ω → ℝ → ℂ → ℝ) (ε : ℝ)
    (h : ¬ secondScale ε) (ω : Ω) (x : ℂ) :
    interleavedRegularization Y Z ω ε x = Y ω ε x := by
  simp [interleavedRegularization, h]

theorem interleaved_of_secondScale {Ω : Type*} (Y Z : Ω → ℝ → ℂ → ℝ) (ε : ℝ)
    (h : secondScale ε) (ω : Ω) (x : ℂ) :
    interleavedRegularization Y Z ω ε x = Z ω ε x := by
  simp [interleavedRegularization, h]

theorem interleaved_exp_neg_nat {Ω : Type*} (Y Z : Ω → ℝ → ℂ → ℝ) (k : ℕ) (ω : Ω) (x : ℂ) :
    interleavedRegularization Y Z ω (Real.exp (-(k : ℝ))) x = Y ω (Real.exp (-(k : ℝ))) x :=
  interleaved_of_not_secondScale Y Z _ (not_secondScale_exp_neg_nat k) ω x

theorem gaussianCovariance_comm {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A B : Ω → ℝ) : gaussianCovariance P A B = gaussianCovariance P B A := by
  unfold gaussianCovariance
  congr 1
  funext ω
  ring

/-- The interleaving of two compatible admissible regularizations is admissible. -/
theorem interleavedRegularization_admissible
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z) :
    IsAdmissibleLogRegularization P U dens (min ε₀ ε₁) (interleavedRegularization Y Z) := by
  classical
  obtain ⟨hjoint, hcovYZ, hcoarseYZ, hoffYZ, hfixYZ⟩ := hYZ
  set W := interleavedRegularization Y Z with hWdef
  have hnat (k : ℕ) (ω : Ω) (x : ℂ) : W ω (Real.exp (-(k : ℝ))) x = Y ω (Real.exp (-(k : ℝ))) x :=
    interleaved_of_not_secondScale Y Z _ (not_secondScale_exp_neg_nat k) ω x
  refine
    { measurableAtScale := ?_
      openChart := hY.openChart
      densityContinuous := hY.densityContinuous
      densityPositive := hY.densityPositive
      cutoffPositive := lt_min hY.cutoffPositive hZ.cutoffPositive
      gaussian := ?_
      covarianceBound := ?_
      coarseVarianceBound := ?_
      coarseMixedBound := ?_
      offDiagonalLimit := ?_
      fixedCoarseLimit := ?_ }
  · intro ε
    by_cases h : secondScale ε
    · simp only [W, interleavedRegularization, h, ite_true]
      exact hZ.measurableAtScale ε
    · simp only [W, interleavedRegularization, h, ite_false]
      exact hY.measurableAtScale ε
  · intro n q hq
    have h := hjoint n (fun i => (decide (¬ secondScale (q i).1), (q i).1, (q i).2)) hq
    convert h using 2 with ω
    funext i
    by_cases hs : secondScale (q i).1
    · simp [W, interleavedRegularization, hs]
    · simp [W, interleavedRegularization, hs]
  · intro K hK hKU
    obtain ⟨CY, hCY, hY'⟩ := hY.covarianceBound K hK hKU
    obtain ⟨CZ, hCZ, hZ'⟩ := hZ.covarianceBound K hK hKU
    obtain ⟨CX, hCX, hX'⟩ := hcovYZ K hK hKU
    refine ⟨max CY (max CZ CX), le_max_of_le_left hCY, ?_⟩
    intro ε δ hε hεc hδ hδc x hx y hy
    have hεY : ε ≤ ε₀ := hεc.trans (min_le_left _ _)
    have hεZ : ε ≤ ε₁ := hεc.trans (min_le_right _ _)
    have hδY : δ ≤ ε₀ := hδc.trans (min_le_left _ _)
    have hδZ : δ ≤ ε₁ := hδc.trans (min_le_right _ _)
    have hCY' : CY ≤ max CY (max CZ CX) := le_max_left _ _
    have hCZ' : CZ ≤ max CY (max CZ CX) := le_trans (le_max_left _ _) (le_max_right _ _)
    have hCX' : CX ≤ max CY (max CZ CX) := le_trans (le_max_right _ _) (le_max_right _ _)
    by_cases hsε : secondScale ε <;> by_cases hsδ : secondScale δ
    · simp only [W, interleavedRegularization, hsε, hsδ, ite_true]
      exact (hZ' ε δ hε hεZ hδ hδZ x hx y hy).trans hCZ'
    · simp only [W, interleavedRegularization, hsε, hsδ, ite_true, ite_false]
      rw [gaussianCovariance_comm, norm_sub_rev, max_comm ε δ]
      exact (hX' δ ε hδ hδY hε hεZ y hy x hx).trans hCX'
    · simp only [W, interleavedRegularization, hsε, hsδ, ite_true, ite_false]
      exact (hX' ε δ hε hεY hδ hδZ x hx y hy).trans hCX'
    · simp only [W, interleavedRegularization, hsε, hsδ, ite_false]
      exact (hY' ε δ hε hεY hδ hδY x hx y hy).trans hCY'
  · intro K hK hKU
    obtain ⟨C, hC, hvar⟩ := hY.coarseVarianceBound K hK hKU
    refine ⟨C, hC, fun k hk x hx => ?_⟩
    simp only [hnat]
    exact hvar k (hk.trans (min_le_left _ _)) x hx
  · intro K hK hKU
    obtain ⟨CY, hCY, hY'⟩ := hY.coarseMixedBound K hK hKU
    obtain ⟨CX, hCX, hX'⟩ := hcoarseYZ K hK hKU
    refine ⟨max CY CX, le_max_of_le_left hCY, fun k hk ε hε hεk x hx => ?_⟩
    simp only [hnat]
    by_cases hs : secondScale ε
    · simp only [W, interleavedRegularization, hs, ite_true]
      exact (hX' k (hk.trans (min_le_left _ _)) ε hε
        (le_min (hεk.trans (hk.trans (min_le_right _ _))) hεk) x hx).trans (le_max_right _ _)
    · simp only [W, interleavedRegularization, hs, ite_false]
      exact (hY' k (hk.trans (min_le_left _ _)) ε hε hεk x hx).trans (le_max_left _ _)
  · obtain ⟨H, hH, hlim⟩ := hY.offDiagonalLimit
    refine ⟨H, hH, fun K hK hKU s hs η hη => ?_⟩
    obtain ⟨δ₁, hδ₁, h₁⟩ := hlim K hK hKU s hs (η / 2) (half_pos hη)
    obtain ⟨δ₂, hδ₂, h₂⟩ := hoffYZ K hK hKU s hs (η / 2) (half_pos hη)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε ε' hε hεc hε' hε'c x hx y hy hxy => ?_⟩
    have hε1 : ε ≤ min δ₁ ε₀ := le_min ((hεc.trans (min_le_left _ _)).trans (min_le_left _ _))
      ((hεc.trans (min_le_right _ _)).trans (min_le_left _ _))
    have hε'1 : ε' ≤ min δ₁ ε₀ := le_min ((hε'c.trans (min_le_left _ _)).trans (min_le_left _ _))
      ((hε'c.trans (min_le_right _ _)).trans (min_le_left _ _))
    have hε2 : ε ≤ min δ₂ (min ε₀ ε₁) := le_min ((hεc.trans (min_le_left _ _)).trans
      (min_le_right _ _)) (hεc.trans (min_le_right _ _))
    have hε'2 : ε' ≤ min δ₂ (min ε₀ ε₁) := le_min ((hε'c.trans (min_le_left _ _)).trans
      (min_le_right _ _)) (hε'c.trans (min_le_right _ _))
    have hYY := h₁ ε ε' hε hε1 hε' hε'1 x hx y hy hxy
    have hyx : s ≤ ‖y - x‖ := by rwa [norm_sub_rev]
    by_cases hsε : secondScale ε <;> by_cases hsε' : secondScale ε'
    · simp only [W, interleavedRegularization, hsε, hsε', ite_true]
      have h := (h₂ ε ε' hε hε2 hε' hε'2 x hx y hy hxy).2
      calc _ ≤ |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Z ω ε' y) -
              gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| +
            |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y) -
              (Real.log (1 / ‖x - y‖) + H x y)| := abs_sub_le _ _ _
        _ < η / 2 + η / 2 := add_lt_add h hYY
        _ = η := by ring
    · simp only [W, interleavedRegularization, hsε, hsε', ite_true, ite_false]
      have h := (h₂ ε' ε hε' hε'2 hε hε2 y hy x hx hyx).1
      rw [gaussianCovariance_comm P (fun ω => Y ω ε' y)] at h
      rw [gaussianCovariance_comm P (fun ω => Y ω ε' y) (fun ω => Y ω ε x)] at h
      rw [gaussianCovariance_comm P (fun ω => Z ω ε x)]
      calc _ ≤ |gaussianCovariance P (fun ω => Y ω ε' y) (fun ω => Z ω ε x) -
              gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| +
            |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y) -
              (Real.log (1 / ‖x - y‖) + H x y)| := abs_sub_le _ _ _
        _ < η / 2 + η / 2 := by
            refine add_lt_add ?_ hYY
            rwa [gaussianCovariance_comm P (fun ω => Z ω ε x)] at h
        _ = η := by ring
    · simp only [W, interleavedRegularization, hsε, hsε', ite_true, ite_false]
      have h := (h₂ ε ε' hε hε2 hε' hε'2 x hx y hy hxy).1
      calc _ ≤ |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Z ω ε' y) -
              gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y)| +
            |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω ε' y) -
              (Real.log (1 / ‖x - y‖) + H x y)| := abs_sub_le _ _ _
        _ < η / 2 + η / 2 := add_lt_add h hYY
        _ = η := by ring
    · simp only [W, interleavedRegularization, hsε, hsε', ite_false]
      exact hYY.trans (by linarith)
  · obtain ⟨κ, hκ⟩ := hY.fixedCoarseLimit
    refine ⟨κ, fun K hK hKU k hk η hη => ?_⟩
    obtain ⟨δ₁, hδ₁, h₁⟩ := hκ K hK hKU k (hk.trans (min_le_left _ _)) (η / 2) (half_pos hη)
    obtain ⟨δ₂, hδ₂, h₂⟩ := hfixYZ K hK hKU k hk (η / 2) (half_pos hη)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ε hε hεc x hx y hy => ?_⟩
    have hε1 : ε ≤ min δ₁ ε₀ := le_min ((hεc.trans (min_le_left _ _)).trans (min_le_left _ _))
      ((hεc.trans (min_le_right _ _)).trans (min_le_left _ _))
    have hε2 : ε ≤ min δ₂ (min ε₀ ε₁) := le_min ((hεc.trans (min_le_left _ _)).trans
      (min_le_right _ _)) (hεc.trans (min_le_right _ _))
    have hYk := h₁ ε hε hε1 x hx y hy
    simp only [hnat]
    by_cases hs : secondScale ε
    · simp only [W, interleavedRegularization, hs, ite_true]
      have h := h₂ ε hε hε2 x hx y hy
      calc _ ≤ |gaussianCovariance P (fun ω => Z ω ε x) (fun ω => Y ω (Real.exp (-(k : ℝ))) y) -
              gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω (Real.exp (-(k : ℝ))) y)| +
            |gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω (Real.exp (-(k : ℝ))) y) -
              κ k x y| := abs_sub_le _ _ _
        _ < η / 2 + η / 2 := add_lt_add h hYk
        _ = η := by ring
    · simp only [W, interleavedRegularization, hs, ite_false]
      exact hYk.trans (by linarith)

end DOZZ.Assembly

/-! ### Uniqueness for compatible regularizations

Compatible admissible regularizations have the same GMC limit.

The interleaved regularization agrees with the first family at even integer logarithmic scales and
with the second at the scales `2 j + 3 / 2`. It is admissible, so its cutoff integrals are `L¹`
Cauchy; along these two scale sequences the cutoff integrals of the two families are therefore
asymptotically equal in `L¹`. Each family converges in `L¹` to its own limit, so the two limits
agree on every compact test, and a countable determining family identifies the measures. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

theorem admissibleCutoffIntegral_interleaved_nat {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y Z : Ω → ℝ → ℂ → ℝ) (γ : ℝ) (k : ℕ)
    (f : ℂ → ℝ) (ω : Ω) :
    admissibleCutoffIntegral P U dens (interleavedRegularization Y Z) γ (k : ℝ) f ω =
      admissibleCutoffIntegral P U dens Y γ (k : ℝ) f ω := by
  unfold admissibleCutoffIntegral
  simp only [interleaved_exp_neg_nat]

theorem admissibleCutoffIntegral_interleaved_odd_half {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y Z : Ω → ℝ → ℂ → ℝ) (γ : ℝ) (j : ℕ)
    (f : ℂ → ℝ) (ω : Ω) :
    admissibleCutoffIntegral P U dens (interleavedRegularization Y Z) γ (2 * (j : ℝ) + 3 / 2) f ω =
      admissibleCutoffIntegral P U dens Z γ (2 * (j : ℝ) + 3 / 2) f ω := by
  unfold admissibleCutoffIntegral
  simp only [interleaved_of_secondScale Y Z _ (secondScale_exp_neg_odd_half j)]

/-- An admissible GMC version is the `L¹` limit of the cutoff integrals of every continuous test
with compact support in the chart. -/
theorem admissibleGMCVersion_lintegral_abs_sub_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ U) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, ∀ r, R ≤ r → ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
      ∫ x, f x ∂M ω| ∂P ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR⟩ := admissibleCutoffIntegral_L1_uniform_cauchy P U dens ε₀ Y hY (tsupport f) hfc
    hfU {γ} isCompact_singleton (Set.singleton_subset_iff.mpr ⟨hγ, hγ2⟩) ‖f‖ ε hε
  refine ⟨R, fun r hr => ?_⟩
  apply lintegral_abs_sub_limit_le_of_uniform_l1_cauchy P
    (fun r => admissibleCutoffIntegral P U dens Y γ r f) _
    (fun r => admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r f f.continuous.measurable)
    (hM.2.2.2 f hfc hfU) r R ε
  intro s hs
  exact (hR r s hr hs γ rfl f f.continuous.measurable
    (fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)).le

end DOZZ.Assembly

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- Compatible admissible regularizations on one chart have the same GMC limit almost surely. -/
theorem admissibleLogRegularization_GMC_unique_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ)
    (Y Z : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hZ : IsAdmissibleLogRegularization P U dens ε₁ Z)
    (hYZ : IsCompatibleAdmissibleRegularizations P U ε₀ ε₁ Y Z)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M N : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hN : IsAdmissibleGMCVersion P U dens Z γ N) :
    ∀ᵐ ω ∂P, M ω = N ω := by
  have : IsProbabilityMeasure P := admissibleLogRegularization_isProbabilityMeasure P U dens ε₀ Y hY
  have hU : IsOpen U := hY.openChart
  have hW := interleavedRegularization_admissible P U dens ε₀ ε₁ Y Z hY hZ hYZ
  -- equality of the two limits on every compact test
  have htest : ∀ f : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (f : ℂ → ℝ) →
      tsupport (f : ℂ → ℝ) ⊆ U →
      (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] fun ω => ∫ x, f x ∂N ω := by
    intro f hfc hfU
    have hfL : ∀ x, |f x| ≤ ‖f‖ := fun x => by
      rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
    have hfK : ∀ x ∉ tsupport (f : ℂ → ℝ), f x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport hx
    have hMf : AEStronglyMeasurable (fun ω => ∫ x, f x ∂M ω) P :=
      (hM.2.2.2 f hfc hfU).aestronglyMeasurable fun r =>
        (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r f
          f.continuous.measurable).aestronglyMeasurable
    have hNf : AEStronglyMeasurable (fun ω => ∫ x, f x ∂N ω) P :=
      (hN.2.2.2 f hfc hfU).aestronglyMeasurable fun r =>
        (admissibleCutoffIntegral_measurable P U dens ε₁ Z hZ γ r f
          f.continuous.measurable).aestronglyMeasurable
    have hzero : ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂M ω - ∫ x, f x ∂N ω| ∂P = 0 := by
      apply le_antisymm _ zero_le
      apply ENNReal.le_of_forall_pos_le_add
      intro δ hδ _
      rw [zero_add]
      set ε : ℝ := (δ : ℝ) / 3 with hεdef
      have hε : 0 < ε := by positivity
      obtain ⟨RY, hRY⟩ := admissibleGMCVersion_lintegral_abs_sub_le P U dens ε₀ Y hY γ hγ hγ2 M
        hM f hfc hfU ε hε
      obtain ⟨RZ, hRZ⟩ := admissibleGMCVersion_lintegral_abs_sub_le P U dens ε₁ Z hZ γ hγ hγ2 N
        hN f hfc hfU ε hε
      obtain ⟨RW, hRW⟩ := admissibleCutoffIntegral_L1_uniform_cauchy P U dens (min ε₀ ε₁)
        (interleavedRegularization Y Z) hW (tsupport f) hfc hfU {γ} isCompact_singleton
        (Set.singleton_subset_iff.mpr ⟨hγ, hγ2⟩) ‖f‖ ε hε
      obtain ⟨j, hj⟩ := exists_nat_ge (max RY (max RZ RW))
      set r : ℝ := ((2 * j : ℕ) : ℝ) with hrdef
      set s : ℝ := 2 * (j : ℝ) + 3 / 2 with hsdef
      have hjr : max RY (max RZ RW) ≤ r := by
        rw [hrdef]; push_cast
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have hjs : max RY (max RZ RW) ≤ s := by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith
      have hRYr : RY ≤ r := (le_max_left _ _).trans hjr
      have hRZs : RZ ≤ s := ((le_max_left _ _).trans (le_max_right _ _)).trans hjs
      have hRWr : RW ≤ r := ((le_max_right _ _).trans (le_max_right _ _)).trans hjr
      have hRWs : RW ≤ s := ((le_max_right _ _).trans (le_max_right _ _)).trans hjs
      have hYmeas := admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r f
        f.continuous.measurable
      have hZmeas := admissibleCutoffIntegral_measurable P U dens ε₁ Z hZ γ s f
        f.continuous.measurable
      have hmid : ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
          admissibleCutoffIntegral P U dens Z γ s f ω| ∂P ≤ ENNReal.ofReal ε := by
        have h := (hRW r s hRWr hRWs γ rfl f f.continuous.measurable hfL hfK).le
        simp only [hrdef, admissibleCutoffIntegral_interleaved_nat, hsdef,
          admissibleCutoffIntegral_interleaved_odd_half] at h
        exact h
      have hend : ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Z γ s f ω -
          ∫ x, f x ∂N ω| ∂P ≤ ENNReal.ofReal ε := hRZ s hRZs
      have hstart : ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂M ω -
          admissibleCutoffIntegral P U dens Y γ r f ω| ∂P ≤ ENNReal.ofReal ε := by
        have h := hRY r hRYr
        refine le_of_eq_of_le ?_ h
        congr 1
        funext ω
        rw [abs_sub_comm]
      calc ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂M ω - ∫ x, f x ∂N ω| ∂P
          ≤ ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂M ω -
              admissibleCutoffIntegral P U dens Y γ r f ω| ∂P +
            ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
              ∫ x, f x ∂N ω| ∂P :=
            lintegral_ofReal_abs_sub_le_add P _ _ _ hMf.aemeasurable hYmeas.aemeasurable
        _ ≤ ENNReal.ofReal ε + (ENNReal.ofReal ε + ENNReal.ofReal ε) := by
            refine add_le_add hstart ?_
            exact (lintegral_ofReal_abs_sub_le_add P _ _ _ hYmeas.aemeasurable
              hZmeas.aemeasurable).trans (add_le_add hmid hend)
        _ = (δ : ℝ≥0∞) := by
            rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add hε.le (by positivity),
              hεdef]
            rw [show (δ : ℝ) / 3 + ((δ : ℝ) / 3 + (δ : ℝ) / 3) = (δ : ℝ) by ring]
            exact ENNReal.ofReal_coe_nnreal
    have hae := (lintegral_eq_zero_iff' (ENNReal.measurable_ofReal.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable (hMf.aemeasurable.sub hNf.aemeasurable)))).mp
      hzero
    filter_upwards [hae] with ω hω
    have h := ENNReal.ofReal_eq_zero.mp hω
    have h' : |∫ x, f x ∂M ω - ∫ x, f x ∂N ω| = 0 := le_antisymm h (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h')
  -- countable determination
  obtain ⟨K, hKc, hKU, -, -, hcof, f, hf, hdense⟩ :=
    DOZZ.Proofs.exists_countable_dense_admissible_tests U hU
  have hall : ∀ᵐ ω ∂P, ∀ nm : ℕ × ℕ, ∫ x, f nm x ∂M ω = ∫ x, f nm x ∂N ω :=
    ae_all_iff.mpr fun nm => htest (f nm) (hf nm.1 nm.2).1 (hf nm.1 nm.2).2.2
  filter_upwards [hall] with ω hω
  exact DOZZ.Proofs.admissible_countable_tests_determine_chart_measures U hU (M ω) (N ω)
    (hM.2.1 ω) (hN.2.1 ω) (fun L hL hLU => hM.2.2.1 ω L hL hLU)
    (fun L hL hLU => hN.2.2.1 ω L hL hLU) K hKc hKU hcof f
    (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩) hdense (fun n m => hω (n, m))

end DOZZ.Proofs
