/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
public import DOZZ.GMC.Moments.SetMassMeasurable
public import DOZZ.GMC.CircleAverageCutoffIntensity
public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Continuity

/-! An L¹ approximation preserves the expected mass of nonnegative observables. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

/-- If nonnegative observables converge in expected absolute difference to a limit, their
extended expectations converge to the same value as the approximants' constant expectation. -/
theorem lintegral_ofReal_eq_of_tendsto_l1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℝ → Ω → ℝ) (G : Ω → ℝ) (c : ℝ≥0∞)
    (hFmeas : ∀ r, AEMeasurable (F r) P) (hGmeas : AEMeasurable G P)
    (hFnonneg : ∀ r ω, 0 ≤ F r ω) (hGnonneg : ∀ ω, 0 ≤ G ω)
    (hmean : ∀ r, ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P = c)
    (hL1 : Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal |F r ω - G ω| ∂P)
      atTop (𝓝 0)) :
    ∫⁻ ω, ENNReal.ofReal (G ω) ∂P = c := by
  let err : ℝ → ℝ≥0∞ := fun r => ∫⁻ ω, ENNReal.ofReal |F r ω - G ω| ∂P
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa [err] using hL1
  have hsplitF (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal (F r ω) + ENNReal.ofReal |F r ω - G ω| ∂P =
        (∫⁻ ω, ENNReal.ofReal (F r ω) ∂P) + err r := by
    exact lintegral_add_left' (ENNReal.measurable_ofReal.comp_aemeasurable (hFmeas r)) _
  have hsplitG (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal (G ω) + ENNReal.ofReal |F r ω - G ω| ∂P =
        (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) + err r := by
    exact lintegral_add_left' (ENNReal.measurable_ofReal.comp_aemeasurable hGmeas) _
  have hmeanG_le (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤ c + err r := by
    have hpoint (ω : Ω) : ENNReal.ofReal (G ω) ≤
        ENNReal.ofReal (F r ω) + ENNReal.ofReal |F r ω - G ω| := by
      have hreal : G ω ≤ F r ω + |F r ω - G ω| := by
        have habs : G ω - F r ω ≤ |F r ω - G ω| := by
          rw [abs_sub_comm]
          exact le_abs_self _
        linarith
      calc
        ENNReal.ofReal (G ω) ≤ ENNReal.ofReal (F r ω + |F r ω - G ω|) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = _ := ENNReal.ofReal_add (hFnonneg r ω) (abs_nonneg _)
    calc
      ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤
          ∫⁻ ω, ENNReal.ofReal (F r ω) + ENNReal.ofReal |F r ω - G ω| ∂P :=
        lintegral_mono hpoint
      _ = c + err r := by
        rw [hsplitF r, hmean r]
  have hmean_le (r : ℝ) : c ≤
      (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) + err r := by
    have hpoint (ω : Ω) : ENNReal.ofReal (F r ω) ≤
        ENNReal.ofReal (G ω) + ENNReal.ofReal |F r ω - G ω| := by
      have hreal : F r ω ≤ G ω + |F r ω - G ω| := by
        have habs : F r ω - G ω ≤ |F r ω - G ω| := le_abs_self _
        linarith
      calc
        ENNReal.ofReal (F r ω) ≤ ENNReal.ofReal (G ω + |F r ω - G ω|) :=
          ENNReal.ofReal_le_ofReal hreal
        _ = _ := ENNReal.ofReal_add (hGnonneg ω) (abs_nonneg _)
    calc
      c = ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P := (hmean r).symm
      _ ≤ ∫⁻ ω, ENNReal.ofReal (G ω) + ENNReal.ofReal |F r ω - G ω| ∂P :=
        lintegral_mono hpoint
      _ = (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) + err r := by
        exact hsplitG r
  have hsumG : Tendsto (fun r : ℝ => c + err r) atTop (𝓝 c) := by
    simpa using Tendsto.add (tendsto_const_nhds (x := c)) herr
  have hsumMean : Tendsto (fun r : ℝ =>
      (∫⁻ ω, ENNReal.ofReal (G ω) ∂P) + err r) atTop
        (𝓝 (∫⁻ ω, ENNReal.ofReal (G ω) ∂P)) := by
    simpa using Tendsto.add (tendsto_const_nhds
      (x := ∫⁻ ω, ENNReal.ofReal (G ω) ∂P)) herr
  have hle1 : ∫⁻ ω, ENNReal.ofReal (G ω) ∂P ≤ c :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsumG hmeanG_le
  have hle2 : c ≤ ∫⁻ ω, ENNReal.ofReal (G ω) ∂P :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hsumMean hmean_le
  exact le_antisymm hle1 hle2

/-- Exact intensity on any measurable set follows from L¹ convergence of its cutoff mass. -/
theorem equatorGFF_GMC_lintegral_mass_eq_reference_of_l1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (A : Set ℂ) (hA : MeasurableSet A)
    (hL1 : Tendsto (fun r => ∫⁻ ω,
      ENNReal.ofReal |(regularizedGMC P Xc γ r ω A).toReal - (M ω A).toReal| ∂P)
      atTop (𝓝 0)) :
    ∫⁻ ω, M ω A ∂P = gmcReferenceMeasure A := by
  let F : ℝ → Ω → ℝ := fun r ω => (regularizedGMC P Xc γ r ω A).toReal
  let G : Ω → ℝ := fun ω => (M ω A).toReal
  have hFmeas : ∀ r, AEMeasurable (F r) P := by
    intro r
    have hcut : Measurable (fun ω => regularizedGMC P Xc γ r ω A) :=
      (Measure.measurable_coe hA).comp
        (regularizedGMC_measurable P X hX Xc hXc γ r)
    exact ENNReal.measurable_toReal.comp_aemeasurable hcut.aemeasurable
  have hGmeas : AEMeasurable G P := by
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_set_mass_aemeasurable_of_isGMCOf
        P X hX γ hγ hγ2 M hM A hA)
  have hFnonneg : ∀ r ω, 0 ≤ F r ω := by
    intro r ω
    exact ENNReal.toReal_nonneg
  have hGnonneg : ∀ ω, 0 ≤ G ω := by
    intro ω
    exact ENNReal.toReal_nonneg
  have hmean : ∀ r, ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P = gmcReferenceMeasure A := by
    intro r
    have hfinite := regularizedGMC_finite_ae P X hX Xc hXc γ r
    have hreal : ∀ᵐ ω ∂P,
        ENNReal.ofReal ((regularizedGMC P Xc γ r ω A).toReal) =
          regularizedGMC P Xc γ r ω A := by
      filter_upwards [hfinite] with ω hω
      exact ENNReal.ofReal_toReal
        (@MeasureTheory.measure_ne_top ℂ _ (regularizedGMC P Xc γ r ω) hω A)
    calc
      ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P =
          ∫⁻ ω, regularizedGMC P Xc γ r ω A ∂P := by
            apply lintegral_congr_ae
            exact hreal
      _ = gmcReferenceMeasure A :=
        regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r A hA
  have hL1' : Tendsto (fun r => ∫⁻ ω,
      ENNReal.ofReal |F r ω - G ω| ∂P) atTop (𝓝 0) := by
    simpa [F, G] using hL1
  have h := lintegral_ofReal_eq_of_tendsto_l1 P F G (gmcReferenceMeasure A)
    hFmeas hGmeas hFnonneg hGnonneg hmean hL1'
  have hmass : ∫⁻ ω, ENNReal.ofReal (G ω) ∂P = ∫⁻ ω, M ω A ∂P := by
    apply lintegral_congr_ae
    filter_upwards [] with ω
    exact ENNReal.ofReal_toReal
      (@MeasureTheory.measure_ne_top ℂ _ (M ω) (hM.1 ω) A)
  rw [hmass] at h
  exact h

/-- The reference measure has positive mass already on the unit disk. -/
theorem gmcReferenceMeasure_unitBall_pos :
    0 < gmcReferenceMeasure (Metric.ball (0 : ℂ) 1) := by
  let B : Set ℂ := Metric.ball (0 : ℂ) 1
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hvolume : 0 < volume B := Metric.measure_ball_pos volume 0 (by norm_num)
  have hle : volume B ≤ gmcReferenceMeasure B := by
    rw [gmcReferenceMeasure, withDensity_apply _ hB]
    calc
      volume B = ∫⁻ x in B, (1 : ℝ≥0∞) ∂volume := by simp
      _ ≤ ∫⁻ x in B, ENNReal.ofReal (normPlus x ^ (-4 : ℝ)) ∂volume :=
        setLIntegral_mono (s := B) (f := fun _ : ℂ => (1 : ℝ≥0∞))
          (g := fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)))
          (by fun_prop [normPlus])
          (fun x hx => by
            have hxnorm : ‖x‖ < 1 := by
              simpa [B, Metric.mem_ball, dist_eq_norm] using hx
            have hplus : normPlus x = 1 := by
              simp [normPlus, max_eq_left hxnorm.le]
            simp [hplus])
  exact lt_of_lt_of_le hvolume hle

/-- Exact expected intensity on all measurable sets rules out the zero GMC. -/
theorem equatorGFF_GMC_nontrivial_of_intensity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ)
    (hIntensity : ∀ A : Set ℂ, MeasurableSet A →
      ∫⁻ ω, M ω A ∂P = gmcReferenceMeasure A) :
    ¬ ∀ᵐ ω ∂P, M ω = 0 := by
  intro hzero
  let B : Set ℂ := Metric.ball (0 : ℂ) 1
  have hB : MeasurableSet B := Metric.isOpen_ball.measurableSet
  have hmassZero : ∀ᵐ ω ∂P, M ω B = 0 := by
    filter_upwards [hzero] with ω hω
    rw [hω]
    simp
  have hmass : ∫⁻ ω, M ω B ∂P = 0 := by
    calc
      ∫⁻ ω, M ω B ∂P = ∫⁻ ω, (0 : ℝ≥0∞) ∂P :=
        lintegral_congr_ae hmassZero
      _ = 0 := by simp
  have hreference : gmcReferenceMeasure B = 0 := by
    rw [← hmass]
    exact (hIntensity B hB).symm
  exact (gmcReferenceMeasure_unitBall_pos).ne' hreference

/-- Exact intensity on every measurable set follows once the cutoff set masses converge in L¹
on bounded sets. The unbounded case is monotone exhaustion by closed balls. -/
theorem equatorGFF_GMC_intensity_of_bounded_mass_l1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (hL1 : ∀ A : Set ℂ, MeasurableSet A → ∀ R : ℝ,
      A ⊆ Metric.closedBall 0 R →
      Tendsto (fun r => ∫⁻ ω,
        ENNReal.ofReal |(regularizedGMC P Xc γ r ω A).toReal - (M ω A).toReal| ∂P)
        atTop (𝓝 0))
    (A : Set ℂ) (hA : MeasurableSet A) :
    ∫⁻ ω, M ω A ∂P = gmcReferenceMeasure A := by
  obtain ⟨N, hNmeas, _hNfinite, hMN⟩ :=
    equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  let ν : Measure ℂ := (P.map N).join
  have hνEval (B : Set ℂ) (hB : MeasurableSet B) :
      ν B = ∫⁻ ω, M ω B ∂P := by
    dsimp [ν]
    rw [Measure.join_apply hB,
      lintegral_map (Measure.measurable_coe hB) hNmeas]
    apply lintegral_congr_ae
    filter_upwards [hMN] with ω hω
    rw [hω]
  let B : ℕ → Set ℂ := fun n => A ∩ Metric.closedBall 0 ((n + 1 : ℕ) : ℝ)
  have hBmeas (n : ℕ) : MeasurableSet (B n) :=
    hA.inter Metric.isClosed_closedBall.measurableSet
  have hBsubset (n : ℕ) : B n ⊆ Metric.closedBall 0 ((n + 1 : ℕ) : ℝ) :=
    Set.inter_subset_right
  have hBintensity (n : ℕ) : ν (B n) = gmcReferenceMeasure (B n) := by
    rw [hνEval (B n) (hBmeas n)]
    exact equatorGFF_GMC_lintegral_mass_eq_reference_of_l1
      P X hX Xc hXc γ hγ hγ2 M hM (B n) (hBmeas n)
        (hL1 (B n) (hBmeas n) ((n + 1 : ℕ) : ℝ) (hBsubset n))
  have hBmono : Monotone B := by
    intro i j hij
    apply Set.inter_subset_inter_right
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hBunion : (⋃ n, B n) = A := by
    ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨n, hn⟩
      exact hn.1
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      apply Set.mem_iUnion.mpr
      refine ⟨n, ⟨hx, ?_⟩⟩
      change dist x 0 ≤ ((n + 1 : ℕ) : ℝ)
      rw [dist_zero_right]
      exact hn.le.trans (by norm_num)
  have hνlim : Tendsto (fun n : ℕ => ν (B n)) atTop (𝓝 (ν A)) := by
    rw [← hBunion]
    exact tendsto_measure_iUnion_atTop (μ := ν) hBmono
  have hrefLim : Tendsto (fun n : ℕ => gmcReferenceMeasure (B n)) atTop
      (𝓝 (gmcReferenceMeasure A)) := by
    rw [← hBunion]
    exact tendsto_measure_iUnion_atTop (μ := gmcReferenceMeasure) hBmono
  have hSeqEq : (fun n : ℕ => ν (B n)) = fun n => gmcReferenceMeasure (B n) :=
    funext hBintensity
  have hνA : ν A = gmcReferenceMeasure A :=
    tendsto_nhds_unique hνlim (hSeqEq ▸ hrefLim)
  rw [← hνEval A hA]
  exact hνA

end DOZZ.Proofs
