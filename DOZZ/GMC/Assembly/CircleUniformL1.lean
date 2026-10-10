/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Assembly.CircleIntensity
public import DOZZ.GMC.Construction.GMCUniformL1FromCauchy
public import DOZZ.GMC.Assembly.CutoffIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import DOZZ.GMC.Construction.ReferenceMeasureTight

/-! Uniform `L¹` convergence of the circle cutoff chaos (proof of `DOZZ.equatorGFF_GMC_uniform_L1`)
and `L¹` continuity of circle GMC masses in the charge (proof of
`DOZZ.equatorGFF_GMC_L1_continuous_gamma`). -/

@[expose] public section

/-! ### Uniform `L¹` convergence

Uniform `L¹` convergence of the circle cutoff chaos to the GMC, uniformly over compact
charge intervals and bounded Borel tests supported in a compact set.

Continuous tests converge uniformly by the cutoff `L¹` Cauchy estimate and Fatou along convergence
in measure. A Borel test is within any prescribed reference `L¹` distance of a continuous test
with the same bound; both the cutoff chaos and the limit have intensity at most the reference
measure, so this distance controls both approximation errors. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- Uniform `L¹` convergence of regularized GMC masses on compact charge intervals, uniformly
over bounded Borel tests supported in a compact set. -/
theorem equatorGFF_GMC_uniform_L1
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (I : Set ℝ) (hI : IsCompact I) (hI2 : I ⊆ Set.Ioo 0 2)
    (K : Set ℂ) (hK : IsCompact K) (Lb : ℝ) :
    Tendsto (fun r : ℝ => ⨆ γ ∈ I, ⨆ (f : ℂ → ℝ) (_ : Measurable f)
        (_ : ∀ x, |f x| ≤ Lb) (_ : ∀ x ∉ K, f x = 0),
        ∫⁻ ω, ENNReal.ofReal
          |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P)
      atTop (𝓝 0) := by
  classical
  have : IsProbabilityMeasure P := hX.1
  have : IsFiniteMeasure gmcReferenceMeasure :=
    ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, K ⊆ Metric.closedBall (0 : ℂ) ρ := hK.isBounded.subset_closedBall 0
  set Lb' : ℝ := max Lb 0 with hLb'def
  set K' : Set ℂ := Metric.closedBall (0 : ℂ) (ρ + 1) with hK'def
  have hK' : IsCompact K' := isCompact_closedBall _ _
  let ι := {p : ℝ × (ℂ → ℝ) // p.1 ∈ I ∧ Continuous p.2 ∧ (∀ x, |p.2 x| ≤ Lb') ∧
    ∀ x, ρ + 1 < ‖x‖ → p.2 x = 0}
  let bcf : ι → BoundedContinuousFunction ℂ ℝ := fun i => BoundedContinuousFunction.ofNormedAddCommGroup i.1.2
    i.2.2.1 Lb' (fun x => by rw [Real.norm_eq_abs]; exact i.2.2.2.1 x)
  let F : ℝ → ι → Ω → ℝ := fun r i ω => ∫ x, i.1.2 x ∂regularizedGMC P Xc i.1.1 r ω
  let G : ι → Ω → ℝ := fun i ω => ∫ x, i.1.2 x ∂Mfam i.1.1 ω
  have hFmeas : ∀ r i, Measurable (F r i) := fun r i =>
    regularizedGMC_integral_measurable P X hX Xc hXc _ r _ i.2.2.1.measurable
  have hFG : ∀ i, TendstoInMeasure P (fun r => F r i) atTop (G i) := fun i =>
    isGMCOf_tendstoInMeasure P X hX Xc hXc i.1.1 (Mfam i.1.1) (hMfam _ (hI2 i.2.1)) (bcf i)
  have hCauchy : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ r ≥ R, ∀ s ≥ R, ∀ i,
      ∫⁻ ω, ENNReal.ofReal |F r i ω - F s i ω| ∂P < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := regularizedGMC_integral_L1_uniform_cauchy P X hX Xc hXc I hI hI2 K' hK'
      Lb' ε hε
    refine ⟨R, fun r hr s hs i => hR r s hr hs i.1.1 i.2.1 i.1.2 i.2.2.1.measurable i.2.2.2.1
      (fun x hx => i.2.2.2.2 x ?_)⟩
    simpa [K', Metric.mem_closedBall, dist_zero_right] using hx
  have hS := tendsto_iSup_lintegral_abs_sub_of_uniform_l1_cauchy P F G hFmeas hFG hCauchy
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS (fun r => zero_le)
    (fun r => ?_)
  refine iSup₂_le fun γ hγ => iSup_le fun f => iSup_le fun hf => iSup_le fun hfL =>
    iSup_le fun hfK => ?_
  have hγ2 := hI2 hγ
  have hM := hMfam γ hγ2
  obtain ⟨N, hNmeas, -, hMN⟩ :=
    DOZZ.Proofs.equatorGFF_GMC_measurable_version P X hX γ hγ2.1 hγ2.2 (Mfam γ) hM
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hδ2 : ((δ / 2 : ℝ≥0) : ℝ≥0∞) ≠ 0 := by
    simpa using (half_pos hδ).ne'
  have hfρ : ∀ x, ρ < ‖x‖ → f x = 0 := fun x hx => hfK x (fun hxK => by
    have := hρ hxK
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith)
  obtain ⟨h, hcont, hhL, hhsupp, happrox⟩ := exists_continuous_L1_approx gmcReferenceMeasure ρ
    Lb' f hf (fun x => (hfL x).trans (le_max_left _ _)) hfρ _ hδ2
  let i : ι := ⟨(γ, h), hγ, hcont, hhL, hhsupp⟩
  have hfh : Measurable (fun x => ENNReal.ofReal |f x - h x|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hf.sub hcont.measurable))
  have hhf : Measurable (fun x => ENNReal.ofReal |h x - f x|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hcont.measurable.sub hf))
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω -
      ∫ x, f x ∂Mfam γ ω| ≤
      ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω +
        (ENNReal.ofReal |F r i ω - G i ω| + ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω) := by
    filter_upwards [hMN] with ω hω
    set A := ∫ x, f x ∂regularizedGMC P Xc γ r ω
    set A' := ∫ x, h x ∂regularizedGMC P Xc γ r ω
    set B' := ∫ x, h x ∂Mfam γ ω
    set B := ∫ x, f x ∂Mfam γ ω
    have hFi : F r i ω = A' := rfl
    have hGi : G i ω = B' := rfl
    rw [hFi, hGi]
    calc ENNReal.ofReal |A - B| ≤ ENNReal.ofReal (|A - A'| + |A' - B'| + |B' - B|) := by
          apply ENNReal.ofReal_le_ofReal
          calc |A - B| = |(A - A') + (A' - B') + (B' - B)| := by ring_nf
            _ ≤ |A - A'| + |A' - B'| + |B' - B| := abs_add_three _ _ _
      _ = ENNReal.ofReal |A - A'| + (ENNReal.ofReal |A' - B'| + ENNReal.ofReal |B' - B|) := by
          rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
            ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _), add_assoc]
      _ ≤ _ := by
          gcongr
          · exact ofReal_abs_integral_sub_le_lintegral _ f h hf hcont.measurable
          · calc ENNReal.ofReal |B' - B| ≤ ∫⁻ x, ENNReal.ofReal |h x - f x| ∂Mfam γ ω :=
                ofReal_abs_integral_sub_le_lintegral (Mfam γ ω) h f hcont.measurable hf
              _ = ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω := by rw [hω]
  have ha : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω) :=
    (Measure.measurable_lintegral hfh).comp (regularizedGMC_measurable P X hX Xc hXc γ r)
  have hc : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω) :=
    (Measure.measurable_lintegral hhf).comp hNmeas
  have hA : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω ∂P ≤
      ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r _ hfh]
    exact happrox
  have hC : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω ∂P ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) := by
    calc ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω ∂P =
          ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂Mfam γ ω ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hMN] with ω hω
          rw [hω]
      _ ≤ ∫⁻ x, ENNReal.ofReal |h x - f x| ∂gmcReferenceMeasure :=
          isGMCOf_lintegral_le P X hX γ hγ2.1 hγ2.2 (Mfam γ) hM _ hhf
      _ = ∫⁻ x, ENNReal.ofReal |f x - h x| ∂gmcReferenceMeasure := by
          apply lintegral_congr
          intro x
          rw [abs_sub_comm]
      _ ≤ _ := happrox
  have hB : ∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P ≤
      ⨆ j, ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P :=
    le_iSup (fun j => ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P) i
  calc ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P
      ≤ ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω +
        (ENNReal.ofReal |F r i ω - G i ω| + ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω) ∂P :=
        lintegral_mono_ae hpt
    _ = ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |f x - h x| ∂regularizedGMC P Xc γ r ω ∂P +
        (∫⁻ ω, ENNReal.ofReal |F r i ω - G i ω| ∂P +
          ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x - f x| ∂N ω ∂P) := by
        rw [lintegral_add_left ha, lintegral_add_right _ hc]
    _ ≤ ((δ / 2 : ℝ≥0) : ℝ≥0∞) + ((⨆ j, ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P) +
        ((δ / 2 : ℝ≥0) : ℝ≥0∞)) := add_le_add hA (add_le_add hB hC)
    _ = (⨆ j, ∫⁻ ω, ENNReal.ofReal |F r j ω - G j ω| ∂P) + δ := by
        rw [add_comm, add_assoc, ← ENNReal.coe_add, add_halves]

end DOZZ.Proofs

/-! ### Fixed-cutoff continuity in the charge

At a fixed cutoff, admissible cutoff integrals are continuous in the charge in `L¹(P)`.

The Wick weights `exp (γ Z - γ² v / 2)` of a centered Gaussian `Z` with variance `v` are dominated,
for charges near `γ₀`, by `2 (exp (c Z) + exp (-c Z))`, whose expectation is finite by Wick
normalization; dominated convergence in the sample and then in the point gives continuity. -/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- The Gaussian exponential moments of one admissible coordinate are finite. -/
theorem admissible_lintegral_exp_mul_ne_top
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) (hε : 0 < ε) (hεcut : ε ≤ ε₀)
    (x : ℂ) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * Y ω ε x)) ∂P ≠ ⊤ := by
  have hone := lintegral_admissibleLogWickWeight P U dens ε₀ Y hY t ε hε hεcut x
  have heq : (fun ω => ENNReal.ofReal (Real.exp (t * Y ω ε x))) = fun ω =>
      ENNReal.ofReal (Real.exp (t ^ 2 / 2 * gaussianVariance P (fun ω => Y ω ε x))) *
        admissibleLogWickWeight P Y t ε x ω := by
    funext ω
    unfold admissibleLogWickWeight
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  rw [heq, lintegral_const_mul _ (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY t ε x),
    hone, mul_one]
  exact ENNReal.ofReal_ne_top

/-- The Wick weight at one point is continuous in the charge in `L¹(P)`. -/
theorem admissible_wick_weight_L1_continuous
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (ε : ℝ) (hε : 0 < ε) (hεcut : ε ≤ ε₀)
    (x : ℂ) (γ₀ : ℝ) :
    Tendsto (fun γ => ∫⁻ ω, ENNReal.ofReal
        |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
          Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)| ∂P)
      (𝓝 γ₀) (𝓝 0) := by
  set v : ℝ := ∫ ω', Y ω' ε x ^ 2 ∂P with hvdef
  have hv : 0 ≤ v := integral_nonneg fun ω => sq_nonneg _
  set c : ℝ := |γ₀| + 1 with hcdef
  have hZ : Measurable (fun ω => Y ω ε x) := admissible_field_measurable_sample P U dens ε₀ Y hY ε x
  let bound : Ω → ℝ≥0∞ := fun ω => 2 * (ENNReal.ofReal (Real.exp (c * Y ω ε x)) +
    ENNReal.ofReal (Real.exp (-c * Y ω ε x)))
  have hexp_le (t z : ℝ) (ht : |t| ≤ c) :
      Real.exp (t * z) ≤ Real.exp (c * z) + Real.exp (-c * z) := by
    have hle : t * z ≤ c * |z| := by
      calc t * z ≤ |t * z| := le_abs_self _
        _ = |t| * |z| := abs_mul _ _
        _ ≤ c * |z| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    rcases le_total 0 z with hz | hz
    · rw [abs_of_nonneg hz] at hle
      exact (Real.exp_le_exp.mpr hle).trans (le_add_of_nonneg_right (Real.exp_pos _).le)
    · rw [abs_of_nonpos hz] at hle
      have : t * z ≤ -c * z := by linarith
      exact (Real.exp_le_exp.mpr this).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hweight_le (t z : ℝ) (ht : |t| ≤ c) :
      Real.exp (t * z - t ^ 2 / 2 * v) ≤ Real.exp (c * z) + Real.exp (-c * z) := by
    refine le_trans (Real.exp_le_exp.mpr ?_) (hexp_le t z ht)
    have : 0 ≤ t ^ 2 / 2 * v := by positivity
    linarith
  rw [show (𝓝 (0 : ℝ≥0∞)) = 𝓝 (∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P) by rw [lintegral_zero]]
  apply tendsto_lintegral_filter_of_dominated_convergence (f := fun _ => 0) bound
  · filter_upwards [] with γ
    exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      ((Real.measurable_exp.comp ((hZ.const_mul γ).sub_const _)).sub
        (Real.measurable_exp.comp ((hZ.const_mul γ₀).sub_const _))))
  · have hball : ∀ᶠ γ in 𝓝 γ₀, |γ| ≤ c := by
      filter_upwards [Metric.ball_mem_nhds γ₀ one_pos] with γ hγ
      rw [Metric.mem_ball, Real.dist_eq] at hγ
      have := abs_sub_abs_le_abs_sub γ γ₀
      rw [hcdef]
      linarith
    filter_upwards [hball] with γ hγ
    filter_upwards [] with ω
    have hγ₀c : |γ₀| ≤ c := by rw [hcdef]; linarith
    have h1 := hweight_le γ (Y ω ε x) hγ
    have h2 := hweight_le γ₀ (Y ω ε x) hγ₀c
    have hsum : |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * v) - Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)|
        ≤ 2 * (Real.exp (c * Y ω ε x) + Real.exp (-c * Y ω ε x)) := by
      rw [abs_le]
      constructor <;> linarith [Real.exp_pos (γ * Y ω ε x - γ ^ 2 / 2 * v),
        Real.exp_pos (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)]
    calc ENNReal.ofReal |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * v) -
          Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)|
        ≤ ENNReal.ofReal (2 * (Real.exp (c * Y ω ε x) + Real.exp (-c * Y ω ε x))) :=
          ENNReal.ofReal_le_ofReal hsum
      _ = bound ω := by
          simp only [bound]
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (Real.exp_pos _).le
            (Real.exp_pos _).le, ENNReal.ofReal_ofNat]
  · have h1 := admissible_lintegral_exp_mul_ne_top P U dens ε₀ Y hY ε hε hεcut x c
    have h2 := admissible_lintegral_exp_mul_ne_top P U dens ε₀ Y hY ε hε hεcut x (-c)
    have hm1 : Measurable (fun ω => ENNReal.ofReal (Real.exp (c * Y ω ε x))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hZ.const_mul c))
    have hm2 : Measurable (fun ω => ENNReal.ofReal (Real.exp (-c * Y ω ε x))) :=
      ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hZ.const_mul (-c)))
    have hm12 : Measurable (fun ω => ENNReal.ofReal (Real.exp (c * Y ω ε x)) +
        ENNReal.ofReal (Real.exp (-c * Y ω ε x))) := hm1.add hm2
    simp only [bound]
    rw [lintegral_const_mul _ hm12, lintegral_add_left hm1]
    exact ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨h1, h2⟩)
  · filter_upwards [] with ω
    have hcont : Continuous (fun γ : ℝ => ENNReal.ofReal
        |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * v) - Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * v)|) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    have h := hcont.tendsto γ₀
    simpa using h

/-- At a fixed admissible cutoff, the cutoff integral of a bounded Borel test supported in a
compact chart is continuous in the charge in `L¹(P)`. -/
theorem admissibleCutoffIntegral_L1_continuous_in_charge
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) (r : ℝ) (hr : Real.exp (-r) ≤ ε₀)
    (L : ℝ) (g : ℂ → ℝ) (hg : Measurable g) (hgL : ∀ x, |g x| ≤ L)
    (hgK : ∀ x ∉ K, g x = 0) (γ₀ : ℝ) :
    Tendsto (fun γ => ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r g ω -
        admissibleCutoffIntegral P U dens Y γ₀ r g ω| ∂P) (𝓝 γ₀) (𝓝 0) := by
  have hσK := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
  set ε := Real.exp (-r) with hεdef
  have hε : 0 < ε := Real.exp_pos _
  let D : ℝ → ℂ → ℝ≥0∞ := fun γ x => ∫⁻ ω, ENNReal.ofReal
    |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
      Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)| ∂P
  have hv : Measurable (fun x => ∫ ω', Y ω' ε x ^ 2 ∂P) := by
    have heq : (fun x => ∫ ω', Y ω' ε x ^ 2 ∂P) =
        fun x => gaussianVariance P (fun ω => Y ω ε x) := by
      funext x
      unfold gaussianVariance gaussianCovariance
      simp only [pow_two]
    rw [heq]
    exact admissibleLogRegularization_variance_measurable P U dens ε₀ Y hY ε
  have hfield : Measurable (fun q : Ω × ℂ => Y q.1 ε q.2) := hY.measurableAtScale ε
  have hjoint (γ : ℝ) : Measurable (fun q : ℂ × Ω => ENNReal.ofReal
      |Real.exp (γ * Y q.2 ε q.1 - γ ^ 2 / 2 * ∫ ω', Y ω' ε q.1 ^ 2 ∂P) -
        Real.exp (γ₀ * Y q.2 ε q.1 - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε q.1 ^ 2 ∂P)|) := by
    have h1 : Measurable (fun q : ℂ × Ω => Y q.2 ε q.1) := hfield.comp measurable_swap
    have h2 : Measurable (fun q : ℂ × Ω => ∫ ω', Y ω' ε q.1 ^ 2 ∂P) := hv.comp measurable_fst
    fun_prop
  have hDmeas (γ : ℝ) : Measurable (D γ) := (hjoint γ).lintegral_prod_right'
  have hDle (γ : ℝ) (x : ℂ) : D γ x ≤ 2 := by
    calc D γ x ≤ ∫⁻ ω, (ENNReal.ofReal (Real.exp (γ * Y ω ε x - γ ^ 2 / 2 *
          ∫ ω', Y ω' ε x ^ 2 ∂P)) + ENNReal.ofReal (Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 *
          ∫ ω', Y ω' ε x ^ 2 ∂P))) ∂P := by
          apply lintegral_mono
          intro ω
          beta_reduce
          rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          rw [abs_le]
          constructor <;> linarith [Real.exp_pos (γ * Y ω ε x - γ ^ 2 / 2 *
            ∫ ω', Y ω' ε x ^ 2 ∂P), Real.exp_pos (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 *
            ∫ ω', Y ω' ε x ^ 2 ∂P)]
      _ = 1 + 1 := by
          simp only [ofReal_exp_eq_admissibleLogWickWeight]
          rw [lintegral_add_left (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY γ
            ε x), lintegral_admissibleLogWickWeight P U dens ε₀ Y hY γ ε hε hr x,
            lintegral_admissibleLogWickWeight P U dens ε₀ Y hY γ₀ ε hε hr x]
      _ = 2 := by norm_num
  -- the expected difference is bounded by the integrated weight difference
  have hbound (γ : ℝ) : ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r g ω -
      admissibleCutoffIntegral P U dens Y γ₀ r g ω| ∂P ≤
      ENNReal.ofReal L * ∫⁻ x, D γ x ∂(logRegularizationReference U dens).restrict K := by
    have hpt (ω : Ω) : ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r g ω -
        admissibleCutoffIntegral P U dens Y γ₀ r g ω| ≤
        ENNReal.ofReal L * ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂(logRegularizationReference U dens).restrict K := by
      unfold admissibleCutoffIntegral
      refine (ofReal_abs_integral_sub_le_lintegral _ _ _
        (admissibleCutoff_integrand_measurable P U dens ε₀ Y hY γ r g hg ω)
        (admissibleCutoff_integrand_measurable P U dens ε₀ Y hY γ₀ r g hg ω)).trans ?_
      have hFx : Measurable (fun x => ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|) :=
        ((hjoint γ).comp (measurable_id.prodMk measurable_const) :)
      rw [← setLIntegral_eq_of_support_subset (s := K)]
      · rw [← lintegral_const_mul _ hFx]
        apply lintegral_mono
        intro x
        beta_reduce
        rw [← mul_sub, abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
        exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hgL x)) _
      · intro x hx
        by_contra hxK
        exact hx (by simp [hgK x hxK])
    have hint : ∫⁻ ω, ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂(logRegularizationReference U dens).restrict K ∂P =
        ∫⁻ x, D γ x ∂(logRegularizationReference U dens).restrict K := by
      apply lintegral_lintegral_swap
      exact ((hjoint γ).comp measurable_swap).aemeasurable
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal L * ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂(logRegularizationReference U dens).restrict K ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal L * ∫⁻ ω, ∫⁻ x, ENNReal.ofReal
          |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
            Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
          ∂(logRegularizationReference U dens).restrict K ∂P := by
          have hΦ : Measurable (fun ω => ∫⁻ x, ENNReal.ofReal
              |Real.exp (γ * Y ω ε x - γ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P) -
                Real.exp (γ₀ * Y ω ε x - γ₀ ^ 2 / 2 * ∫ ω', Y ω' ε x ^ 2 ∂P)|
              ∂(logRegularizationReference U dens).restrict K) :=
            ((hjoint γ).comp measurable_swap).lintegral_prod_right'
          rw [lintegral_const_mul _ hΦ]
      _ = _ := by rw [hint]
  have hDlim : Tendsto (fun γ => ∫⁻ x, D γ x ∂(logRegularizationReference U dens).restrict K)
      (𝓝 γ₀) (𝓝 0) := by
    have h := tendsto_lintegral_filter_of_dominated_convergence
      (μ := (logRegularizationReference U dens).restrict K) (f := fun _ => 0) (fun _ => 2)
      (Eventually.of_forall hDmeas) (Eventually.of_forall fun γ => ae_of_all _ (hDle γ))
      (by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top (by norm_num) hσK)
      (ae_of_all _ fun x => admissible_wick_weight_L1_continuous P U dens ε₀ Y hY ε hε hr x γ₀)
    simpa using h
  have hmul : Tendsto (fun γ => ENNReal.ofReal L *
      ∫⁻ x, D γ x ∂(logRegularizationReference U dens).restrict K) (𝓝 γ₀) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal L) hDlim
      (Or.inr ENNReal.ofReal_ne_top)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmul (fun _ => zero_le)
    hbound

end DOZZ.Assembly

/-! ### `L¹` continuity in the charge

`L¹` continuity of circle GMC masses in the charge, for bounded continuous tests.

A bounded continuous test splits into a compactly supported part and a tail. The tail is
uniformly small by the intensity bound and the reference tail. For the compact part, cutoff
masses converge uniformly on a compact charge neighbourhood, and at a fixed cutoff they depend
continuously on the charge in `L¹`. -/

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Assembly

open DOZZ.Proofs

/-- Bounded measurable tests integrate measurably against a measurable finite random measure. -/
theorem measurable_integral_of_measurable_kernel
    {Ω : Type*} [MeasurableSpace Ω] (N : Ω → Measure ℂ) (hN : Measurable N)
    (hfin : ∀ ω, IsFiniteMeasure (N ω)) (φ : ℂ → ℝ) (hφ : Measurable φ) (C : ℝ)
    (hC : ∀ x, |φ x| ≤ C) :
    Measurable (fun ω => ∫ x, φ x ∂N ω) := by
  have hint (ω : Ω) : Integrable φ (N ω) := by
    have := hfin ω
    exact Integrable.of_bound hφ.aestronglyMeasurable C (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hC x)
  have heq : (fun ω => ∫ x, φ x ∂N ω) = fun ω =>
      (∫⁻ x, ENNReal.ofReal (φ x) ∂N ω).toReal - (∫⁻ x, ENNReal.ofReal (-φ x) ∂N ω).toReal := by
    funext ω
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint ω)
  rw [heq]
  exact ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hφ)).comp
    hN).ennreal_toReal.sub ((Measure.measurable_lintegral
      (ENNReal.measurable_ofReal.comp hφ.neg)).comp hN).ennreal_toReal

/-- Bounded measurable tests integrate almost everywhere measurably against a circle GMC
version. -/
theorem isGMCOf_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (φ : ℂ → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ x, |φ x| ≤ C) :
    AEMeasurable (fun ω => ∫ x, φ x ∂M ω) P := by
  obtain ⟨N, hNmeas, hNfin, hMN⟩ :=
    DOZZ.Proofs.equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  refine ⟨fun ω => ∫ x, φ x ∂N ω,
    measurable_integral_of_measurable_kernel N hNmeas hNfin φ hφ C hC, ?_⟩
  filter_upwards [hMN] with ω hω
  rw [hω]

/-- The triangle inequality for expected absolute differences of almost everywhere measurable
real random variables. -/
theorem lintegral_ofReal_abs_sub_le_add
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U V W : Ω → ℝ)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P) :
    ∫⁻ ω, ENNReal.ofReal |U ω - W ω| ∂P ≤
      ∫⁻ ω, ENNReal.ofReal |U ω - V ω| ∂P + ∫⁻ ω, ENNReal.ofReal |V ω - W ω| ∂P := by
  have hUV : AEMeasurable (fun ω => ENNReal.ofReal |U ω - V ω|) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (continuous_abs.measurable.comp_aemeasurable
      (hU.sub hV))
  rw [← lintegral_add_left' hUV]
  apply lintegral_mono
  intro ω
  beta_reduce
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc |U ω - W ω| = |(U ω - V ω) + (V ω - W ω)| := by ring_nf
    _ ≤ |U ω - V ω| + |V ω - W ω| := abs_add_le _ _

end DOZZ.Assembly

namespace DOZZ.Proofs

open DOZZ.Assembly

/-- `L¹` continuity of the GMC mass against bounded continuous tests as the charge varies on
the same probability space. -/
theorem equatorGFF_GMC_L1_continuous_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Mfam : ℝ → Ω → Measure ℂ)
    (hMfam : ∀ γ ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X γ (Mfam γ))
    (f : BoundedContinuousFunction ℂ ℝ) (γ₀ : ℝ) (hγ₀ : γ₀ ∈ Set.Ioo (0 : ℝ) 2) :
    Tendsto (fun γ => ∫⁻ ω, ENNReal.ofReal
        |∫ x, f x ∂Mfam γ ω - ∫ x, f x ∂Mfam γ₀ ω| ∂P) (𝓝 γ₀) (𝓝 0) := by
  classical
  have : IsProbabilityMeasure P := hX.1
  have : IsFiniteMeasure gmcReferenceMeasure :=
    ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  obtain ⟨Xc, hXc, -⟩ := (hMfam γ₀ hγ₀).2
  set δ₀ : ℝ := min (γ₀ / 2) ((2 - γ₀) / 2) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min (by linarith [hγ₀.1]) (by linarith [hγ₀.2])
  set I : Set ℝ := Icc (γ₀ - δ₀) (γ₀ + δ₀) with hIdef
  have hI : IsCompact I := isCompact_Icc
  have hI2 : I ⊆ Ioo 0 2 := by
    intro γ hγ
    have h1 : δ₀ ≤ γ₀ / 2 := min_le_left _ _
    have h2 : δ₀ ≤ (2 - γ₀) / 2 := min_le_right _ _
    constructor <;> linarith [hγ.1, hγ.2, hγ₀.1, hγ₀.2]
  have hInhds : I ∈ 𝓝 γ₀ := Icc_mem_nhds (by linarith) (by linarith)
  set Lf : ℝ := ‖f‖ with hLfdef
  have hLf : 0 ≤ Lf := norm_nonneg _
  have hfL (x : ℂ) : |f x| ≤ Lf := by
    rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x
  have hmain : ∀ ε : ℝ, 0 < ε → ∀ᶠ γ in 𝓝 γ₀, ∫⁻ ω, ENNReal.ofReal
      |∫ x, f x ∂Mfam γ ω - ∫ x, f x ∂Mfam γ₀ ω| ∂P ≤ ENNReal.ofReal ε := by
    intro ε hε
    have hε5 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 5) := ENNReal.ofReal_pos.mpr (by linarith)
    -- the tail radius
    have htail := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal Lf)
      gmcReferenceMeasure_compl_closedBall_tendsto_zero (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at htail
    obtain ⟨n, hn⟩ := (htail.eventually (gt_mem_nhds hε5)).exists
    set R : ℝ := (n : ℝ) with hRdef
    let g : ℂ → ℝ := fun x => f x * ballCutoff R x
    let h : ℂ → ℝ := fun x => f x * (1 - ballCutoff R x)
    have hgm : Measurable g := f.continuous.measurable.mul (continuous_ballCutoff R).measurable
    have hhm : Measurable h :=
      f.continuous.measurable.mul (measurable_const.sub (continuous_ballCutoff R).measurable)
    have hgL (x : ℂ) : |g x| ≤ Lf := by
      simp only [g, abs_mul, abs_of_nonneg (ballCutoff_nonneg R x)]
      calc |f x| * ballCutoff R x ≤ Lf * 1 :=
            mul_le_mul (hfL x) (ballCutoff_le_one R x) (ballCutoff_nonneg R x) hLf
        _ = Lf := mul_one _
    have hgK (x : ℂ) (hx : x ∉ Metric.closedBall (0 : ℂ) (R + 1)) : g x = 0 := by
      have : R + 1 < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx; exact hx
      simp only [g, ballCutoff_eq_zero R x this, mul_zero]
    have hfgh (x : ℂ) : f x = g x + h x := by simp only [g, h]; ring
    have hhabs (x : ℂ) : ENNReal.ofReal |h x| ≤
        ENNReal.ofReal Lf * (Metric.closedBall (0 : ℂ) R)ᶜ.indicator (fun _ => 1) x := by
      by_cases hx : x ∈ Metric.closedBall (0 : ℂ) R
      · have hx' : ‖x‖ ≤ R := by rwa [Metric.mem_closedBall, dist_zero_right] at hx
        simp [h, ballCutoff_eq_one R x hx']
      · rw [Set.indicator_of_mem (show x ∈ (Metric.closedBall (0 : ℂ) R)ᶜ from hx), mul_one]
        apply ENNReal.ofReal_le_ofReal
        simp only [h, abs_mul]
        have h1 : |1 - ballCutoff R x| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [ballCutoff_nonneg R x, ballCutoff_le_one R x]
        calc |f x| * |1 - ballCutoff R x| ≤ Lf * 1 :=
              mul_le_mul (hfL x) h1 (abs_nonneg _) hLf
          _ = Lf := mul_one _
    -- the tail of any charge in the neighbourhood
    have htailbound (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
        ∫⁻ ω, ∫⁻ x, ENNReal.ofReal |h x| ∂Mfam γ ω ∂P ≤ ENNReal.ofReal (ε / 5) := by
      have hφ : Measurable (fun x => ENNReal.ofReal |h x|) :=
        ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hhm)
      refine (isGMCOf_lintegral_le P X hX γ hγ.1 hγ.2 (Mfam γ) (hMfam γ hγ) _ hφ).trans ?_
      calc ∫⁻ x, ENNReal.ofReal |h x| ∂gmcReferenceMeasure ≤
            ∫⁻ x, ENNReal.ofReal Lf * (Metric.closedBall (0 : ℂ) R)ᶜ.indicator (fun _ => 1) x
              ∂gmcReferenceMeasure := lintegral_mono hhabs
        _ = ENNReal.ofReal Lf * gmcReferenceMeasure (Metric.closedBall (0 : ℂ) R)ᶜ := by
            rw [lintegral_const_mul _ (measurable_const.indicator
              Metric.isClosed_closedBall.measurableSet.compl),
              lintegral_indicator_const Metric.isClosed_closedBall.measurableSet.compl, one_mul]
        _ ≤ ENNReal.ofReal (ε / 5) := hn.le
    -- the uniform cutoff convergence of the compact part
    have hT1 := DOZZ.Proofs.equatorGFF_GMC_uniform_L1 P X hX Xc hXc Mfam hMfam I hI hI2
      (Metric.closedBall (0 : ℂ) (R + 1)) (isCompact_closedBall _ _) Lf
    obtain ⟨r₀, hr₀⟩ := (eventually_atTop.mp (hT1.eventually (gt_mem_nhds hε5)))
    set r : ℝ := max r₀ 0 with hrdef
    have hrbound := hr₀ r (le_max_left _ _)
    have hT1γ (γ : ℝ) (hγ : γ ∈ I) : ∫⁻ ω, ENNReal.ofReal |∫ x, g x ∂regularizedGMC P Xc γ r ω -
        ∫ x, g x ∂Mfam γ ω| ∂P ≤ ENNReal.ofReal (ε / 5) := by
      refine le_trans ?_ hrbound.le
      refine le_trans ?_ (le_iSup₂ (f := fun γ (_ : γ ∈ I) => ⨆ (f : ℂ → ℝ) (_ : Measurable f)
        (_ : ∀ x, |f x| ≤ Lf) (_ : ∀ x ∉ Metric.closedBall (0 : ℂ) (R + 1), f x = 0),
        ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P)
        γ hγ)
      exact le_iSup_of_le g (le_iSup_of_le hgm (le_iSup_of_le hgL (le_iSup_of_le hgK le_rfl)))
    -- continuity at the fixed cutoff
    have hcont := admissibleCutoffIntegral_L1_continuous_in_charge P Set.univ circleDensity 1 _
      (circleRegularization_admissible P X hX Xc hXc) (Metric.closedBall (0 : ℂ) (R + 1))
      (isCompact_closedBall _ _) (Set.subset_univ _) r
      (Real.exp_le_one_iff.mpr (by linarith [le_max_right r₀ 0])) Lf g hgm hgL hgK γ₀
    have hcontev := hcont.eventually (gt_mem_nhds hε5)
    have hIoo : ∀ᶠ γ in 𝓝 γ₀, γ ∈ Ioo (0 : ℝ) 2 := Ioo_mem_nhds hγ₀.1 hγ₀.2
    filter_upwards [hInhds, hIoo, hcontev] with γ hγI hγ hγcont
    have hγ₀I : γ₀ ∈ I := ⟨by linarith, by linarith⟩
    -- assemble the five terms
    have hAE (γ' : ℝ) (hγ' : γ' ∈ Ioo (0 : ℝ) 2) (φ : ℂ → ℝ) (hφ : Measurable φ) (C : ℝ)
        (hC : ∀ x, |φ x| ≤ C) : AEMeasurable (fun ω => ∫ x, φ x ∂Mfam γ' ω) P :=
      isGMCOf_integral_aemeasurable P X hX γ' hγ'.1 hγ'.2 (Mfam γ') (hMfam γ' hγ') φ hφ C hC
    have hcutm (γ' : ℝ) : Measurable (fun ω => ∫ x, g x ∂regularizedGMC P Xc γ' r ω) :=
      regularizedGMC_integral_measurable P X hX Xc hXc γ' r g hgm
    have hhL (x : ℂ) : |h x| ≤ Lf := by
      simp only [h, abs_mul]
      have h1 : |1 - ballCutoff R x| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [ballCutoff_nonneg R x, ballCutoff_le_one R x]
      calc |f x| * |1 - ballCutoff R x| ≤ Lf * 1 := mul_le_mul (hfL x) h1 (abs_nonneg _) hLf
        _ = Lf := mul_one _
    have hsplit (γ' : ℝ) (hγ' : γ' ∈ Ioo (0 : ℝ) 2) (ω : Ω) : ∫ x, f x ∂Mfam γ' ω =
        ∫ x, g x ∂Mfam γ' ω + ∫ x, h x ∂Mfam γ' ω := by
      have : IsFiniteMeasure (Mfam γ' ω) := (hMfam γ' hγ').1 ω
      have hgi : Integrable g (Mfam γ' ω) := Integrable.of_bound hgm.aestronglyMeasurable Lf
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hgL x)
      have hhi : Integrable h (Mfam γ' ω) := Integrable.of_bound hhm.aestronglyMeasurable Lf
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hhL x)
      rw [← integral_add hgi hhi]
      congr 1
      funext x
      exact hfgh x
    have hHtail (γ' : ℝ) (hγ' : γ' ∈ Ioo (0 : ℝ) 2) :
        ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂Mfam γ' ω - ∫ x, g x ∂Mfam γ' ω| ∂P ≤
          ENNReal.ofReal (ε / 5) := by
      refine le_trans (lintegral_mono fun ω => ?_) (htailbound γ' hγ')
      rw [hsplit γ' hγ' ω, add_sub_cancel_left]
      have := ofReal_abs_integral_sub_le_lintegral (Mfam γ' ω) h (fun _ => 0) hhm
        measurable_const
      simpa using this
    have hcutγ : ∫⁻ ω, ENNReal.ofReal |∫ x, g x ∂regularizedGMC P Xc γ r ω -
        ∫ x, g x ∂regularizedGMC P Xc γ₀ r ω| ∂P ≤ ENNReal.ofReal (ε / 5) := by
      simp only [integral_regularizedGMC_eq_admissibleCutoffIntegral P X hX Xc hXc]
      exact hγcont.le
    have hAγ := hAE γ hγ f f.continuous.measurable Lf hfL
    have hGγ := hAE γ hγ g hgm Lf hgL
    have hGγ₀ := hAE γ₀ hγ₀ g hgm Lf hgL
    have hswap (U V : Ω → ℝ) : ∫⁻ ω, ENNReal.ofReal |U ω - V ω| ∂P =
        ∫⁻ ω, ENNReal.ofReal |V ω - U ω| ∂P := by
      congr 1
      funext ω
      rw [abs_sub_comm]
    have hstep4 : ∫⁻ ω, ENNReal.ofReal |∫ x, g x ∂regularizedGMC P Xc γ₀ r ω -
        ∫ x, f x ∂Mfam γ₀ ω| ∂P ≤ ENNReal.ofReal (ε / 5) + ENNReal.ofReal (ε / 5) := by
      refine (lintegral_ofReal_abs_sub_le_add P _ (fun ω => ∫ x, g x ∂Mfam γ₀ ω) _
        (hcutm γ₀).aemeasurable hGγ₀).trans (add_le_add (hT1γ γ₀ hγ₀I) ?_)
      rw [hswap]
      exact hHtail γ₀ hγ₀
    have hstep3 : ∫⁻ ω, ENNReal.ofReal |∫ x, g x ∂regularizedGMC P Xc γ r ω -
        ∫ x, f x ∂Mfam γ₀ ω| ∂P ≤
        ENNReal.ofReal (ε / 5) + (ENNReal.ofReal (ε / 5) + ENNReal.ofReal (ε / 5)) :=
      (lintegral_ofReal_abs_sub_le_add P _ (fun ω => ∫ x, g x ∂regularizedGMC P Xc γ₀ r ω) _
        (hcutm γ).aemeasurable (hcutm γ₀).aemeasurable).trans (add_le_add hcutγ hstep4)
    have hstep2 : ∫⁻ ω, ENNReal.ofReal |∫ x, g x ∂Mfam γ ω - ∫ x, f x ∂Mfam γ₀ ω| ∂P ≤
        ENNReal.ofReal (ε / 5) + (ENNReal.ofReal (ε / 5) +
          (ENNReal.ofReal (ε / 5) + ENNReal.ofReal (ε / 5))) := by
      refine (lintegral_ofReal_abs_sub_le_add P _ (fun ω => ∫ x, g x ∂regularizedGMC P Xc γ r ω)
        _ hGγ (hcutm γ).aemeasurable).trans (add_le_add ?_ hstep3)
      rw [hswap]
      exact hT1γ γ hγI
    calc ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂Mfam γ ω - ∫ x, f x ∂Mfam γ₀ ω| ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂Mfam γ ω - ∫ x, g x ∂Mfam γ ω| ∂P +
          ∫⁻ ω, ENNReal.ofReal |∫ x, g x ∂Mfam γ ω - ∫ x, f x ∂Mfam γ₀ ω| ∂P :=
          lintegral_ofReal_abs_sub_le_add P _ _ _ hAγ hGγ
      _ ≤ ENNReal.ofReal (ε / 5) + (ENNReal.ofReal (ε / 5) +
          (ENNReal.ofReal (ε / 5) + (ENNReal.ofReal (ε / 5) + ENNReal.ofReal (ε / 5)))) :=
          add_le_add (hHtail γ hγ) hstep2
      _ = ENNReal.ofReal ε := by
          simp only [← ENNReal.ofReal_add (by positivity : (0 : ℝ) ≤ ε / 5)
            (by positivity : (0 : ℝ) ≤ ε / 5)]
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  by_cases hεtop : ε = ⊤
  · exact Eventually.of_forall fun _ => hεtop ▸ le_top
  · have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
    filter_upwards [hmain ε.toReal hεr] with γ hγ
    rwa [ENNReal.ofReal_toReal hεtop] at hγ

end DOZZ.Proofs
