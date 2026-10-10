/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Annulus.HigherScales
public import DOZZ.GMC.Moments.WeightedCutoffBallMomentUpToTwo
public import DOZZ.GMC.Moments.WeightedCutoffCompactSlack

/-! All-order cutoff estimates on the logarithmic chart, using the preceding-order induction. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

private theorem lintegral_rpow_le_measure_add_higher_order_all_orders
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → ℝ≥0∞)
    (hf : AEMeasurable f P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    (∫⁻ ω, ENNReal.rpow (f ω) p ∂P) ≤
      P Set.univ + ∫⁻ ω, ENNReal.rpow (f ω) q ∂P := by
  have hqmeas : AEMeasurable (fun ω => ENNReal.rpow (f ω) q) P := by
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf
  have hpoint (ω : Ω) : ENNReal.rpow (f ω) p ≤ 1 + ENNReal.rpow (f ω) q := by
    by_cases hω : f ω ≤ 1
    · exact (ENNReal.rpow_le_one hω hp).trans (le_add_of_nonneg_right (by positivity))
    · have hω' : 1 ≤ f ω := le_of_not_ge hω
      calc
        ENNReal.rpow (f ω) p ≤ ENNReal.rpow (f ω) q :=
          ENNReal.rpow_le_rpow_of_exponent_le hω' hpq
        _ ≤ 1 + ENNReal.rpow (f ω) q := le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ ∫⁻ ω, 1 + ENNReal.rpow (f ω) q ∂P := lintegral_mono hpoint
    _ = P Set.univ + ∫⁻ ω, ENNReal.rpow (f ω) q ∂P := by
      rw [lintegral_add_left' (aemeasurable_const :
        AEMeasurable (fun _ : Ω => (1 : ℝ≥0∞)) P), lintegral_const]
      simp

/-- The higher-order induction gives a uniform cutoff moment on every sufficiently small
chart-contained ball, with its exact scale exponent. -/
theorem regularizedGMC_openBall_moment_bound_all_orders_uniform_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hpcrit : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 8 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ≤
        C * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
  let R₀ : ℝ := 1 / 8
  have hR₀ : 0 < R₀ := by norm_num [R₀]
  have hR₀small : R₀ ≤ 1 / 8 := by norm_num [R₀]
  obtain ⟨C, hC, hbound⟩ := regularizedGMC_reference_positive_moment_uniform
    P X hX Xc hXc γ p hγ hp hpcrit hR₀ hR₀small
  refine ⟨C, hC, ?_⟩
  intro z R δ hR hRsmall hδ hδR hchart
  let t : ℝ := Real.log (1 / δ)
  have hR₀one : R₀ < 1 := by norm_num [R₀]
  have hδeq : Real.exp (-t) = δ := by
    dsimp [t]
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hratio : δ * (R₀ / R) ≤ R₀ := by
    have hmul := mul_le_mul_of_nonneg_right hδR (div_nonneg (le_of_lt hR₀) hR.le)
    calc
      δ * (R₀ / R) ≤ R * (R₀ / R) := hmul
      _ = R₀ := by field_simp [ne_of_gt hR]
  have hbase : R₀ + Real.exp (-t) * (R₀ / R) ≤ 1 := by
    rw [hδeq]
    calc
      R₀ + δ * (R₀ / R) ≤ R₀ + R₀ := by
        simpa [add_comm] using add_le_add_left hratio R₀
      _ ≤ 1 := by norm_num [R₀]
  have htarget : ‖z‖ + R + Real.exp (-t) ≤ 1 := by
    rw [hδeq]
    linarith [hchart, hδR]
  have htbase : 0 ≤ t + Real.log (R / R₀) := by
    have hquot : 1 ≤ R / (δ * R₀) := by
      apply (le_div_iff₀ (mul_pos hδ hR₀)).2
      have hδR₀ : δ * R₀ ≤ R * R₀ :=
        mul_le_mul_of_nonneg_right hδR (le_of_lt hR₀)
      have hR₀le : R * R₀ ≤ R := mul_le_of_le_one_right hR.le hR₀one.le
      simpa using hδR₀.trans hR₀le
    have hlog : 0 ≤ Real.log (R / (δ * R₀)) := Real.log_nonneg hquot
    have hlogmul : Real.log (R / (δ * R₀)) = t + Real.log (R / R₀) := by
      have hmul : (1 / δ) * (R / R₀) = R / (δ * R₀) := by
        field_simp [ne_of_gt hδ, ne_of_gt hR₀]
      rw [← hmul, Real.log_mul (by positivity) (by positivity)]
    rw [← hlogmul]
    exact hlog
  have hscale := regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z
    (s := R) (R := R₀) (t := t) hR hRsmall hR₀ hR₀one
    (by linarith [hchart]) hbase htarget p
  have hbaseBound := hbound (t + Real.log (R / R₀)) htbase
  change gmcMassMoment P (regularizedGMC P Xc γ (Real.log (1 / δ)))
    (Metric.ball z R) p ≤ _
  rw [hscale]
  calc
    _ ≤ ENNReal.ofReal ((R / R₀) ^
          (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) * C :=
      mul_le_mul' le_rfl hbaseBound
    _ = _ := by rw [mul_comm]

/-- For larger chart balls, a finite spatial cover reduces fine cutoffs to the small-ball
estimate; coarse cutoffs use the Gaussian convexity estimate. -/
theorem regularizedGMC_openBall_moment_bound_all_orders_large_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hpcrit : p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      1 / 8 ≤ R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ≤ C := by
  classical
  let r₀ : ℝ := 1 / 32
  let K : Set ℂ := Metric.closedBall 0 (7 / 8 : ℝ)
  let U : Type := {w : ℂ // w ∈ K}
  obtain ⟨S, hcover⟩ := (isCompact_closedBall (0 : ℂ) (7 / 8 : ℝ)).elim_finite_subcover
    (fun w : U => Metric.ball (w : ℂ) r₀) (fun _ => Metric.isOpen_ball)
    (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (by norm_num [r₀])⟩)
  have hSne : S.Nonempty := by
    have hzero : (0 : ℂ) ∈ K := by simp [K]; positivity
    have hc := hcover hzero
    simp only [Set.mem_iUnion] at hc
    obtain ⟨w, hwS, _⟩ := hc
    exact ⟨w, hwS⟩
  have hr₀pos : 0 < r₀ := by norm_num [r₀]
  have hr₀small : r₀ ≤ 1 / 8 := by norm_num [r₀]
  have hsmallChart : ∀ w : U, ‖(w : ℂ)‖ + 2 * r₀ ≤ 1 := by
    intro w
    have hw : ‖(w : ℂ)‖ ≤ 7 / 8 := by
      have hwmem : (w : ℂ) ∈ Metric.closedBall 0 (7 / 8 : ℝ) := w.property
      simpa only [Metric.mem_closedBall, dist_zero_right] using hwmem
    norm_num [r₀] at hw ⊢
    linarith
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    regularizedGMC_openBall_moment_bound_all_orders_uniform_chart
      P X hX Xc hXc γ p hγ hp hpcrit
  let Hcover : ℝ≥0∞ := Csmall * ENNReal.ofReal
    ((r₀ / (1 / 8 : ℝ)) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2))
  have hHcover : Hcover < ⊤ := by
    dsimp [Hcover]
    exact ENNReal.mul_lt_top hCsmall ENNReal.ofReal_lt_top
  let Ccover : ℝ≥0∞ := (S.card : ℝ≥0∞) ^ p * (S.card : ℝ≥0∞) * Hcover
  have hCcover : Ccover < ⊤ := by
    dsimp [Ccover]
    have hcardpow : (S.card : ℝ≥0∞) ^ p < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        (ENNReal.natCast_ne_top S.card))
    have hcard : (S.card : ℝ≥0∞) < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top S.card)
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hcardpow hcard) hHcover
  let T : ℝ := Real.log 32
  let Ccoarse : ℝ≥0∞ :=
    (gmcReferenceMeasure Set.univ) ^ p * ENNReal.ofReal
      (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder 1)))
  have hCcoarse : Ccoarse < ⊤ := by
    dsimp [Ccoarse]
    have hrefpow : (gmcReferenceMeasure Set.univ) ^ p < ⊤ :=
      lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        gmcReferenceMeasure_univ_ne_top)
    exact ENNReal.mul_lt_top hrefpow ENNReal.ofReal_lt_top
  let C : ℝ≥0∞ := Ccover + Ccoarse
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.add_lt_top.mpr ⟨hCcover, hCcoarse⟩
  refine ⟨C, hC, ?_⟩
  intro z R δ hRlo hRhi hδ hδR hchart
  let t : ℝ := Real.log (1 / δ)
  have ht0 : 0 ≤ t := by
    dsimp [t]
    apply Real.log_nonneg
    have hδhalf : δ ≤ 1 / 2 := hδR.trans hRhi
    exact (one_le_div₀ hδ).2 (by linarith)
  by_cases hδcoarse : 1 / 32 < δ
  · have hδupper : 1 / δ ≤ 32 := by
      apply (div_le_iff₀ hδ).2
      linarith
    have htT : t ≤ T := by
      dsimp [t, T]
      exact Real.log_le_log (one_div_pos.mpr hδ) hδupper
    have hballChart : ∀ x ∈ Metric.ball z R, ‖x‖ ≤ 1 := by
      intro x hx
      have hdist : ‖x - z‖ < R := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hnorm : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        calc
          ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
          _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖x - z‖ := by ring
      have hzR : ‖z‖ + R ≤ 1 := by linarith [hchart]
      exact le_trans hnorm (by linarith)
    have hcoarse := regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ 1 T p
      (by norm_num) (by linarith) (Metric.ball z R) Metric.isOpen_ball.measurableSet
      hballChart t ht0 htT
    have hmeasure : gmcReferenceMeasure (Metric.ball z R) ≤ gmcReferenceMeasure Set.univ :=
      measure_mono (Set.subset_univ _)
    have hpow := ENNReal.rpow_le_rpow hmeasure (by linarith : 0 ≤ p)
    dsimp [t, Ccoarse] at hcoarse ⊢
    have hcoarse' := hcoarse.trans (mul_le_mul_of_nonneg_right hpow (by positivity))
    dsimp [C]
    exact hcoarse'.trans (le_add_of_nonneg_left (by positivity))
  · have hδsmall : δ ≤ r₀ := by
      dsimp [r₀]
      linarith
    have htargetDisk : Metric.ball z R ⊆ K := by
      intro x hx
      have hdist : ‖x - z‖ < R := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hx
      have hnorm : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        calc
          ‖x‖ = ‖(x - z) + z‖ := by congr 1; abel
          _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖x - z‖ := by ring
      have hRnorm : ‖z‖ + R ≤ 7 / 8 := by
        have : 1 / 8 ≤ R := hRlo
        linarith [hchart]
      have hxnorm : ‖x‖ ≤ 7 / 8 := le_trans hnorm (by linarith)
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hxnorm
    let μ : Ω → Measure ℂ := regularizedGMC P Xc γ t
    let f : U → Ω → ℝ≥0∞ := fun w ω => μ ω (Metric.ball (w : ℂ) r₀)
    have hmass : ∀ ω, μ ω (Metric.ball z R) ≤ ∑ w ∈ S, f w ω := by
      intro ω
      calc
        μ ω (Metric.ball z R) ≤ μ ω (⋃ w ∈ S, Metric.ball (w : ℂ) r₀) := by
          apply measure_mono
          exact htargetDisk.trans hcover
        _ ≤ ∑ w ∈ S, μ ω (Metric.ball (w : ℂ) r₀) := measure_biUnion_finset_le _ _
    have hmeas (w : U) : AEMeasurable (fun ω => (f w ω) ^ p) P := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        ((regularizedGMC_mass_aemeasurable P X hX Xc hXc γ t
          (Metric.ball (w : ℂ) r₀) Metric.isOpen_ball.measurableSet))
    have hlocal (w : U) : (∫⁻ ω, (f w ω) ^ p ∂P) ≤ Hcover := by
      dsimp [f, μ, Hcover]
      have hwchart := hsmallChart w
      simpa [r₀, t] using hsmall (w : ℂ) r₀ δ hr₀pos hr₀small hδ hδsmall hwchart
    have hsumMeas : AEMeasurable (fun ω => ∑ w ∈ S, f w ω ^ p) P :=
      Finset.aemeasurable_fun_sum _ fun w hw => hmeas w
    calc
      _ ≤ ∫⁻ ω, ((S.card : ℝ≥0∞) ^ p) * ∑ w ∈ S, (f w ω) ^ p ∂P := by
        apply lintegral_mono
        intro ω
        exact (ENNReal.rpow_le_rpow (hmass ω) (by linarith)).trans
          (ennreal_finset_sum_rpow_le_card_rpow_sum S hSne (fun w => f w ω) p
            (by linarith))
      _ = (S.card : ℝ≥0∞) ^ p * ∑ w ∈ S, ∫⁻ ω, (f w ω) ^ p ∂P := by
        rw [lintegral_const_mul'' _ hsumMeas,
          lintegral_finsetSum' S (f := fun w ω => (f w ω) ^ p)
            (fun w hw => hmeas w)]
      _ ≤ (S.card : ℝ≥0∞) ^ p * ∑ _w ∈ S, Hcover := by
        gcongr
        exact hlocal _
      _ = Ccover := by simp [Ccover]; ac_rfl
      _ ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (by positivity)

/-- All strictly subcritical orders have a uniform chart-ball root estimate through radius
`1/2`. -/
theorem regularizedGMC_openBall_lp_root_bound_all_orders_uniform_chart_all_radius
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ p : ℝ) (hγ : 0 < γ) (hp : 1 < p) (hpcrit : p < 4 / γ ^ 2) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (((∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤) := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hxi : 0 < 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
    have hcrit' : γ ^ 2 * p < 4 := by
      have h := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hpcrit
      linarith only [h]
    have hfactor : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by linarith only [hcrit', sq_nonneg γ]
    linarith only [mul_pos hp0 hfactor]
  let beta : ℝ := (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p
  have hbeta : 0 < beta := div_pos hxi hp0
  obtain ⟨Csmall, hCsmall, hsmall⟩ :=
    regularizedGMC_openBall_moment_bound_all_orders_uniform_chart
      P X hX Xc hXc γ p hγ hp hpcrit
  obtain ⟨Cbig, hCbig, hbig⟩ := regularizedGMC_openBall_moment_bound_all_orders_large_chart
    P X hX Xc hXc γ p hγ hp hpcrit
  let Asmall : ℝ≥0∞ := Csmall ^ (1 / p)
  let Abig : ℝ≥0∞ := Cbig ^ (1 / p)
  have hAsmall : Asmall < ⊤ := by
    dsimp [Asmall]
    exact lt_top_iff_ne_top.mpr <| ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hp0.le) hCsmall.ne
  have hAbig : Abig < ⊤ := by
    dsimp [Abig]
    exact lt_top_iff_ne_top.mpr <| ENNReal.rpow_ne_top_of_nonneg
      (one_div_nonneg.mpr hp0.le) hCbig.ne
  let A : ℝ≥0∞ := Asmall + Abig
  have hA : A < ⊤ := by
    dsimp [A]
    exact ENNReal.add_lt_top.mpr ⟨hAsmall, hAbig⟩
  refine ⟨A, hA, ?_⟩
  intro z R δ hR hRhi hδ hδR hchart
  by_cases hRsmall : R ≤ 1 / 8
  · have hmoment := hsmall z R δ hR hRsmall hδ hδR hchart
    have hmomentTop : (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤ :=
      hmoment.trans_lt (ENNReal.mul_lt_top hCsmall ENNReal.ofReal_lt_top)
    have hrootBound :
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^ (1 / p) ≤
          Asmall * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) := by
      have hratio : 0 < R / (1 / 8 : ℝ) := div_pos hR (by norm_num)
      have hrootConst := ennreal_root_mul_ofReal_rpow_eq Csmall hCsmall
        (R / (1 / 8 : ℝ))
        (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) p hratio hp0
      calc
        _ ≤ (Csmall * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2))) ^ (1 / p) :=
          ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hp0.le)
        _ = Asmall * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) := by
          rw [hrootConst]
    have hAsmallA : Asmall ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
    refine ⟨?_, hmomentTop⟩
    calc
      _ ≤ Asmall * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) := hrootBound
      _ ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) :=
        mul_le_mul_of_nonneg_right hAsmallA (by positivity)
      _ = _ := by rfl
  · have hRlo : 1 / 8 ≤ R := le_of_not_ge hRsmall
    have hmoment := hbig z R δ hRlo hRhi hδ hδR hchart
    have hmomentTop := hmoment.trans_lt hCbig
    have hroot :
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
            (1 / p) ≤ Abig := by
      dsimp [Abig]
      exact ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hp0.le)
    have hratio : 1 ≤ R / (1 / 8 : ℝ) := (one_le_div₀ (by norm_num)).2 hRlo
    have hscale : 1 ≤ ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) :=
      ENNReal.one_le_ofReal.mpr (Real.one_le_rpow hratio hbeta.le)
    have hAbigA : Abig ≤ A := by dsimp [A]; exact le_add_of_nonneg_left (by positivity)
    refine ⟨?_, hmomentTop⟩
    calc
      _ ≤ Abig := hroot
      _ ≤ A := hAbigA
      _ = A * 1 := by simp
      _ ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta) :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ = _ := by rfl


/-- A compact family of strictly subcritical orders has one chart-ball root estimate through
radius `1/2`, uniformly over the orders and all cutoffs. -/
theorem regularizedGMC_openBall_lp_root_bound_compact_order_chart_all_orders
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (T : Set ℝ) (hT : IsCompact T)
    (hTadm : ∀ p ∈ T, 1 < p ∧ p < 4 / γ ^ 2) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ p ∈ T, ∀ (z : ℂ) (R δ : ℝ),
      0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (((∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ^
          (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
            ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
        (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) < ⊤) := by
  let _ := hX.1
  classical
  rcases Set.eq_empty_or_nonempty T with hEmpty | hNonempty
  · refine ⟨0, by simp, ?_⟩
    simp [hEmpty]
  · let orders : Set ℝ := T
    obtain ⟨q, hqmem, hqmax⟩ := hT.exists_isMaxOn hNonempty continuousOn_id
    have hqadm := hTadm q hqmem
    have hq0 : 0 < q := lt_trans zero_lt_one hqadm.1
    have hpq (p : ℝ) (hp : p ∈ T) : p ≤ q := hqmax hp
    let R₀ : ℝ := 1 / 8
    obtain ⟨Cref, hCref, hRef⟩ :=
      regularizedGMC_reference_positive_moment_uniform
        P X hX Xc hXc γ q hγ hqadm.1 hqadm.2
        (R := R₀) (by norm_num [R₀]) (by norm_num [R₀])
    obtain ⟨CbigQ, hCbigQ, hBigQ⟩ :=
      regularizedGMC_openBall_moment_bound_all_orders_large_chart
        P X hX Xc hXc γ q hγ hqadm.1 hqadm.2
    let Csmall : ℝ≥0∞ := 1 + Cref
    let Clarge : ℝ≥0∞ := 1 + CbigQ
    let A : ℝ≥0∞ := Csmall + Clarge
    have hCsmall : Csmall < ⊤ := by
      dsimp [Csmall]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hCref⟩
    have hClarge : Clarge < ⊤ := by
      dsimp [Clarge]
      exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hCbigQ⟩
    have hA : A < ⊤ := by
      dsimp [A]
      exact ENNReal.add_lt_top.mpr ⟨hCsmall, hClarge⟩
    have hCsmallOne : 1 ≤ Csmall := by
      dsimp [Csmall]
      exact le_add_of_nonneg_right (by positivity)
    have hClargeOne : 1 ≤ Clarge := by
      dsimp [Clarge]
      exact le_add_of_nonneg_right (by positivity)
    have hCsmallA : Csmall ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
    have hClargeA : Clarge ≤ A := by dsimp [A]; exact le_add_of_nonneg_left (by positivity)
    refine ⟨A, hA, ?_⟩
    intro p hp z R δ hR hRhi hδ hδR hchart
    have hpadm := hTadm p hp
    have hp0 : 0 < p := lt_trans zero_lt_one hpadm.1
    let beta : ℝ := (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p
    have hxi : 0 < 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
      have hcrit' : γ ^ 2 * p < 4 := by
        have h := (lt_div_iff₀ (sq_pos_of_pos hγ)).mp hpadm.2
        linarith only [h]
      have hfactor : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by linarith only [hcrit', sq_nonneg γ]
      linarith only [mul_pos hp0 hfactor]
    have hbeta : 0 < beta := div_pos hxi hp0
    by_cases hRsmall : R ≤ R₀
    · let t : ℝ := Real.log (1 / δ)
      have hR₀pos : 0 < R₀ := by norm_num [R₀]
      have hR₀one : R₀ < 1 := by norm_num [R₀]
      have hδeq : Real.exp (-t) = δ := by
        dsimp [t]
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp
      have hratio : δ * (R₀ / R) ≤ R₀ := by
        have hmul := mul_le_mul_of_nonneg_right hδR (div_nonneg (le_of_lt hR₀pos) hR.le)
        calc
          δ * (R₀ / R) ≤ R * (R₀ / R) := hmul
          _ = R₀ := by field_simp [ne_of_gt hR]
      have hbase : R₀ + Real.exp (-t) * (R₀ / R) ≤ 1 := by
        rw [hδeq]
        calc
          R₀ + δ * (R₀ / R) ≤ R₀ + R₀ := by
            simpa [add_comm] using add_le_add_left hratio R₀
          _ ≤ 1 := by norm_num [R₀]
      have htarget : ‖z‖ + R + Real.exp (-t) ≤ 1 := by
        rw [hδeq]
        linarith [hchart, hδR]
      have htbase : 0 ≤ t + Real.log (R / R₀) := by
        have hquot : 1 ≤ R / (δ * R₀) := by
          apply (le_div_iff₀ (mul_pos hδ hR₀pos)).2
          have hδR₀ : δ * R₀ ≤ R * R₀ :=
            mul_le_mul_of_nonneg_right hδR (le_of_lt hR₀pos)
          have hR₀le : R * R₀ ≤ R := mul_le_of_le_one_right hR.le hR₀one.le
          simpa using hδR₀.trans hR₀le
        have hlog : 0 ≤ Real.log (R / (δ * R₀)) := Real.log_nonneg hquot
        have hlogmul : Real.log (R / (δ * R₀)) = t + Real.log (R / R₀) := by
          have hmul : (1 / δ) * (R / R₀) = R / (δ * R₀) := by
            field_simp [ne_of_gt hδ, ne_of_gt hR₀pos]
          rw [← hmul, Real.log_mul (by positivity) (by positivity)]
        rw [← hlogmul]
        exact hlog
      let massQ : Ω → ℝ≥0∞ := fun ω =>
        regularizedGMC P Xc γ (t + Real.log (R / R₀)) ω (Metric.ball 0 R₀)
      have hmassQ : AEMeasurable massQ P := by
        exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
          (t + Real.log (R / R₀)) (Metric.ball 0 R₀) Metric.isOpen_ball.measurableSet
      have hqbound := hRef (t + Real.log (R / R₀)) htbase
      have hRefp : (∫⁻ ω, ENNReal.rpow (massQ ω) p ∂P) ≤ Csmall := by
        calc
          _ ≤ P Set.univ + ∫⁻ ω, ENNReal.rpow (massQ ω) q ∂P :=
            lintegral_rpow_le_measure_add_higher_order_all_orders P massQ hmassQ
              (by linarith) (hpq p hp)
          _ = 1 + gmcMassMoment P
              (regularizedGMC P Xc γ (t + Real.log (R / R₀)))
              (Metric.ball 0 R₀) q := by
            change P Set.univ + gmcMassMoment P
              (regularizedGMC P Xc γ (t + Real.log (R / R₀)))
              (Metric.ball 0 R₀) q = _
            rw [hX.1.measure_univ]
          _ ≤ Csmall := by
            dsimp [Csmall]
            simpa [add_comm] using add_le_add_left hqbound 1
      have hRefpMass : gmcMassMoment P
          (regularizedGMC P Xc γ (t + Real.log (R / R₀))) (Metric.ball 0 R₀) p ≤ Csmall := by
        simpa [gmcMassMoment, massQ] using hRefp
      have hscale := regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc z
        (s := R) (R := R₀) (t := t) hR hRsmall hR₀pos hR₀one
        (by linarith [hchart]) hbase htarget p
      have hmoment : (∫⁻ ω, ENNReal.rpow
          (regularizedGMC P Xc γ t ω (Metric.ball z R)) p ∂P) ≤
            Csmall * ENNReal.ofReal ((R / R₀) ^
              (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by
        change gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball z R) p ≤ _
        rw [hscale]
        calc
          _ = gmcMassMoment P
              (regularizedGMC P Xc γ (t + Real.log (R / R₀)))
              (Metric.ball 0 R₀) p * ENNReal.ofReal
                ((R / R₀) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) := by ac_rfl
          _ ≤ Csmall * ENNReal.ofReal
              ((R / R₀) ^ (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) :=
            mul_le_mul' hRefpMass le_rfl
      have hmomentTop := hmoment.trans_lt (ENNReal.mul_lt_top hCsmall ENNReal.ofReal_lt_top)
      have hrootConst := ennreal_root_mul_ofReal_rpow_eq Csmall hCsmall
        (R / R₀) (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) p
        (div_pos hR hR₀pos) hp0
      have hCroot : Csmall ^ (1 / p) ≤ Csmall := by
        calc
          Csmall ^ (1 / p) ≤ Csmall ^ (1 : ℝ) :=
            ENNReal.rpow_le_rpow_of_exponent_le hCsmallOne
              ((div_le_iff₀ hp0).2 (by linarith [hpadm.1]))
          _ = Csmall := by rw [ENNReal.rpow_one]
      have hroot :
          (∫⁻ ω, ENNReal.rpow
            (regularizedGMC P Xc γ t ω (Metric.ball z R)) p ∂P) ^ (1 / p) ≤
            Csmall * ENNReal.ofReal ((R / R₀) ^ beta) := by
        calc
          _ ≤ (Csmall * ENNReal.ofReal ((R / R₀) ^
              (2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2))) ^ (1 / p) :=
            ENNReal.rpow_le_rpow hmoment (one_div_nonneg.mpr hp0.le)
          _ = Csmall ^ (1 / p) * ENNReal.ofReal ((R / R₀) ^ beta) := by
            rw [hrootConst]
          _ ≤ Csmall * ENNReal.ofReal ((R / R₀) ^ beta) :=
            mul_le_mul_of_nonneg_right hCroot (by positivity)
      refine ⟨?_, hmomentTop⟩
      calc
        _ ≤ Csmall * ENNReal.ofReal ((R / R₀) ^ beta) := hroot
        _ ≤ A * ENNReal.ofReal ((R / R₀) ^ beta) :=
          mul_le_mul_of_nonneg_right hCsmallA (by positivity)
        _ = _ := by rfl
    · have hRlo : R₀ ≤ R := le_of_not_ge hRsmall
      let mass : Ω → ℝ≥0∞ := fun ω =>
        regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)
      have hR₀pos : 0 < R₀ := by norm_num [R₀]
      have hmass : AEMeasurable mass P := by
        exact regularizedGMC_mass_aemeasurable P X hX Xc hXc γ (Real.log (1 / δ))
          (Metric.ball z R) Metric.isOpen_ball.measurableSet
      have hqbound := hBigQ z R δ hRlo hRhi hδ hδR hchart
      have hmoment : (∫⁻ ω, ENNReal.rpow (mass ω) p ∂P) ≤ Clarge := by
        calc
          _ ≤ P Set.univ + ∫⁻ ω, ENNReal.rpow (mass ω) q ∂P :=
            lintegral_rpow_le_measure_add_higher_order_all_orders P mass hmass
              (by linarith) (hpq p hp)
          _ = 1 + ∫⁻ ω, ENNReal.rpow (mass ω) q ∂P := by
            rw [hX.1.measure_univ]
          _ ≤ Clarge := by
            dsimp [Clarge]
            have hqbound' : (∫⁻ ω, ENNReal.rpow (mass ω) q ∂P) ≤ CbigQ := by
              simpa [mass] using hqbound
            simpa [add_comm] using add_le_add_left hqbound' 1
      have hmomentTop := hmoment.trans_lt hClarge
      have hroot : (∫⁻ ω, ENNReal.rpow (mass ω) p ∂P) ^ (1 / p) ≤ Clarge := by
        calc
          _ ≤ Clarge ^ (1 / p) := ENNReal.rpow_le_rpow hmoment
            (one_div_nonneg.mpr hp0.le)
          _ ≤ Clarge ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hClargeOne
            ((div_le_iff₀ hp0).2 (by linarith [hpadm.1]))
          _ = Clarge := by rw [ENNReal.rpow_one]
      have hratio : 1 ≤ R / R₀ := (one_le_div₀ hR₀pos).2 hRlo
      have hscale : 1 ≤ ENNReal.ofReal ((R / R₀) ^ beta) :=
        ENNReal.one_le_ofReal.mpr (Real.one_le_rpow hratio hbeta.le)
      refine ⟨?_, hmomentTop⟩
      change (∫⁻ ω, ENNReal.rpow (mass ω) p ∂P) ^ (1 / p) ≤ _
      calc
        _ ≤ Clarge := hroot
        _ ≤ A := hClargeA
        _ = A * 1 := by simp
        _ ≤ A * ENNReal.ofReal ((R / R₀) ^ beta) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = _ := by rfl

/- Compact charge/order uniformity for the all-order chart estimate. -/

end DOZZ.Proofs
