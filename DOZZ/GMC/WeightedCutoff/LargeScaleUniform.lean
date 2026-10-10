module

public import DOZZ.GMC.WeightedCutoff.SmallScaleUniform

/-! # Uniform moments on larger finite-chart balls -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem regularizedGMC_openBall_moment_compact_gamma_large_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (p : ℝ) (hp : 1 < p) (hpcrit : ∀ γ ∈ Γ, p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ (z : ℂ) (R δ : ℝ),
      1 / 8 ≤ R → R ≤ 1 / 2 → 0 < δ → δ ≤ R → ‖z‖ + 2 * R ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
        (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) p ∂P) ≤ C := by
  classical
  rcases Set.eq_empty_or_nonempty Γ with hEmpty | hNonempty
  · refine ⟨0, by simp, ?_⟩
    simp [hEmpty]
  obtain ⟨g, hg, hmax⟩ := hΓ.exists_isMaxOn hNonempty continuousOn_id
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
  obtain ⟨A, hA, hsmall⟩ := regularizedGMC_openBall_root_bound_compact_gamma_small_chart
    P X hX Xc hXc Γ hΓ hΓpos p hp hpcrit
  let Hcover : ℝ≥0∞ := A ^ p
  have hHcover : Hcover < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) hA.ne)
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
      (Real.exp (g ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder 1)))
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
  intro γ hγ z R δ hRlo hRhi hδ hδR hchart
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
    have hγsq : γ ^ 2 ≤ g ^ 2 := by
      have hpos := hΓpos γ hγ
      have hle : γ ≤ g := hmax hγ
      exact pow_le_pow_left₀ hpos.le hle 2
    have hrem := gmcCircleChartRemainder_nonneg (R := 1) (by norm_num)
    have hTpos : 0 ≤ T := Real.log_nonneg (by norm_num)
    have hexp : γ ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder 1) ≤
        g ^ 2 * (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder 1) := by
      have hcoef : 0 ≤ (p ^ 2 - p) / 2 * (T + gmcCircleChartRemainder 1) :=
        mul_nonneg
          (by linarith only [mul_nonneg (by linarith only [hp] : (0 : ℝ) ≤ p) (sub_nonneg.2 hp.le)])
          (add_nonneg hTpos hrem)
      linarith only [mul_le_mul_of_nonneg_right hγsq hcoef]
    have hcoarse' : (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ p ∂P) ≤ Ccoarse := by
      apply hcoarse.trans
      apply mul_le_mul'
      · exact hpow
      · exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
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
      have hroot := (hsmall γ hγ p hp.le le_rfl (w : ℂ) r₀ δ hr₀pos hr₀small
        hδ hδsmall (hsmallChart w)).1
      have hxi : 0 < 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
        have hγpos := hΓpos γ hγ
        have hcrit' := (lt_div_iff₀ (sq_pos_of_pos hγpos)).mp (hpcrit γ hγ)
        have hfac : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by linarith only [hcrit', sq_nonneg γ]
        linarith only [mul_pos (lt_trans zero_lt_one hp) hfac]
      have hscale : ENNReal.ofReal ((r₀ / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) ≤ 1 := by
        apply ENNReal.ofReal_le_one.mpr
        apply Real.rpow_le_one (by norm_num [r₀]) (by norm_num [r₀])
        exact (div_pos hxi (lt_trans zero_lt_one hp)).le
      have hrootA : (∫⁻ ω, (f w ω) ^ p ∂P) ^ p⁻¹ ≤ A := by
        change (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball (w : ℂ) r₀)) ^ p ∂P) ^ p⁻¹ ≤ A
        simpa only [one_div] using hroot.trans (by simpa using mul_le_mul_right hscale A)
      exact (ENNReal.rpow_inv_le_iff (lt_trans zero_lt_one hp)).mp hrootA
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

end DOZZ.Proofs
