module

public import DOZZ.GMC.WeightedCutoff.ConvexGamma

/-! # Uniform reference moments at all nonnegative cutoff times -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem regularizedGMC_reference_positive_moment_compact_gamma_all_cutoffs
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (p : ℝ) (hp : 1 < p) (hcrit : ∀ γ ∈ Γ, p < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ r : ℝ, 0 ≤ r →
      (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ p ∂P) ≤ C := by
  classical
  rcases Set.eq_empty_or_nonempty Γ with hEmpty | hNonempty
  · refine ⟨0, by simp, ?_⟩
    simp [hEmpty]
  obtain ⟨g, hg, hmax⟩ := hΓ.exists_isMaxOn hNonempty continuousOn_id
  obtain ⟨D, hD, hfine⟩ := regularizedGMC_reference_positive_moment_compact_gamma
    P X hX Xc hXc Γ hΓ hΓpos p hp hcrit
  let A : ℝ := (p ^ 2 - p) / 2 * (1 + gmcCircleChartRemainder 1)
  have hA : 0 ≤ A := by
    have hrem := gmcCircleChartRemainder_nonneg (R := 1) (by norm_num)
    dsimp [A]
    exact mul_nonneg (by nlinarith) (by linarith)
  let E : ℝ≥0∞ := gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 8)) ^ p *
    ENNReal.ofReal (Real.exp (g ^ 2 * A))
  have htop : gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 8)) ≠ ⊤ :=
    ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
  have hE : E < ⊤ := by
    exact ENNReal.mul_lt_top
      (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) htop))
      ENNReal.ofReal_lt_top
  refine ⟨D + E, ENNReal.add_lt_top.mpr ⟨hD, hE⟩, ?_⟩
  intro γ hγ r hr
  by_cases hr1 : 1 ≤ r
  · exact (hfine γ hγ r hr1).trans (le_add_of_nonneg_right (by positivity))
  have hcoarse := regularizedGMC_coarse_chart_moment_upper P X hX Xc hXc γ 1 1 p
    (by norm_num) hp.le (Metric.ball 0 (1 / 8)) Metric.isOpen_ball.measurableSet
    (by
      intro x hx
      have hx' : ‖x‖ < 1 / 8 := by simpa using hx
      linarith)
    r hr (le_of_not_ge hr1)
  have hγsq : γ ^ 2 ≤ g ^ 2 := by
    have hγpos := hΓpos γ hγ
    have hγg : γ ≤ g := hmax hγ
    nlinarith
  have hexp : γ ^ 2 * (p ^ 2 - p) / 2 * (1 + gmcCircleChartRemainder 1) ≤ g ^ 2 * A := by
    calc
      _ = γ ^ 2 * A := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hγsq hA
  have hcoarseE : (∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ p ∂P) ≤ E := by
    apply hcoarse.trans
    apply mul_le_mul_right
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexp)
  exact hcoarseE.trans (le_add_of_nonneg_left (by positivity))

/-- Lower nonnegative moments are bounded by the mass of the probability space plus a higher moment. -/
theorem lintegral_rpow_le_measure_add_larger_order
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

end DOZZ.Proofs
