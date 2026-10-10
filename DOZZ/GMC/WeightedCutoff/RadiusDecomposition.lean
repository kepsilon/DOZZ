module

public import DOZZ.GMC.WeightedCutoff.CompactCoefficients

/-! # Separating a bounded singular core from the outer part of a cutoff mass -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMass_le_inner_add_outer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (γ α a r₀ W B R δ : ℝ) (z : ℂ)
    (hR : a ≤ R) (hR₀ : R ≤ r₀) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hz : ‖z‖ + R ≤ B)
    (hW : ∀ s ∈ Set.Icc a (2 * r₀), s ^ (-γ * α) ≤ W) (ω : Ω) :
    cutoffWeightedGmcBallMass P Xc γ α z R δ ω ≤
      cutoffWeightedGmcBallMass P Xc γ α z a δ ω +
        ENNReal.ofReal W * regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball 0 B) := by
  have _ := hR
  let μ := regularizedGMC P Xc γ (Real.log (1 / δ)) ω
  let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α))
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hi : Measurable ((Metric.ball z a).indicator w) :=
    hw.indicator Metric.isOpen_ball.measurableSet
  have hball : Metric.ball z R ⊆ Metric.ball (0 : ℂ) B := by
    intro x hx
    have hx' : ‖x - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hn := norm_add_le (x - z) z
    rw [sub_add_cancel] at hn
    simpa using lt_of_le_of_lt hn (by linarith)
  change (∫⁻ x in Metric.ball z R, w x ∂μ) ≤ _
  calc
    _ ≤ ∫⁻ x in Metric.ball z R, (Metric.ball z a).indicator w x + ENNReal.ofReal W ∂μ := by
      apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
      intro x hx
      by_cases hxa : x ∈ Metric.ball z a
      · simp only [Set.indicator_of_mem hxa]
        exact le_add_of_nonneg_right (by positivity)
      · have hx' : ‖x - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hx
        have hxa' : a ≤ ‖x - z‖ := by simpa [Metric.mem_ball, dist_eq_norm] using hxa
        simp only [Set.indicator_of_notMem hxa, zero_add]
        exact ENNReal.ofReal_le_ofReal (hW (‖x - z‖ + δ) ⟨by linarith, by linarith⟩)
    _ = (∫⁻ x in Metric.ball z R, (Metric.ball z a).indicator w x ∂μ) +
        ENNReal.ofReal W * μ (Metric.ball z R) := by
      rw [lintegral_add_left hi, lintegral_const, Measure.restrict_apply_univ]
    _ ≤ (∫⁻ x, (Metric.ball z a).indicator w x ∂μ) +
        ENNReal.ofReal W * μ (Metric.ball 0 B) :=
      add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
        (mul_le_mul_right (measure_mono hball) _)
    _ = _ := by rw [lintegral_indicator Metric.isOpen_ball.measurableSet]; rfl

theorem cutoffWeightedGmcBallMass_le_coarse_weight
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (γ α a r₀ W B R δ : ℝ) (z : ℂ)
    (hR₀ : R ≤ r₀) (hδa : a ≤ δ) (hδR : δ ≤ R) (hz : ‖z‖ + R ≤ B)
    (hW : ∀ s ∈ Set.Icc a (2 * r₀), s ^ (-γ * α) ≤ W) (ω : Ω) :
    cutoffWeightedGmcBallMass P Xc γ α z R δ ω ≤
      ENNReal.ofReal W * regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball 0 B) := by
  let μ := regularizedGMC P Xc γ (Real.log (1 / δ)) ω
  have hball : Metric.ball z R ⊆ Metric.ball (0 : ℂ) B := by
    intro x hx
    have hx' : ‖x - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hn := norm_add_le (x - z) z
    rw [sub_add_cancel] at hn
    simpa using lt_of_le_of_lt hn (by linarith)
  calc
    _ ≤ ∫⁻ _x in Metric.ball z R, ENNReal.ofReal W ∂μ := by
      apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
      intro x hx
      have hx' : ‖x - z‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hx
      exact ENNReal.ofReal_le_ofReal (hW (‖x - z‖ + δ)
        ⟨by linarith [norm_nonneg (x - z)], by linarith⟩)
    _ = ENNReal.ofReal W * μ (Metric.ball z R) := by
      rw [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ _ := mul_le_mul_right (measure_mono hball) _

theorem ennreal_rpow_add_le_uniform_order_cap (a b : ℝ≥0∞) (p q : ℝ)
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    (a + b) ^ p ≤ (2 : ℝ≥0∞) ^ q * (a ^ p + b ^ p) := by
  have htwo : (2 : ℝ≥0∞) ^ p ≤ 2 ^ q :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hpq
  rcases le_total a b with hab | hba
  · have hadd : a + b ≤ 2 * b := by simpa [two_mul, add_comm] using add_le_add_right hab b
    calc
      _ ≤ (2 * b) ^ p := ENNReal.rpow_le_rpow hadd hp
      _ = 2 ^ p * b ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp
      _ ≤ _ := mul_le_mul' htwo (le_add_of_nonneg_left (by positivity))
  · have hadd : a + b ≤ 2 * a := by simpa [two_mul, add_comm] using add_le_add_left hba a
    calc
      _ ≤ (2 * a) ^ p := ENNReal.rpow_le_rpow hadd hp
      _ = 2 ^ p * a ^ p := ENNReal.mul_rpow_of_nonneg _ _ hp
      _ ≤ _ := mul_le_mul' htwo (le_add_of_nonneg_right (by positivity))

end DOZZ.Proofs
