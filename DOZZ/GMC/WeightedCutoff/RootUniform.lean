module

public import DOZZ.GMC.WeightedCutoff.LargeScaleUniform

/-! # Uniform root estimates through the whole finite chart -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem regularizedGMC_openBall_root_bound_compact_gamma_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (q : ℝ) (hq : 1 < q) (hcrit : ∀ γ ∈ Γ, q < 4 / γ ^ 2) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ γ ∈ Γ, ∀ p : ℝ, 1 ≤ p → p ≤ q →
      ∀ (z : ℂ) (R δ : ℝ), 0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R →
      ‖z‖ + 2 * R ≤ 1 →
      ((∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ p ∂P) ^
        (1 / p) ≤ A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
          ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p))) ∧
      (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ p ∂P) < ⊤ := by
  let _ := hX.1
  obtain ⟨Asmall, hAsmall, hsmall⟩ := regularizedGMC_openBall_root_bound_compact_gamma_small_chart
    P X hX Xc hXc Γ hΓ hΓpos q hq hcrit
  obtain ⟨D, hD, hlarge⟩ := regularizedGMC_openBall_moment_compact_gamma_large_chart
    P X hX Xc hXc Γ hΓ hΓpos q hq hcrit
  let B : ℝ≥0∞ := 1 + D
  have hB : B < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hD⟩
  have hBone : 1 ≤ B := le_add_of_nonneg_right (by positivity)
  let A : ℝ≥0∞ := Asmall + B
  have hA : A < ⊤ := ENNReal.add_lt_top.mpr ⟨hAsmall, hB⟩
  refine ⟨A, hA, ?_⟩
  intro γ hγ p hp hpq z R δ hR hRhalf hδ hδR hchart
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hRsmall : R ≤ 1 / 8
  · obtain ⟨hs, htop⟩ := hsmall γ hγ p hp hpq z R δ hR hRsmall hδ hδR hchart
    refine ⟨hs.trans ?_, htop⟩
    apply mul_le_mul_left
    exact le_add_of_nonneg_right (by positivity)
  have hRlo : 1 / 8 ≤ R := le_of_not_ge hRsmall
  let f : Ω → ℝ≥0∞ := fun ω =>
    regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)
  have hf : AEMeasurable f P := regularizedGMC_mass_aemeasurable P X hX Xc hXc γ
    (Real.log (1 / δ)) (Metric.ball z R) Metric.isOpen_ball.measurableSet
  have hqbound := hlarge γ hγ z R δ hRlo hRhalf hδ hδR hchart
  have hmoment : (∫⁻ ω, f ω ^ p ∂P) ≤ B := by
    calc
      _ ≤ P Set.univ + ∫⁻ ω, f ω ^ q ∂P :=
        lintegral_rpow_le_measure_add_larger_order P f hf hp0.le hpq
      _ ≤ B := by
        rw [hX.1.measure_univ]
        simpa [B, f, add_comm] using add_le_add_left hqbound 1
  have hroot : (∫⁻ ω, f ω ^ p ∂P) ^ (1 / p) ≤ B := by
    calc
      _ ≤ B ^ (1 / p) := ENNReal.rpow_le_rpow hmoment (by positivity)
      _ ≤ B ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hBone
        ((div_le_iff₀ hp0).mpr (by simpa using hp))
      _ = B := ENNReal.rpow_one B
  have hγpos := hΓpos γ hγ
  have hcritp : γ ^ 2 * p < 4 := by
    have hcritq := (lt_div_iff₀ (sq_pos_of_pos hγpos)).mp (hcrit γ hγ)
    nlinarith [mul_le_mul_of_nonneg_left hpq (sq_nonneg γ)]
  have hxi : 0 < 2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 := by
    have hfac : 0 < 2 + γ ^ 2 / 2 - γ ^ 2 * p / 2 := by nlinarith
    nlinarith [mul_pos hp0 hfac]
  have hscale : 1 ≤ ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^
      ((2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2) / p)) := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.one_le_rpow (by linarith : 1 ≤ R / (1 / 8 : ℝ))
    exact (div_pos hxi hp0).le
  refine ⟨?_, hmoment.trans_lt hB⟩
  calc
    _ ≤ B := hroot
    _ ≤ A := le_add_of_nonneg_left (by positivity)
    _ ≤ A * _ := by simpa using mul_le_mul_right hscale A

end DOZZ.Proofs
