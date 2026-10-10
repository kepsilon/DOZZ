module

public import DOZZ.GMC.WeightedCutoff.LocationTransfer

/-! # Uniform location comparison on compact parameter sets -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Moving the center to the origin costs a single finite factor on compact families.
No moment admissibility is required for this comparison. -/
theorem cutoffWeightedGmcBallMoment_translate_compact
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ z ∈ K, ∀ ρ δ : ℝ,
      0 < ρ → ρ ≤ 1 / 2 → 0 < δ → δ ≤ ρ →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z ρ δ ω ^ t.2 ∂P) ≤
        ENNReal.ofReal C *
          ∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 0 ρ δ ω ^ t.2 ∂P := by
  classical
  rcases Set.eq_empty_or_nonempty K with hKe | hKn
  · refine ⟨1, by norm_num, ?_⟩
    simp [hKe]
  rcases Set.eq_empty_or_nonempty (Γ ×ˢ T) with hUe | hUn
  · refine ⟨1, by norm_num, ?_⟩
    intro γ hγ t ht
    have : (γ, t) ∈ Γ ×ˢ T := ⟨hγ, ht⟩
    simp [hUe] at this
  obtain ⟨zmax, hzmax, hzbound⟩ := hK.exists_isMaxOn hKn continuous_norm.continuousOn
  let B : ℝ := ‖zmax‖ + 1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : 0 < 1 + B := by linarith
  let f : ℝ × (ℝ × ℝ) → ℝ := fun u =>
    Real.exp (u.1 ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + B))) / 2 *
      |u.2.2 ^ 2 - u.2.2|) * ((1 + B) ^ 4 : ℝ) ^ |u.2.2|
  have hbase : (1 + B) ^ 4 ≠ 0 := ne_of_gt (pow_pos hB1 4)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  obtain ⟨umax, humax, hmax⟩ := (hΓ.prod hT).exists_isMaxOn hUn hf.continuousOn
  have hfpos : 0 < f umax := by dsimp [f]; positivity
  refine ⟨f umax, hfpos, ?_⟩
  intro γ hγ t ht z hz ρ δ hρ hρhalf hδ hδρ
  have hzB : ‖z‖ + ρ ≤ B := by
    have hn : ‖z‖ ≤ ‖zmax‖ := hzbound hz
    dsimp [B]
    linarith
  have hzeroB : ‖(0 : ℂ)‖ + ρ ≤ B := by
    simp only [norm_zero, zero_add]
    dsimp [B]
    linarith [norm_nonneg zmax]
  have hcmp := cutoffWeightedGmcBallMoment_translate_le P X hX Xc hXc γ t.1 t.2
    z 0 ρ B δ hρ hB hzB hzeroB hδ (by linarith)
  have hfactor :
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + B))) / 2 *
        |t.2 ^ 2 - t.2|)) * ENNReal.ofReal ((1 + B) ^ 4) ^ |t.2| =
      ENNReal.ofReal (f (γ, t)) := by
    rw [ENNReal.ofReal_rpow_of_pos (pow_pos hB1 4),
      ← ENNReal.ofReal_mul (Real.exp_nonneg _)]
  rw [hfactor] at hcmp
  apply hcmp.trans
  apply mul_le_mul_left
  exact ENNReal.ofReal_le_ofReal (hmax ⟨hγ, ht⟩)

end DOZZ.Proofs
