module

public import DOZZ.GMC.WeightedCutoff.ChartUniform
public import DOZZ.GMC.WeightedCutoff.CompactLocation

/-! # The weighted cutoff bound at small radii and arbitrary compact centers -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMoment_compact_gamma_small_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ z ∈ K, ∀ R δ : ℝ,
      0 < R → R ≤ 1 / 2 → 0 < δ → δ ≤ R →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤
        ENNReal.ofReal (C * R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
  obtain ⟨A, hA, hmove⟩ := cutoffWeightedGmcBallMoment_translate_compact
    P X hX Xc hXc Γ hΓ T hT K hK
  obtain ⟨D, hD, hchart⟩ := cutoffWeightedGmcBallMoment_compact_gamma_chart
    P X hX Xc hXc Γ hΓ hΓ2 T hT hTadm
  let E : ℝ≥0∞ := ENNReal.ofReal A * D
  have hE : E < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD
  let C : ℝ := E.toReal + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hEC : E ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hE.ne]
    apply ENNReal.ofReal_le_ofReal
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro γ hγ t ht z hz R δ hR hRhalf hδ hδR
  have hfirst := hmove γ hγ t ht z hz R δ hR hRhalf hδ hδR
  have hsecond := hchart γ hγ t ht 0 R δ hR hRhalf (by simp; linarith) hδ hδR
  calc
    _ ≤ ENNReal.ofReal A * _ := hfirst
    _ ≤ ENNReal.ofReal A * (D * _) := mul_le_mul_right hsecond _
    _ = E * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) :=
      (mul_assoc _ _ _).symm
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) :=
      mul_le_mul_left hEC _
    _ = _ := (ENNReal.ofReal_mul hC.le).symm

end DOZZ.Proofs
