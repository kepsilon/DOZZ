module

public import DOZZ.GMC.WeightedCutoff.PositiveCompact
public import DOZZ.GMC.WeightedCutoff.NonpositiveCompact
public import DOZZ.GMC.WeightedCutoff.OrderCap
public import DOZZ.GMC.Moments.WeightedCutoffCompactPositive

/-! # The compact finite-chart weighted cutoff bound for all positive orders -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMoment_compact_gamma_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ z : ℂ, ∀ R δ : ℝ,
      0 < R → R ≤ 1 / 2 → ‖z‖ + 2 * R ≤ 1 → 0 < δ → δ ≤ R →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤
        C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
  classical
  rcases Set.eq_empty_or_nonempty Γ with hΓe | hΓn
  · refine ⟨0, by simp, ?_⟩
    simp [hΓe]
  rcases Set.eq_empty_or_nonempty T with hTe | hTn
  · refine ⟨0, by simp, ?_⟩
    simp [hTe]
  obtain ⟨q, hq, hqcrit, hqorders⟩ := exists_weighted_cutoff_order_cap Γ hΓ hΓn hΓ2 T hT hTn
    (fun γ hγ t ht => lt_of_lt_of_le (hTadm γ hγ t ht).2 (min_le_left _ _))
  let Ts : Set (ℝ × ℝ) := T ∩ {t | t.2 ≤ 1}
  let Tp : Set (ℝ × ℝ) := T ∩ {t | 1 ≤ t.2}
  have hTs : IsCompact Ts := hT.inter_right (isClosed_Iic.preimage continuous_snd)
  have hTp : IsCompact Tp := hT.inter_right (isClosed_Ici.preimage continuous_snd)
  have hsadm : ∀ γ ∈ Γ, ∀ t ∈ Ts, 0 < t.2 ∧ t.2 ≤ 1 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)) := by
    intro γ hγ t ht
    exact ⟨(hTadm γ hγ t ht.1).1, ht.2, (hTadm γ hγ t ht.1).2⟩
  have hpadm : ∀ γ ∈ Γ, ∀ t ∈ Tp, 1 ≤ t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)) := by
    intro γ hγ t ht
    exact ⟨ht.2, (hTadm γ hγ t ht.1).2⟩
  obtain ⟨Cs, hCs, hs⟩ := cutoffWeightedGmcBallMoment_subunit_compact_gamma_parameters_chart
    P X hX Γ hΓ hΓ2 Xc hXc Ts hTs hsadm
  obtain ⟨Cp, hCp, hpos⟩ := cutoffWeightedGmcBallMoment_positive_compact_gamma_chart
    P X hX Xc hXc Γ hΓ hΓ2 Tp hTp hpadm q hq hqcrit (fun t ht => hqorders t ht.1)
  obtain ⟨Cn, hCn, hnonpos⟩ := cutoffWeightedGmcBallMoment_nonpos_compact_gamma_chart
    P X hX Xc hXc Γ hΓ (fun γ hγ => (hΓ2 hγ).1) Tp hTp (fun t ht => ht.2)
    q hq hqcrit (fun t ht => hqorders t ht.1)
  let C : ℝ≥0∞ := max Cs (max Cp Cn)
  have hC : C < ⊤ := max_lt_iff.mpr ⟨hCs, max_lt_iff.mpr ⟨hCp, hCn⟩⟩
  have hsC : Cs ≤ C := le_max_left _ _
  have hpC : Cp ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hnC : Cn ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, hC, ?_⟩
  intro γ hγ t ht z R δ hR hRhalf hchart hδ hδR
  by_cases hp : t.2 ≤ 1
  · exact (hs z R hR hRhalf hchart γ hγ t ⟨ht, hp⟩ δ hδ hδR).trans
      (mul_le_mul_left hsC _)
  have htp : t ∈ Tp := ⟨ht, (le_of_not_ge hp)⟩
  by_cases hα : 0 < t.1
  · exact (hpos γ hγ t htp hα z R hR hRhalf hchart δ hδ hδR).trans
      (mul_le_mul_left hpC _)
  · exact (hnonpos γ hγ t htp (le_of_not_gt hα) z R hR hRhalf hchart δ hδ hδR).trans
      (mul_le_mul_left hnC _)

end DOZZ.Proofs
