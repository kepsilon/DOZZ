module

public import DOZZ.GMC.WeightedCutoff.RootUniform

/-! # A common subcritical order cap for compact parameter families -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem exists_weighted_cutoff_order_cap
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓn : Γ.Nonempty)
    (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T) (hTn : T.Nonempty)
    (hcrit : ∀ γ ∈ Γ, ∀ t ∈ T, t.2 < 4 / γ ^ 2) :
    ∃ q : ℝ, 1 < q ∧ (∀ γ ∈ Γ, q < 4 / γ ^ 2) ∧ ∀ t ∈ T, t.2 ≤ q := by
  obtain ⟨g, hg, hγmax⟩ := hΓ.exists_isMaxOn hΓn continuousOn_id
  obtain ⟨tmax, htmax, hpmax⟩ := hT.exists_isMaxOn hTn continuous_snd.continuousOn
  have hgpos : 0 < g := (hΓ2 hg).1
  have hg2 : g < 2 := (hΓ2 hg).2
  have hone : 1 < 4 / g ^ 2 := by
    apply (lt_div_iff₀ (sq_pos_of_pos hgpos)).mpr
    nlinarith
  have hmax : max 1 tmax.2 < 4 / g ^ 2 :=
    max_lt_iff.mpr ⟨hone, hcrit g hg tmax htmax⟩
  obtain ⟨q, hqlo, hqhi⟩ := exists_between hmax
  refine ⟨q, lt_of_le_of_lt (le_max_left _ _) hqlo, ?_, ?_⟩
  · intro γ hγ
    have hγpos : 0 < γ := (hΓ2 hγ).1
    have hγg : γ ≤ g := hγmax hγ
    have hγsq : γ ^ 2 ≤ g ^ 2 := by nlinarith
    exact hqhi.trans_le (div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hγpos) hγsq)
  · intro t ht
    exact (hpmax ht).trans ((le_max_right _ _).trans hqlo.le)

end DOZZ.Proofs
