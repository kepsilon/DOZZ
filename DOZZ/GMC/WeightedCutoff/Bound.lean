module

public import DOZZ.GMC.WeightedCutoff.UniformGamma

/-! # Weighted cutoff bounds at a fixed subcritical coupling -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem equatorGFF_GMC_weighted_cutoff_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ t ∈ T, t.1 < Q γ ∧ 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    (K : Set ℂ) (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ T, ∀ z ∈ K, ∀ δ R : ℝ,
      0 < δ → δ ≤ R → R ≤ r₀ →
      (∫⁻ ω,
        ENNReal.rpow (cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω) t.2 ∂P) ≤
        ENNReal.ofReal (C * Real.rpow R
          (γ * (Q γ - t.1) * t.2 - γ ^ 2 * t.2 ^ 2 / 2)) := by
  have hΓ2 : {γ} ⊆ Set.Ioo (0 : ℝ) 2 := by
    intro g hg
    have hg' : g = γ := Set.mem_singleton_iff.mp hg
    subst g
    exact ⟨hγ, hγ2⟩
  have hadm : ∀ g ∈ ({γ} : Set ℝ), ∀ t ∈ T, t.1 < Q g ∧ 0 < t.2 ∧
      t.2 < min (4 / g ^ 2) (2 / g * (Q g - t.1)) := by
    intro g hg
    have hg' : g = γ := Set.mem_singleton_iff.mp hg
    subst g
    exact hTadm
  obtain ⟨C, hC, hbound⟩ := equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma
    P X hX {γ} isCompact_singleton hΓ2 Xc hXc T hT hadm K hK r₀ hr₀
  refine ⟨C, hC, ?_⟩
  intro t ht z hz δ R hδ hδR hR₀
  exact hbound γ (by simp) t ht z hz δ R hδ hδR hR₀

end DOZZ.Proofs
