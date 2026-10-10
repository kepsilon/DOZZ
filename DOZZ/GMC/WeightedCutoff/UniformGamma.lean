module

public import DOZZ.GMC.WeightedCutoff.LargeBound

/-! # Weighted cutoff bounds uniform in the coupling

The compact-center location comparison and local scaling prove the small-radius estimate.
At larger radii a fixed singular core is combined with a bounded outer weight. Gaussian
Jensen controls coarse physical cutoffs, including cutoffs larger than one.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem equatorGFF_GMC_weighted_cutoff_bound_uniform_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (hTadm : ∀ γ ∈ Γ, ∀ t ∈ T, t.1 < Q γ ∧ 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)))
    (K : Set ℂ) (hK : IsCompact K) (r₀ : ℝ) (hr₀ : 0 < r₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ z ∈ K, ∀ δ R : ℝ,
      0 < δ → δ ≤ R → R ≤ r₀ →
      (∫⁻ ω, ENNReal.rpow
        (cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω) t.2 ∂P) ≤
        ENNReal.ofReal (C * Real.rpow R
          (γ * (Q γ - t.1) * t.2 - γ ^ 2 * t.2 ^ 2 / 2)) := by
  have hadm : ∀ γ ∈ Γ, ∀ t ∈ T, 0 < t.2 ∧
      t.2 < min (4 / γ ^ 2) (2 / γ * (Q γ - t.1)) :=
    fun γ hγ t ht => (hTadm γ hγ t ht).2
  obtain ⟨Cs, hCs, hsmall⟩ := cutoffWeightedGmcBallMoment_compact_gamma_small_bound
    P X hX Xc hXc Γ hΓ hΓ2 T hT hadm K hK
  obtain ⟨E, hE, hlarge⟩ := cutoffWeightedGmcBallMoment_compact_gamma_large_uniform
    P X hX Xc hXc Γ hΓ hΓ2 T hT hadm K hK r₀ hr₀
  obtain ⟨L, U, hL, hU, hupper, hlower⟩ := exists_compact_cutoff_scale_bounds
    Γ hΓ (fun γ hγ => (hΓ2 hγ).1) T hT (1 / 8 : ℝ) r₀ (by norm_num)
  let Cl : ℝ := (E.toReal + 1) / L
  have hCl : 0 < Cl := by dsimp [Cl]; positivity
  let C : ℝ := max Cs Cl
  have hC : 0 < C := hCs.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro γ hγ t ht z hz δ R hδ hδR hR₀
  have hR : 0 < R := hδ.trans_le hδR
  change (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤
    ENNReal.ofReal (C * R ^ weightedCutoffMomentScaleExponent γ t.1 t.2)
  by_cases hRsmall : R ≤ 1 / 2
  · apply (hsmall γ hγ t ht z hz R δ hR hRsmall hδ hδR).trans
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (le_max_left Cs Cl) (Real.rpow_nonneg hR.le _))
  have hRa : 1 / 8 ≤ R := by linarith
  have hscale := hlower γ hγ t ht R ⟨hRa, hR₀⟩
  have hEscale : E ≤ ENNReal.ofReal (Cl * R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
    rw [← ENNReal.ofReal_toReal hE.ne]
    apply ENNReal.ofReal_le_ofReal
    calc
      E.toReal ≤ E.toReal + 1 := by linarith
      _ = Cl * L := by dsimp [Cl]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hscale hCl.le
  calc
    _ ≤ E := hlarge γ hγ t ht z hz R δ hRa hR₀ hδ hδR
    _ ≤ _ := hEscale
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (le_max_right Cs Cl) (Real.rpow_nonneg hR.le _))

end DOZZ.Proofs
