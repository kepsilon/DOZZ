module

public import DOZZ.GMC.WeightedCutoff.SmallBound

/-! # Compact bounds for the deterministic weight and scale factors -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem exists_compact_cutoff_weight_bound
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (T : Set (ℝ × ℝ)) (hT : IsCompact T)
    (a b : ℝ) (ha : 0 < a) :
    ∃ W : ℝ, 0 < W ∧ ∀ γ ∈ Γ, ∀ t ∈ T, ∀ s ∈ Set.Icc a b,
      s ^ (-γ * t.1) ≤ W := by
  let S : Set (ℝ × ((ℝ × ℝ) × ℝ)) := Γ ×ˢ (T ×ˢ Set.Icc a b)
  have hS : IsCompact S := hΓ.prod (hT.prod isCompact_Icc)
  let f : ℝ × ((ℝ × ℝ) × ℝ) → ℝ := fun u => u.2.2 ^ (-u.1 * u.2.1.1)
  have hf : ContinuousOn f S := by
    apply ContinuousOn.rpow
    · fun_prop
    · fun_prop
    · intro u hu
      exact Or.inl (ne_of_gt (ha.trans_le hu.2.2.1))
  obtain ⟨W, hW, hnorm⟩ := (hS.image_of_continuousOn hf).isBounded.exists_pos_norm_le
  refine ⟨W, hW, ?_⟩
  intro γ hγ t ht s hs
  have h := hnorm (f (γ, t, s)) ⟨(γ, t, s), ⟨hγ, ht, hs⟩, rfl⟩
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)

theorem exists_compact_cutoff_scale_bounds
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T) (a b : ℝ) (ha : 0 < a) :
    ∃ L U : ℝ, 0 < L ∧ 0 < U ∧
      (∀ γ ∈ Γ, ∀ t ∈ T, a ^ weightedCutoffMomentScaleExponent γ t.1 t.2 ≤ U) ∧
      (∀ γ ∈ Γ, ∀ t ∈ T, ∀ R ∈ Set.Icc a b,
        L ≤ R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
  let S : Set (ℝ × ((ℝ × ℝ) × ℝ)) := Γ ×ˢ (T ×ˢ Set.Icc a b)
  have hS : IsCompact S := hΓ.prod (hT.prod isCompact_Icc)
  have hQ : ContinuousOn (fun γ : ℝ => Q γ) Γ := by
    dsimp [Q]
    apply ContinuousOn.add
    · exact continuousOn_const.div continuousOn_id (fun γ hγ => (hΓpos γ hγ).ne')
    · exact continuousOn_id.div_const 2
  have hQS : ContinuousOn (fun u : ℝ × ((ℝ × ℝ) × ℝ) => Q u.1) S :=
    hQ.comp continuousOn_fst (fun u hu => hu.1)
  let f : ℝ × ((ℝ × ℝ) × ℝ) → ℝ := fun u =>
    u.2.2 ^ weightedCutoffMomentScaleExponent u.1 u.2.1.1 u.2.1.2
  have hf : ContinuousOn f S := by
    dsimp [f, weightedCutoffMomentScaleExponent]
    apply ContinuousOn.rpow
    · fun_prop
    · fun_prop
    · intro u hu
      exact Or.inl (ne_of_gt (ha.trans_le hu.2.2.1))
  have hfpos : ∀ u ∈ S, 0 < f u := fun u hu =>
    Real.rpow_pos_of_pos (ha.trans_le hu.2.2.1) _
  obtain ⟨L, hL, hLower⟩ := hS.exists_forall_le' hf hfpos
  let V : Set (ℝ × (ℝ × ℝ)) := Γ ×ˢ T
  have hV : IsCompact V := hΓ.prod hT
  have hQV : ContinuousOn (fun u : ℝ × (ℝ × ℝ) => Q u.1) V :=
    hQ.comp continuousOn_fst (fun u hu => hu.1)
  let g : ℝ × (ℝ × ℝ) → ℝ := fun u => a ^ weightedCutoffMomentScaleExponent u.1 u.2.1 u.2.2
  have hg : ContinuousOn g V := by
    have ha0 : a ≠ 0 := ha.ne'
    dsimp [g, weightedCutoffMomentScaleExponent]
    fun_prop
  obtain ⟨U, hU, hnorm⟩ := (hV.image_of_continuousOn hg).isBounded.exists_pos_norm_le
  refine ⟨L, U, hL, hU, ?_, ?_⟩
  · intro γ hγ t ht
    have h := hnorm (g (γ, t)) ⟨(γ, t), ⟨hγ, ht⟩, rfl⟩
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using h)
  · intro γ hγ t ht R hR
    exact hLower (γ, t, R) ⟨hγ, ht, hR⟩

end DOZZ.Proofs
