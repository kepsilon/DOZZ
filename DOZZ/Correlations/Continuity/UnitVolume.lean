/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Continuity.MomentLimit
public import DOZZ.Statements.Correlations.UnitVolumeNPointCorrelation
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The empty infinity insertion satisfies a weaker bound than the bulk bound. -/
theorem continuity_infinity_bound {γ p : ℝ} (hγ : 0 < γ)
    (hp : p < 4 / γ ^ 2) : p < 2 / γ * (Q γ - 0) := by
  have he : 2 / γ * (Q γ - 0) = 4 / γ ^ 2 + 1 := by
    unfold Q
    field_simp
    ring
  rw [he]
  linarith

/-- The finite-position prefactor is continuous in all charges at distinct roots. -/
theorem continuity_finite_prefactor {N : ℕ} (z : Fin N → ℂ)
    (hz : ∀ i j, i ≠ j → z i ≠ z j) :
    Continuous (fun α : Fin N → ℝ => nPointCoulombPrefactor α z) := by
  classical
  unfold nPointCoulombPrefactor
  apply continuous_finsetProd
  intro i _
  apply continuous_finsetProd
  intro j _
  by_cases hij : i < j
  · simp only [ite_eq_left hij]
    apply (Real.continuous_const_rpow (norm_ne_zero_iff.mpr
      (sub_ne_zero.mpr (hz i j (ne_of_lt hij))))).comp
    fun_prop
  · simp only [ite_eq_right hij]
    exact continuous_const

/-- Joint continuity of the normalized unit-volume moments on the literal domain of
`DOZZ.unitVolumeNPoint_jointly_continuous_parameters`. -/
theorem unitVolumeNPoint_jointly_continuous_parameters
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 3 ≤ N)
    (P : Measure Ω) (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ)
    (z : Fin N → ℂ) (hz : ∀ i j, i ≠ j → z i ≠ z j)
    (K : Set (ℝ × (Fin N → ℝ))) (hK : IsCompact K)
    (hKdom : ∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ ExtendedSeibergN q.1 q.2)
    (hX : IsEquatorGFF P X)
    (hM : ∀ q ∈ K, IsGMCOf P X q.1 (M q.1)) :
    ContinuousOn (fun q => unitVolumeNPointCorrelation P (M q.1) q.1 q.2 z) K := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hN
  obtain ⟨Mfam, hMf, hMeq⟩ := extendGMCFamily_on_compact P X hX M K hM
  obtain ⟨Xc, hXc⟩ := exists_equatorGFF_circle_average_witness X hX
  let J : (ℝ × (Fin (3 + n) → ℝ)) → ContinuityCoulombParameter (3 + n) :=
    fun q => (q.1, (z, q.2, 0))
  have hJ : Continuous J := by unfold J; fun_prop
  have hp (q : ℝ × (Fin (3 + n) → ℝ)) : continuityCoulombPower (J q) = -nPointSExp q.1 q.2 := by
    simp only [continuityCoulombPower, J, nPointSExp, add_zero]
    ring
  have hz' : Function.Injective z := by
    intro i j hij
    by_contra hne
    exact hz i j hne hij
  have hadm : ∀ c ∈ J '' K, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      continuityCoulombPower c < 4 / c.1 ^ 2 ∧
      (∀ k, continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.2) := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hγ, hγ2, hα, hbulk, hroot⟩ := hKdom q hq
    refine ⟨hγ, hγ2, hz', hα, ?_, ?_, ?_, ?_⟩
    · change 0 < Q q.1
      unfold Q
      positivity
    · simpa only [hp, J] using hbulk
    · simpa only [hp, J] using hroot
    · simpa only [hp, J] using continuity_infinity_bound hγ hbulk
  have hm := (continuity_coulomb_moment_on_compact P X hX Xc hXc Mfam hMf
    (J '' K) (hK.image hJ) hadm).comp hJ.continuousOn (mapsTo_image J K)
  have hm' : ContinuousOn (fun q => (∫⁻ ω,
      (coulombMass q.1 (M q.1 ω) q.2 z 0) ^ (-nPointSExp q.1 q.2) ∂P).toReal) K := by
    apply hm.congr
    intro q hq
    simp only [Function.comp_apply, J, hp, hMeq q hq]
  have hc : ContinuousOn (fun q : ℝ × (Fin (3 + n) → ℝ) => 2 / q.1) K :=
    continuousOn_const.div continuous_fst.continuousOn (fun q hq => (hKdom q hq).1.ne')
  have hf : Continuous (fun q : ℝ × (Fin (3 + n) → ℝ) => nPointCoulombPrefactor q.2 z) :=
    (continuity_finite_prefactor z hz).comp continuous_snd
  exact (hc.mul hf.continuousOn).mul hm'

end DOZZ.Proofs
