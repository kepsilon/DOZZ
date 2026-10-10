/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Continuity.MomentLimit
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The source frame has three finite roots and the fourth charge at infinity. -/
theorem fourPointMoment_jointly_continuous_parameters
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : ℝ → Ω → Measure ℂ) (z : ℂ) (hz : z ≠ 0 ∧ z ≠ 1)
    (K : Set (ℝ × (Fin 4 → ℝ))) (hK : IsCompact K)
    (hKdom : ∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ ExtendedSeibergN q.1 q.2)
    (hX : IsEquatorGFF P X) (hM : ∀ q ∈ K, IsGMCOf P X q.1 (M q.1)) :
    ContinuousOn (fun q : ℝ × (Fin 4 → ℝ) =>
      (∫⁻ ω, ENNReal.rpow
        (coulombMass q.1 (M q.1 ω) ![q.2 0, q.2 1, q.2 2] ![z, 0, 1] (q.2 3))
        (-nPointSExp q.1 q.2) ∂P).toReal) K := by
  classical
  obtain ⟨Mfam, hMf, hMeq⟩ := extendGMCFamily_on_compact P X hX M K hM
  obtain ⟨Xc, hXc⟩ := exists_equatorGFF_circle_average_witness X hX
  let J : (ℝ × (Fin 4 → ℝ)) → ContinuityCoulombParameter 3 :=
    fun q => (q.1, (![z, 0, 1], ![q.2 0, q.2 1, q.2 2], q.2 3))
  have hJ : Continuous J := by unfold J; fun_prop
  have hp (q : ℝ × (Fin 4 → ℝ)) : continuityCoulombPower (J q) = -nPointSExp q.1 q.2 := by
    simp [continuityCoulombPower, J, nPointSExp, Fin.sum_univ_three, Fin.sum_univ_four]
    ring
  have hz' : Function.Injective (![z, 0, 1] : Fin 3 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hadm : ∀ c ∈ J '' K, 0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      continuityCoulombPower c < 4 / c.1 ^ 2 ∧
      (∀ k, continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.2) := by
    rintro _ ⟨q, hq, rfl⟩
    obtain ⟨hγ, hγ2, hα, hbulk, hroot⟩ := hKdom q hq
    refine ⟨hγ, hγ2, hz', ?_, hα 3, ?_, ?_, ?_⟩
    · intro k
      fin_cases k
      · exact hα 0
      · exact hα 1
      · exact hα 2
    · simpa only [hp, J] using hbulk
    · intro k
      rw [hp]
      fin_cases k
      · exact hroot 0
      · exact hroot 1
      · exact hroot 2
    · simpa only [hp, J] using hroot 3
  have hm := (continuity_coulomb_moment_on_compact P X hX Xc hXc Mfam hMf
    (J '' K) (hK.image hJ) hadm).comp hJ.continuousOn (mapsTo_image J K)
  apply hm.congr
  intro q hq
  simp only [Function.comp_apply, J, hp, hMeq q hq]
  rfl

end DOZZ.Proofs
