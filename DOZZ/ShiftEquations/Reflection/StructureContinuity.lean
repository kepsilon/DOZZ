/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.FrameGeneral
public import DOZZ.Statements.Correlations.ExtendedSeibergN
import DOZZ.Correlations.Continuity.UnitVolume

/-!
# Joint continuity of the unit-volume structure constant

Through the finite frame `(0, 2, -2)` the structure constant is a continuous positive multiple of
the finite-position unit-volume moment, which is jointly continuous in `(γ, α)` on compact subsets
of the strict extended domain (`unitVolumeNPoint_jointly_continuous_parameters`). This is the last
conjunct of `DOZZ.reflection_endpoint_and_gamma_continuity`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The three charges of the extended domain satisfy the `N`-point extended bounds. -/
theorem extendedSeibergN_of_extendedSeiberg3 {γ α₁ α₂ α₃ : ℝ}
    (h : ExtendedSeiberg3 γ α₁ α₂ α₃) : ExtendedSeibergN γ ![α₁, α₂, α₃] := by
  obtain ⟨h1, h2, h3, hs⟩ := h
  have hsN : -nPointSExp γ ![α₁, α₂, α₃] = -sExp γ α₁ α₂ α₃ := by
    unfold nPointSExp sExp
    rw [Fin.sum_univ_three]
    simp
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact h1
    · exact h2
    · exact h3
  · rw [hsN]
    exact lt_of_lt_of_le hs (min_le_left _ _)
  · intro i
    rw [hsN]
    fin_cases i
    · exact lt_of_lt_of_le hs ((min_le_right _ _).trans (min_le_left _ _))
    · exact lt_of_lt_of_le hs ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_left _ _)))
    · exact lt_of_lt_of_le hs ((min_le_right _ _).trans ((min_le_right _ _).trans
        (min_le_right _ _)))

theorem distinct_pole_frame : ∀ i j : Fin 3, i ≠ j →
    (![0, 2, -2] : Fin 3 → ℂ) i ≠ (![0, 2, -2] : Fin 3 → ℂ) j := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | (simp_all; done) | (simp_all; norm_num)

theorem nPointCoulombPrefactor_pole_frame_pos (α : Fin 3 → ℝ) :
    0 < nPointCoulombPrefactor α ![0, 2, -2] := by
  unfold nPointCoulombPrefactor
  refine Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => ?_
  split_ifs with hij
  · exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr
      (distinct_pole_frame i j (ne_of_lt hij)))) _
  · exact one_pos

theorem continuous_nPointCoulombPrefactor_pole_frame :
    Continuous fun α : Fin 3 → ℝ => nPointCoulombPrefactor α ![0, 2, -2] := by
  unfold nPointCoulombPrefactor
  refine continuous_finsetProd _ fun i _ => continuous_finsetProd _ fun j _ => ?_
  split_ifs with hij
  · have hpos : 0 < ‖(![0, 2, -2] : Fin 3 → ℂ) i - (![0, 2, -2] : Fin 3 → ℂ) j‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (distinct_pole_frame i j (ne_of_lt hij)))
    exact continuous_const.rpow ((continuous_apply i).mul (continuous_apply j)).neg
      fun _ => Or.inl hpos.ne'
  · exact continuous_const

theorem vec_three_eta (α : Fin 3 → ℝ) : (![α 0, α 1, α 2] : Fin 3 → ℝ) = α := by
  funext i
  fin_cases i <;> rfl

/-- **Joint continuity of the unit-volume structure constant** (last conjunct of
`DOZZ.reflection_endpoint_and_gamma_continuity`). -/
theorem continuousOn_unitVolumeStructureConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (hX : IsEquatorGFF P X)
    (hM : ∀ γ, 0 < γ → γ < 2 → IsGMCOf P X γ (M γ))
    (K : Set (ℝ × (Fin 3 → ℝ))) (hK : IsCompact K)
    (hKdom : ∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ ExtendedSeiberg3 q.1 (q.2 0) (q.2 1) (q.2 2)) :
    ContinuousOn (fun q => unitVolumeStructureConstant P (M q.1) q.1 (q.2 0) (q.2 1) (q.2 2))
      K := by
  have hcont := unitVolumeNPoint_jointly_continuous_parameters (N := 3) le_rfl P X M
    ![0, 2, -2] distinct_pole_frame K hK (fun q hq => ⟨(hKdom q hq).1, (hKdom q hq).2.1, by
      rw [← vec_three_eta q.2]
      exact extendedSeibergN_of_extendedSeiberg3 (hKdom q hq).2.2⟩) hX
    (fun q hq => hM q.1 (hKdom q hq).1 (hKdom q hq).2.1)
  have hγne : ∀ q ∈ K, q.1 ≠ 0 := fun q hq => (hKdom q hq).1.ne'
  have hfst : ContinuousOn (fun q : ℝ × (Fin 3 → ℝ) => q.1) K := continuous_fst.continuousOn
  have hQc : ContinuousOn (fun q : ℝ × (Fin 3 → ℝ) => Q q.1) K := by
    unfold Q
    exact (continuousOn_const.div hfst hγne).add (hfst.div_const _)
  have hsum : Continuous fun q : ℝ × (Fin 3 → ℝ) => q.2 0 + q.2 1 + q.2 2 := by fun_prop
  have hnum : ContinuousOn (fun q : ℝ × (Fin 3 → ℝ) => q.2 0 + q.2 1 + q.2 2 - 2 * Q q.1) K :=
    hsum.continuousOn.sub (continuousOn_const.mul hQc)
  have hsc : ContinuousOn (fun q : ℝ × (Fin 3 → ℝ) => sExp q.1 (q.2 0) (q.2 1) (q.2 2)) K := by
    unfold sExp
    exact hnum.div hfst hγne
  have hpre : Continuous fun q : ℝ × (Fin 3 → ℝ) => q.1 * (q.2 1 + q.2 2) := by fun_prop
  have hexp : ContinuousOn (fun q : ℝ × (Fin 3 → ℝ) =>
      q.1 * (q.2 1 + q.2 2) * (-sExp q.1 (q.2 0) (q.2 1) (q.2 2))) K :=
    hpre.continuousOn.mul hsc.neg
  have hfac : ContinuousOn (fun q : ℝ × (Fin 3 → ℝ) =>
      (2 : ℝ) ^ (q.1 * (q.2 1 + q.2 2) * (-sExp q.1 (q.2 0) (q.2 1) (q.2 2))) /
        nPointCoulombPrefactor q.2 ![0, 2, -2]) K :=
    (continuousOn_const.rpow hexp fun _ _ => Or.inl two_ne_zero).div
      (continuous_nPointCoulombPrefactor_pole_frame.comp continuous_snd).continuousOn
      fun q _ => (nPointCoulombPrefactor_pole_frame_pos q.2).ne'
  refine (hfac.mul hcont).congr fun q hq => ?_
  have h := unitVolumeStructureConstant_eq_nPoint P X hX q.1 (hKdom q hq).1 (hKdom q hq).2.1
    (M q.1) (hM q.1 (hKdom q hq).1 (hKdom q hq).2.1) (q.2 0) (q.2 1) (q.2 2)
  rw [vec_three_eta] at h
  exact h

end DOZZ.Proofs

end
