/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.GMC.Moments.RhoCoulomb
import DOZZ.GMC.SharpMoments.SeibergMoment
import DOZZ.GMC.SharpMoments.SeibergMomentBound
import DOZZ.Brownian.Reflection.LastCut
import DOZZ.Correlations.Residue.FullFromUnit

/-! Nonvanishing of a physical three-point value for the cancellation in the gluing equation of
`DOZZ.structureConstant_reflected_shift_and_gluing`. Finite positive Coulomb moments and inverse
moments justify both positivity and the `toReal` totalization in the moment definition. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The unit-volume three-point value is positive when all charges are below `Q`
and the zero-mode exponent is positive. -/
theorem unitVolume_pos_of_positive_sExp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (hs : 0 < sExp γ a b c) :
    0 < unitVolumeStructureConstant P M γ a b c := by
  let _ : IsProbabilityMeasure P := hX.1
  let Z : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) ![a, b] ![0, 1] c
  have hZm : AEMeasurable Z P :=
    gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _
  let T : ℝ := min (4 / γ ^ 2)
    (min (2 / γ * (Q γ - a)) (min (2 / γ * (Q γ - b)) (2 / γ * (Q γ - c))))
  have hT : 0 < T := lt_min (by positivity)
    (lt_min (mul_pos (by positivity) (sub_pos.mpr ha))
      (lt_min (mul_pos (by positivity) (sub_pos.mpr hb))
        (mul_pos (by positivity) (sub_pos.mpr hc))))
  obtain ⟨t, ht, htT⟩ := exists_between hT
  have hz : Function.Injective (![0, 1] : Fin 2 → ℂ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have htf : ∫⁻ ω, Z ω ^ t ∂P < ⊤ := by
    apply coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM
      ![0, 1] hz ![a, b] c t ht (htT.trans_le (min_le_left _ _))
    · intro k
      fin_cases k
      · exact htT.trans_le ((min_le_right _ _).trans (min_le_left _ _))
      · exact htT.trans_le ((min_le_right _ _).trans
          ((min_le_right _ _).trans (min_le_left _ _)))
    · exact htT.trans_le ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  have hZfin := ae_lt_top_of_lintegral_rpow_lt_top hZm ht htf
  obtain ⟨K, hK, hKb⟩ := coulombMass_moment_uniform_nonpos P X hX γ hγ hγ2 M hM
    2 3 (by norm_num) (|a| + |b| + |c|) (-sExp γ a b c) (neg_nonpos.mpr hs.le)
  have hnf : ∫⁻ ω, Z ω ^ (-sExp γ a b c) ∂P < ⊤ := by
    apply lt_of_le_of_lt (hKb ![0, 1] ![a, b] c (-sExp γ a b c) ?_ ?_ ?_
      le_rfl (neg_nonpos.mpr hs.le)) hK
    · intro j
      fin_cases j <;> norm_num
    · intro j
      fin_cases j
      · change |a| ≤ |a| + |b| + |c|
        linarith [abs_nonneg b, abs_nonneg c]
      · change |b| ≤ |a| + |b| + |c|
        linarith [abs_nonneg a, abs_nonneg c]
    · linarith [abs_nonneg a, abs_nonneg b]
  have hZpos := ae_pos_of_lintegral_rpow_neg_lt_top hZm hs hnf
  have hnpos : ∀ᵐ ω ∂P, 0 < Z ω ^ (-sExp γ a b c) := by
    filter_upwards [hZpos, hZfin] with ω hωp hωf
    exact ENNReal.rpow_pos hωp hωf.ne
  have hne : (∫⁻ ω, Z ω ^ (-sExp γ a b c) ∂P) ≠ 0 := by
    intro hzero
    have hzeroae := (lintegral_eq_zero_iff' (hZm.pow_const _)).mp hzero
    obtain ⟨ω, hωp, hωz⟩ := (hnpos.and hzeroae).exists
    exact hωp.ne' hωz
  unfold unitVolumeStructureConstant
  change 0 < 2 / γ * (∫⁻ ω, ENNReal.rpow (rho γ (M ω) a b c)
    (-sExp γ a b c) ∂P).toReal
  rw [rho_moment_eq_coulomb_moment P X hX γ hγ hγ2 M hM a b c]
  have he : (2 * Q γ - ((∑ k : Fin 2, (![a, b] : Fin 2 → ℝ) k) + c)) / γ =
      -sExp γ a b c := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sExp]
    ring
  rw [he]
  exact mul_pos (by positivity) (ENNReal.toReal_pos hne hnf.ne)

/-- Positivity of the full physical three-point constant, including the moment
normalization, for a positive zero-mode exponent. -/
theorem structureConstant_pos
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (hs : 0 < sExp γ a b c) :
    0 < structureConstant P M γ μ a b c := by
  rw [residue_structureConstant_eq_unitVolume]
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos hμ _) (Real.Gamma_pos_of_pos hs))
    (unitVolume_pos_of_positive_sExp P X M γ a b c hγ hγ2 hX hM ha hb hc hs)

end DOZZ.Proofs
