/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.UnequalReduction
public import DOZZ.Correlations.Residue.EqualDecomposition

/-! The equal-charge unit-volume residue of the three-to-two residue bridge, reduced solely to the
exact two-insertion tail. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- The coalesced two-insertion estimate gives the factor-four unit-volume residue. All
remaining moment, complement and chart obligations are supplied by proved source helpers. -/
theorem residue_unit_equal_of_twoInsertion_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α Rbar dT : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : γ / 2 < α) (hαQ : α < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (hdT : 0 < dT)
    (htail : ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ ε, 0 < ε → ε < dT → ∀ t : ℝ, 1 ≤ t →
        |(P {ω | ENNReal.ofReal t <
            localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
            localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω}).toReal -
          (oneInsertionTailCoefficient γ α 3 (residueLocalWeight γ (2 * α + ε) α 7 3) Rbar * t ^ (-reflectionExponent γ α) +
           oneInsertionTailCoefficient γ α 7 (residueLocalWeight γ (2 * α + ε) α 3 7) Rbar * t ^ (-reflectionExponent γ α))| ≤
          C * t ^ (-(twoInsertionTailCeiling γ α α - θ))) :
    Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ ε α α)
      (𝓝[>] 0) (𝓝 (4 * reflectionExponent γ α * Rbar)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let p := reflectionExponent γ α
  have hp := (residue_critical_order_bounds γ α hγ hα hαQ).1
  let θ := (twoInsertionTailCeiling γ α α - p) / 2
  have hθ : 0 < θ := div_pos (sub_pos.mpr (residue_equal_twoInsertionTailCeiling_gt γ α hγ hα hαQ)) (by norm_num)
  have hexp : -(twoInsertionTailCeiling γ α α - θ) = -p - θ := by dsimp only [θ]; ring
  obtain ⟨C, hC, hCb⟩ := htail θ hθ
  obtain ⟨dR, ρ, hdR, hρ, K, hK, hKb⟩ := residue_equal_complement_moment_uniform
    P X M γ α hγ hγ2 hX hM hα hαQ
  let d₀ := min dT (min dR (γ * p))
  have hd₀ : 0 < d₀ := lt_min hdT (lt_min hdR (mul_pos hγ hp))
  have hdT' : d₀ ≤ dT := min_le_left _ _
  have hdR' : d₀ ≤ dR := (min_le_right _ _).trans (min_le_left _ _)
  have hdβ : d₀ ≤ γ * p := (min_le_right _ _).trans (min_le_right _ _)
  let A : ℝ → Ω → ℝ≥0∞ := fun ε ω =>
    localSingularMass M (residueLocalWeight γ (2 * α + ε) α 7) 3 γ α ω +
    localSingularMass M (residueLocalWeight γ (2 * α + ε) α 3) 7 γ α ω
  let R : ℝ → Ω → ℝ≥0∞ := fun ε ω => ∫⁻ x, if ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1 then
    coulombWeight γ ![α, α] ![3, 7] ε x else 0 ∂M ω
  let c : ℝ → ℝ := fun ε =>
    oneInsertionTailCoefficient γ α 3 (residueLocalWeight γ (2 * α + ε) α 7 3) Rbar +
    oneInsertionTailCoefficient γ α 7 (residueLocalWeight γ (2 * α + ε) α 3 7) Rbar
  have hA (ε : ℝ) : AEMeasurable (A ε) P :=
    (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _).add
    (localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _)
  have hR (ε : ℝ) : AEMeasurable (R ε) P := by
    have hset : MeasurableSet {x : ℂ | ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1} := by
      have hs : {x : ℂ | ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1} =
          (Metric.ball (3 : ℂ) 1)ᶜ ∩ (Metric.ball (7 : ℂ) 1)ᶜ := by
        ext x
        simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
      rw [hs]
      exact Metric.isOpen_ball.measurableSet.compl.inter Metric.isOpen_ball.measurableSet.compl
    have hf : Measurable (fun x : ℂ => if ∀ k : Fin 2, x ∉ Metric.ball (![3, 7] k) 1 then
        coulombWeight γ ![α, α] ![3, 7] ε x else 0) :=
      Measurable.ite hset (measurable_coulombWeight _ _ _ _) measurable_const
    exact (Measure.measurable_lintegral hf).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  have hlimA := residue_twoInsertion_equal_local_moment P X M γ α Rbar d₀
    hγ hγ2 hα hαQ hX hM hd₀ (by
      intro θ hθ
      obtain ⟨C, hC, hh⟩ := htail θ hθ
      exact ⟨C, hC, fun ε hε hεd => hh ε hε (hεd.trans_le hdT')⟩)
  have hq (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) : 0 < p - ε / γ ∧ p - ε / γ < p := by
    have hh : ε / γ < p := (div_lt_iff₀ hγ).mpr (by simpa only [mul_comm] using hεd.trans_le hdβ)
    exact ⟨sub_pos.mpr hh, sub_lt_self _ (div_pos hε hγ)⟩
  have htail' (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) (t : ℝ) (ht : 1 ≤ t) :
      |(P {ω | ENNReal.ofReal t < A ε ω}).toReal - c ε * t ^ (-p)| ≤ C * t ^ (-p - θ) := by
    have hh := hCb ε hε (hεd.trans_le hdT') t ht
    rw [hexp, ← add_mul] at hh
    exact hh
  have hAfin (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) : ∀ᵐ ω ∂P, A ε ω ≠ ⊤ :=
    residue_ae_finite_of_tail P (A ε) (c ε) p θ C hp hθ (htail' ε hε hεd)
  have hiA (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) :
      Integrable (fun ω => (A ε ω).toReal ^ (p - ε / γ)) P :=
    residue_real_power_integrable_of_extended_tail P (A ε) (hA ε) (c ε)
      p θ C (p - ε / γ) hp hθ hC (hq ε hε hεd).1 (hq ε hε hεd).2 (htail' ε hε hεd)
  have hsum := residue_extended_addition_preserves_limit P A R p γ d₀ (p + ρ)
    (2 * γ * p * (4 : ℝ) ^ (-(γ * α * p)) * Rbar) K hp hγ hd₀ hdβ
    (lt_add_of_pos_right _ hρ) hK (fun ε _ _ => hA ε) (fun ε _ _ => hR ε)
    hAfin hiA (fun ε hε hεd => hKb ε hε (hεd.trans_le hdR')) hlimA
  have hatoms : ∀ᵐ ω ∂P, M ω {3} = 0 ∧ M ω {7} = 0 :=
    (gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 3).and
      (gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 7)
  have hdecomp (ε : ℝ) : ∀ᵐ ω ∂P,
      coulombMass γ (M ω) ![α, α] ![3, 7] ε = A ε ω + R ε ω := by
    filter_upwards [hatoms] with ω hω
    exact residue_equal_mass_decomposition M ω γ α ε hω.1 hω.2
  have hh : Tendsto (fun ε : ℝ => ε *
      (∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α, α] ![3, 7] ε) (p - ε / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 (2 * γ * p * (4 : ℝ) ^ (-(γ * α * p)) * Rbar)) := by
    apply hsum.congr'
    filter_upwards [] with ε
    congr 2
    exact lintegral_congr_ae ((hdecomp ε).mono fun ω hω => congrArg (fun v : ℝ≥0∞ => ENNReal.rpow v (p - ε / γ)) hω.symm)
  have hunit := residue_unit_limit_from_chart_limit P X M γ α α 2 Rbar hγ hγ2 hX hM
    (by simpa only [sub_self, zero_add] using hh)
  simpa only [sub_self, zero_add, show (2 : ℝ) * 2 = 4 by norm_num] using hunit

end DOZZ.Proofs
