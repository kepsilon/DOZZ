/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.LocalTailMoments
public import DOZZ.Correlations.Residue.ExtendedAddition
public import DOZZ.Correlations.Residue.ComplementUniform
public import DOZZ.Correlations.Residue.MassDecomposition
public import DOZZ.Correlations.Residue.ChartLimit

/-! The full unequal-charge unit-volume residue (erratum K30, see docs/ERRATA-AND-DEVIATIONS.md),
reduced solely to the exact insertion tail. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- All moment, complement, chart and normalization steps of the unequal-charge residue are
proved. The remaining input is the one-insertion estimate, uniform in the actual epsilon family. -/
theorem residue_unit_unequal_of_oneInsertion_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 Rbar η dT C : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα2 : 0 < α2) (hα23 : α2 < α3)
    (hα3 : γ / 2 < α3) (hα3Q : α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hη : 0 < η) (hdT : 0 < dT) (hC : 0 ≤ C)
    (htail : ∀ ε, 0 < ε → ε < dT → ∀ t : ℝ, 1 ≤ t →
      |(P {ω | ENNReal.ofReal t < localSingularMass M
        (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3 ω}).toReal -
        oneInsertionTailCoefficient γ α3 3 (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar *
          t ^ (-reflectionExponent γ α3)| ≤ C * t ^ (-reflectionExponent γ α3 - η)) :
    Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
      (α3 - α2 + ε) α2 α3) (𝓝[>] 0) (𝓝 (2 * reflectionExponent γ α3 * Rbar)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let p := reflectionExponent γ α3
  have hp := (residue_critical_order_bounds γ α3 hγ hα3 hα3Q).1
  obtain ⟨dR, ρ, hdR, hρ, K, hK, hKb⟩ := residue_unequal_complement_moment_uniform
    P X M γ α2 α3 hγ hγ2 hX hM hα2 hα23 hα3 hα3Q
  let d₀ := min dT (min dR (γ * p))
  have hd₀ : 0 < d₀ := lt_min hdT (lt_min hdR (mul_pos hγ hp))
  have hdT' : d₀ ≤ dT := min_le_left _ _
  have hdR' : d₀ ≤ dR := (min_le_right _ _).trans (min_le_left _ _)
  have hdβ : d₀ ≤ γ * p := (min_le_right _ _).trans (min_le_right _ _)
  let A : ℝ → Ω → ℝ≥0∞ := fun ε =>
    localSingularMass M (residueLocalWeight γ (2 * α3 + ε) α2 7) 3 γ α3
  let R : ℝ → Ω → ℝ≥0∞ := fun ε ω => ∫⁻ x, if x ∉ Metric.ball (3 : ℂ) 1 then
    coulombWeight γ ![α3, α2] ![3, 7] (α3 - α2 + ε) x else 0 ∂M ω
  have hA (ε : ℝ) : AEMeasurable (A ε) P :=
    localSingularMass_aemeasurable P X hX γ hγ hγ2 M hM _
      (by unfold residueLocalWeight; fun_prop) _ _
  have hR (ε : ℝ) : AEMeasurable (R ε) P := by
    have hf : Measurable (fun x : ℂ => if x ∉ Metric.ball (3 : ℂ) 1 then
        coulombWeight γ ![α3, α2] ![3, 7] (α3 - α2 + ε) x else 0) :=
      Measurable.ite Metric.isOpen_ball.measurableSet.compl (measurable_coulombWeight _ _ _ _) measurable_const
    exact (Measure.measurable_lintegral hf).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
  have hlimA := residue_oneInsertion_local_moment P X M γ α2 α3 Rbar η d₀ C
    hγ hγ2 hα3 hα3Q hX hM hη hd₀ hC
    (fun ε hε hεd => htail ε hε (hεd.trans_le hdT'))
  have hq (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) : 0 < p - ε / γ ∧ p - ε / γ < p := by
    have hh : ε / γ < p := (div_lt_iff₀ hγ).mpr (by simpa only [mul_comm] using hεd.trans_le hdβ)
    exact ⟨sub_pos.mpr hh, sub_lt_self _ (div_pos hε hγ)⟩
  have htail' (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) := htail ε hε (hεd.trans_le hdT')
  have hAfin (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) : ∀ᵐ ω ∂P, A ε ω ≠ ⊤ :=
    residue_ae_finite_of_tail P (A ε)
      (oneInsertionTailCoefficient γ α3 3 (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar)
      p η C hp hη (htail' ε hε hεd)
  have hiA (ε : ℝ) (hε : 0 < ε) (hεd : ε < d₀) :
      Integrable (fun ω => (A ε ω).toReal ^ (p - ε / γ)) P :=
    residue_real_power_integrable_of_extended_tail P (A ε) (hA ε)
      (oneInsertionTailCoefficient γ α3 3 (residueLocalWeight γ (2 * α3 + ε) α2 7 3) Rbar)
      p η C (p - ε / γ) hp hη hC (hq ε hε hεd).1 (hq ε hε hεd).2 (htail' ε hε hεd)
  have hsum := residue_extended_addition_preserves_limit P A R p γ d₀ (p + ρ)
    (γ * p * (4 : ℝ) ^ (-(γ * α2 * p)) * Rbar) K hp hγ hd₀ hdβ
    (lt_add_of_pos_right _ hρ) hK (fun ε _ _ => hA ε) (fun ε _ _ => hR ε)
    hAfin hiA (fun ε hε hεd => hKb ε hε (hεd.trans_le hdR')) hlimA
  have hatoms : ∀ᵐ ω ∂P, M ω {3} = 0 ∧ M ω {7} = 0 :=
    (gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 3).and
      (gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 7)
  have hdecomp (ε : ℝ) : ∀ᵐ ω ∂P,
      coulombMass γ (M ω) ![α3, α2] ![3, 7] (α3 - α2 + ε) = A ε ω + R ε ω := by
    filter_upwards [hatoms] with ω hω
    rw [residue_mass_decomposition γ α3 α2 (α3 - α2 + ε) 3 7 (by norm_num) (by norm_num) (by norm_num)
      (M ω) hω.1 hω.2]
    have hS : α3 + α2 + (α3 - α2 + ε) = 2 * α3 + ε := by ring
    rw [hS]
    rfl
  have hh : Tendsto (fun ε : ℝ => ε *
      (∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) ![α3, α2] ![3, 7] (α3 - α2 + ε)) (p - ε / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 (γ * p * (4 : ℝ) ^ (-(γ * α2 * p)) * Rbar)) := by
    apply hsum.congr'
    filter_upwards [] with ε
    congr 2
    exact lintegral_congr_ae ((hdecomp ε).mono fun ω hω => congrArg (fun v : ℝ≥0∞ => ENNReal.rpow v (p - ε / γ)) hω.symm)
  simpa only [mul_one] using residue_unit_limit_from_chart_limit P X M γ α2 α3 1 Rbar
    hγ hγ2 hX hM (by simpa only [one_mul] using hh)

end DOZZ.Proofs
