/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorExterior
public import DOZZ.GMC.Annulus.BallCover

/-! Combining a finite spatial cover of the actual positive Taylor square. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A finite measurable spatial cover bounds the whole positive Taylor square by its regional
squares. Each expectation uses the same full Coulomb inverse mass. -/
theorem twoRooted_region_cover
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (z : ℂ) (B : Fin 4 → Set ℂ)
    (hB : ∀ i, MeasurableSet (B i)) (hcover : ⋃ i, B i = Set.univ) :
    gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p z ≤
      16 * ∑ i : Fin 4, gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z (B i) := by
  let f : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖)
  let A : Fin 4 → Ω → ℝ≥0∞ := fun i ω => ∫⁻ x in B i, f x ∂M ω
  let I : Ω → ℝ≥0∞ := fun ω => (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) ^ (-p - 2)
  have hf : Measurable f := gammaHalf_absolute_kernel_measurable γ α₁ α₂ α₃ z
  have hMm := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
  have hA (i : Fin 4) : AEMeasurable (A i) P := by
    have hm := Measure.measurable_lintegral (hf.indicator (hB i))
    have hh := hm.comp_aemeasurable hMm
    simpa only [lintegral_indicator (hB i), Function.comp_def, A] using hh
  have hI : AEMeasurable I P :=
    ((coulombMass_measure_measurable γ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).comp_aemeasurable hMm).pow_const _
  have hpoint (ω : Ω) : I ω * (∫⁻ x, f x ∂M ω) ^ 2 ≤
      16 * ∑ i : Fin 4, (A i ω) ^ 2 * I ω := by
    have hmass : (∫⁻ x, f x ∂M ω) ≤ ∑ i : Fin 4, A i ω := by
      have hh := lintegral_iUnion_le (μ := M ω) B f
      simpa only [hcover, setLIntegral_univ, tsum_fintype] using hh
    have hpow := ennreal_finset_sum_rpow_le_card_rpow_sum Finset.univ
      (Finset.univ_nonempty : (Finset.univ : Finset (Fin 4)).Nonempty) (fun i => A i ω) 2 (by norm_num)
    simp only [ENNReal.rpow_two, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] at hpow
    norm_num only [show (4 : ℝ≥0∞) ^ 2 = 16 by norm_num] at hpow
    calc
      _ ≤ I ω * (16 * ∑ i : Fin 4, (A i ω) ^ 2) :=
        mul_le_mul' le_rfl ((pow_le_pow_left' hmass 2).trans hpow)
      _ = _ := by rw [← Finset.sum_mul]; ring
  calc
    _ ≤ ∫⁻ ω, 16 * ∑ i : Fin 4, (A i ω) ^ 2 * I ω ∂P := lintegral_mono hpoint
    _ = _ := by
      have hm (i : Fin 4) : AEMeasurable (fun ω => A i ω ^ 2 * I ω) P := ((hA i).pow_const 2).mul hI
      rw [lintegral_const_mul' _ _ (by norm_num : (16 : ℝ≥0∞) ≠ ⊤),
        lintegral_finsetSum' Finset.univ (fun i _ => hm i)]
      rfl

end DOZZ.Proofs
