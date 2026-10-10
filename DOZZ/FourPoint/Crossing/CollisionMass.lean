/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.MassContinuity
public import DOZZ.Correlations.Analytic.CoulombMassPositiveFinite
public import DOZZ.GMC.SharpMoments.SeibergMomentBound
public import DOZZ.GMC.SharpMoments.MomentConvergence
import Mathlib.Tactic

/-! # The zero-channel collision mass throughout the strict Seiberg domain -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- No upper bound of `2/γ` on the first charge is needed for the order-zero
collision limit. An almost surely finite unshifted three-point mass dominates. -/
theorem crossing_collision_mass_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (a b c : ℝ) (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 0)) (hz1 : ∀ n, ‖z n‖ ≤ 1) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n => coulombMass γ (M ω) ![-γ / 2, a, b] ![z n, 0, 1] c)
      atTop (𝓝 (coulombMass γ (M ω) ![-γ / 2, a, b] ![0, 0, 1] c)) := by
  have hi : Function.Injective (![0, 1] : Fin 2 → ℂ) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hq : ∀ j : Fin 2, (![a, b] : Fin 2 → ℝ) j < Q γ := by
    intro j
    fin_cases j
    · exact ha
    · exact hb
  have hn : ∀ᵐ ω ∂P, ∀ n, M ω {z n} = 0 :=
    ae_all_iff.mpr fun n => gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (z n)
  filter_upwards [coulomb_mass_pos_finite_ae P X hX γ hγ hγ2 M hM
    ![0, 1] hi ![a, b] c hq hc,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1, hn] with ω hf h0 h1 hnω
  exact crossing_coulombMass_tendsto_seq (M ω) γ a b c z hz hz1 h0 h1 hnω hf.2

/-- The unrooted collision masses are finite almost surely, including at the
coincident configuration where generic injective-root lemmas do not apply. -/
theorem crossing_collision_mass_finite_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (a b c : ℝ) (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) ![-γ / 2, a, b] ![z, 0, 1] c ≠ ⊤ := by
  have hi : Function.Injective (![0, 1] : Fin 2 → ℂ) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  have hq : ∀ j : Fin 2, (![a, b] : Fin 2 → ℝ) j < Q γ := by
    intro j
    fin_cases j
    · exact ha
    · exact hb
  filter_upwards [coulomb_mass_pos_finite_ae P X hX γ hγ hγ2 M hM
    ![0, 1] hi ![a, b] c hq hc,
    gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z] with ω hf hatom
  exact (lt_of_le_of_lt (crossing_coulombMass_le (M ω) γ a b c z hz hatom)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2.lt_top)).ne

end DOZZ.Proofs
