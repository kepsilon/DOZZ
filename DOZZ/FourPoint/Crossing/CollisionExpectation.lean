/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Crossing.CollisionMass
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! # Inverse expectations at the half-charge collision

A larger inverse order is uniformly bounded by the fixed-disk estimate
`coulombMass_moment_uniform_nonpos`. Vitali therefore applies to the almost sure mass
convergence, for every first charge below Q, including charges above 2/γ.
-/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- All inverse orders are uniformly bounded as the negative insertion moves. -/
theorem crossing_collision_inverse_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (a b c s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
      (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, a, b] ![z, 0, 1] c ^ s ∂P) ≤ C := by
  let A := |γ / 2| + |a| + |b| + |c|
  obtain ⟨C, hC, hbound⟩ := coulombMass_moment_uniform_nonpos
    P X hX γ hγ hγ2 M hM 3 2 (by norm_num) A s hs
  refine ⟨C, hC, ?_⟩
  intro z hz
  apply hbound ![z, 0, 1] ![-γ / 2, a, b] c s
  · intro j
    fin_cases j
    · change 2 * ‖z‖ ≤ 2
      linarith only [hz]
    · norm_num
    · norm_num
  · intro j
    fin_cases j
    · change |-γ / 2| ≤ A
      rw [neg_div, abs_neg]
      dsimp [A]
      linarith only [abs_nonneg a, abs_nonneg b, abs_nonneg c]
    · change |a| ≤ A
      dsimp [A]
      linarith only [abs_nonneg (γ / 2), abs_nonneg b, abs_nonneg c]
    · change |b| ≤ A
      dsimp [A]
      linarith only [abs_nonneg (γ / 2), abs_nonneg a, abs_nonneg c]
  · dsimp [A]
    linarith only [abs_nonneg (γ / 2), abs_nonneg a, abs_nonneg b]
  · exact le_rfl
  · exact hs

/-- Inverse moments converge at the collision along every sequence in the unit disk. -/
theorem crossing_collision_inverse_expectation_seq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (a b c : ℝ) (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ)
    (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 0)) (hz1 : ∀ n, ‖z n‖ ≤ 1)
    (s : ℝ) (hs : s < 0) :
    Tendsto (fun n => ∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, a, b] ![z n, 0, 1] c ^ s ∂P)
      atTop (𝓝 (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, a, b] ![0, 0, 1] c ^ s ∂P)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω => coulombMass γ (M ω) ![-γ / 2, a, b] ![z n, 0, 1] c
  let g : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) ![-γ / 2, a, b] ![0, 0, 1] c
  have hf : ∀ n, AEMeasurable (f n) P := fun n =>
    gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _
  have hg : AEMeasurable g P := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _
  have hgfin : ∀ᵐ ω ∂P, g ω ≠ ⊤ :=
    crossing_collision_mass_finite_ae P X hX γ hγ hγ2 M hM a b c ha hb hc 0 (by simp)
  have hfin : ∀ n, ∀ᵐ ω ∂P, f n ω ≠ ⊤ := fun n =>
    crossing_collision_mass_finite_ae P X hX γ hγ hγ2 M hM a b c ha hb hc (z n) (hz1 n)
  have hlim := crossing_collision_mass_ae P X hX γ hγ hγ2 M hM a b c ha hb hc z hz hz1
  have hreal : ∀ᵐ ω ∂P, Tendsto (fun n => (f n ω).toReal) atTop (𝓝 ((g ω).toReal)) := by
    filter_upwards [hlim, hgfin] with ω hω hωfin
    exact (ENNReal.continuousAt_toReal hωfin).tendsto.comp hω
  have hconv := tendstoInMeasure_of_tendsto_ae
    (fun n => (ENNReal.measurable_toReal.comp_aemeasurable (hf n)).aestronglyMeasurable) hreal
  obtain ⟨C, hC, hbound⟩ := crossing_collision_inverse_uniform
    P X hX γ hγ hγ2 M hM a b c (2 * s) (by linarith only [hs])
  exact lintegral_rpow_tendsto_of_uniform_moment P f g hf hg hfin hgfin hconv s (2 * s)
    (Or.inr ⟨by linarith only [hs], hs⟩) C hC.ne (fun n => hbound (z n) (hz1 n))

/-- Removing the unit-disk restriction by taking a sequence tail gives the full
collision limit of the inverse expectation. -/
theorem crossing_collision_inverse_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (a b c : ℝ) (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ) (s : ℝ) (hs : s < 0) :
    Tendsto (fun z => ∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, a, b] ![z, 0, 1] c ^ s ∂P)
      (𝓝 0) (𝓝 (∫⁻ ω, coulombMass γ (M ω) ![-γ / 2, a, b] ![0, 0, 1] c ^ s ∂P)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro z hz
  have hn : ∀ᶠ n in atTop, ‖z n‖ ≤ 1 := by
    have ht := continuous_norm.continuousAt.tendsto.comp hz
    simp only [norm_zero] at ht
    exact (ht.eventually_lt_const zero_lt_one).mono fun _ h => h.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hn
  apply (tendsto_add_atTop_iff_nat N).mp
  exact crossing_collision_inverse_expectation_seq P X hX γ hγ hγ2 M hM a b c ha hb hc
    (fun n => z (n + N)) (hz.comp (tendsto_add_atTop_nat N))
    (fun n => hN _ (Nat.le_add_left N n)) s hs

end DOZZ.Proofs
