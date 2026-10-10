/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedNegativeMoments
public import DOZZ.Correlations.Analytic.RetainedMomentLimit

/-! Real moment identification of the retained Coulomb cutoff. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Every strictly admissible fixed moment of the retained Coulomb cutoff converges to the
literal full Coulomb moment. Positive and negative powers use their respective proved envelopes. -/
theorem retained_coulomb_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (hz : Function.Injective z) (αinf p : ℝ)
    (hpbulk : p < 4 / γ ^ 2) (hproot : ∀ i, p < 2 / γ * (Q γ - α i))
    (hpinf : p < 2 / γ * (Q γ - αinf)) :
    Tendsto (fun n : ℕ => ∫⁻ ω,
      (∫⁻ x in retainedRegion z n, coulombWeight γ α z αinf x ∂M ω) ^ p ∂P)
      atTop (𝓝 (∫⁻ ω, coulombMass γ (M ω) α z αinf ^ p ∂P)) := by
  let : IsProbabilityMeasure P := hX.1
  let R := 1 + 2 * ∑ j, ‖z j‖
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  have hout : ∀ᶠ n : ℕ in atTop, R + 2 ≤ Real.exp (n : ℝ) :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (R + 2)
  obtain ⟨n0, hn0⟩ := hout.exists
  have hB := exterior_ball_subset_retainedRegion z R hR hzR n0
    (Nat.cast_nonneg _) hn0
  let f (n : ℕ) (ω : Ω) := ∫⁻ x in retainedRegion z ((n + n0 : ℕ) : ℝ),
    coulombWeight γ α z αinf x ∂M ω
  let g (ω : Ω) := coulombMass γ (M ω) α z αinf
  have hf (n : ℕ) : AEMeasurable (f n) P :=
    gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (measurable_coulombWeight γ α z αinf) _
      (retainedRegion_isOpen z ((n + n0 : ℕ) : ℝ)).measurableSet
  have horder : ∀ᵐ ω ∂P, ∀ n, f 0 ω ≤ f n ω ∧ f n ω ≤ g ω := by
    filter_upwards [] with ω n
    constructor
    · apply lintegral_mono_set
      exact retainedRegion_mono z (Nat.cast_le.mpr
        (by simpa only [zero_add] using Nat.le_add_left n0 n))
    · exact setLIntegral_le_lintegral _ _
  have hatoms : ∀ᵐ ω ∂P, ∀ i, M ω {z i} = 0 := ae_all_iff.mpr
    (fun i => gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM (z i))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hatoms] with ω hω
    simpa only [f, g, Function.comp_def, coulombMass_eq_lintegral_coulombWeight] using
      (retained_weighted_mass_tendsto (M ω) z hω
        (coulombWeight γ α z αinf)).comp (tendsto_add_atTop_nat n0)
  have hpos (hp : 0 ≤ p) : (∫⁻ ω, g ω ^ p ∂P) < ⊤ := by
    rcases eq_or_lt_of_le hp with hp0 | hp0
    · simp only [← hp0, ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one]
      exact ENNReal.one_lt_top
    · exact coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf p hp0
        hpbulk hproot hpinf
  have hneg (hp : p < 0) : (∫⁻ ω, f 0 ω ^ p ∂P) < ⊤ := by
    simpa only [f, zero_add] using
      retained_coulomb_mass_nonpos_moment_finite P X hX γ hγ hγ2 M hM α z αinf
        (retainedRegion z n0) R hR hzR hB p hp.le
  have ht := retained_mass_moment_limit P f g p hf horder hlim hpos hneg
  dsimp only [f, g] at ht
  exact (tendsto_add_atTop_iff_nat n0).mp ht

end DOZZ.Proofs
