/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment

/-! Almost sure positivity and finiteness needed for varying real exponents. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Subcritical individual charges give a positive finite Coulomb mass almost surely, independently
of the sign of the Seiberg exponent. -/
theorem coulomb_mass_pos_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (hz : Function.Injective z) (α : Fin N → ℝ) (αinf : ℝ)
    (ha : ∀ k, α k < Q γ) (hi : αinf < Q γ) :
    ∀ᵐ ω ∂P, coulombMass γ (M ω) α z αinf ≠ 0 ∧
      coulombMass γ (M ω) α z αinf ≠ ⊤ := by
  let := hX.1
  have h4 : (0 : ℝ) < 4 / γ ^ 2 := by positivity
  have hi0 : 0 < 2 / γ * (Q γ - αinf) := mul_pos (by positivity) (sub_pos.mpr hi)
  have hk0 : ∀ k, 0 < 2 / γ * (Q γ - α k) :=
    fun k => mul_pos (by positivity) (sub_pos.mpr (ha k))
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (4 / γ ^ 2) := Ioo_mem_nhdsGT h4
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (2 / γ * (Q γ - αinf)) := Ioo_mem_nhdsGT hi0
  have e3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ k, t ∈ Ioo 0 (2 / γ * (Q γ - α k)) :=
    eventually_all.mpr fun k => Ioo_mem_nhdsGT (hk0 k)
  obtain ⟨t, ht⟩ := (e1.and (e2.and e3)).exists
  have hm := gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf
  have hfin := coulombMass_moment_lt_top_of_pos P X hX γ hγ hγ2 M hM z hz α αinf t
    ht.1.1 ht.1.2 (fun k => (ht.2.2 k).2) ht.2.1.2
  obtain ⟨hR, hzR⟩ := coulomb_exterior_radius_bounds z
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
    ENNReal.ofReal ((1 + 2 * ∑ j, ‖z j‖ + 2) ^ (-|γ * αinf|))
  have hc : c ≠ 0 := by
    have hs : 0 ≤ ∑ j, ‖z j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    exact mul_ne_zero
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hpos := gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM
    (((1 + 2 * ∑ j, ‖z j‖ + 1 : ℝ)) : ℂ) (1 / 8) (by norm_num)
  filter_upwards [ae_lt_top' (hm.pow_const t) hfin.ne, hpos] with ω hf hp
  constructor
  · exact (lt_of_lt_of_le (ENNReal.mul_pos hc hp.ne')
      (coulombMass_ge_exterior_ball (M ω) γ α z αinf hR hzR)).ne'
  · intro htop
    rw [htop, ENNReal.top_rpow_of_pos ht.1.1] at hf
    exact lt_irrefl _ hf

end DOZZ.Proofs
