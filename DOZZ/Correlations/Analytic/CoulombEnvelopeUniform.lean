/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.EnvelopeMoments
public import DOZZ.Correlations.Analytic.LowerMassMoments
public import DOZZ.Correlations.Analytic.CoulombMassPositiveFinite
public import DOZZ.Correlations.Analytic.RetainedMassMoments
public import DOZZ.GMC.SharpMoments.SeibergUniform

/-! Uniform higher moments of the common envelope in the complex increment estimate. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Strict moment slack gives uniform higher moments of the actual Coulomb envelope. The
lower disk mass supplies the negative endpoint; the uniform Seiberg moment estimate
`coulombMass_moment_uniform_pos` supplies the positive endpoint. -/
theorem coulomb_envelope_uniform_moment
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z : Fin N → ℂ) (hz : Function.Injective z)
    (δ R Zs A g : ℝ) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hR : 1 ≤ R)
    (hZs : 0 ≤ Zs) (hg : 0 < g)
    (hsep : ∀ j k, j ≠ k → 2 * δ ≤ ‖z j - z k‖)
    (hzn : ∑ j, ‖z j‖ ≤ Zs) (hzR : ∀ i, 2 * ‖z i‖ ≤ R)
    (center : ℂ) (c : ℝ≥0∞) (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (lo hi q : ℝ) (hlo : lo ≤ 0) (hhi : 0 ≤ hi) (hq : 1 ≤ q) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (α : Fin N → ℝ) (αinf : ℝ),
      (∀ i, |α i| ≤ A) → |αinf| ≤ A → (∀ i, α i < Q γ) → αinf < Q γ →
      hi * q + g ≤ 4 / γ ^ 2 →
      (∀ i, hi * q + g ≤ 2 / γ * (Q γ - α i)) →
      hi * q + g ≤ 2 / γ * (Q γ - αinf) →
      (∫⁻ ω, ENNReal.ofReal ((c * M ω (Metric.ball center (1 / 8))).toReal ^ lo +
        (coulombMass γ (M ω) α z αinf).toReal ^ hi) ^ q ∂P) ≤ K := by
  let : IsProbabilityMeasure P := hX.1
  let L (ω : Ω) := c * M ω (Metric.ball center (1 / 8))
  have hLm : AEMeasurable L P := by
    simpa only [L, Pi.mul_def] using aemeasurable_const.mul
      (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
        Metric.isOpen_ball.measurableSet)
  have hLp : ∀ᵐ ω ∂P, L ω ≠ 0 ∧ L ω ≠ ⊤ := by
    have hb := open_mass_pos_finite_ae P X hX γ hγ hγ2 M hM
      (Metric.ball center (1 / 8)) Metric.isOpen_ball Metric.isBounded_ball
      (Metric.nonempty_ball.mpr (by norm_num))
    filter_upwards [hb] with ω hω
    exact ⟨mul_ne_zero hc hω.1, ENNReal.mul_ne_top hc' hω.2⟩
  let KL := ∫⁻ ω, L ω ^ (lo * q) ∂P
  have hKL : KL < ⊤ := scaled_disk_negative_moment
    P X hX γ hγ hγ2 M hM center (1 / 8) (by norm_num) le_rfl c hc hc'
      (lo * q) (mul_nonpos_of_nonpos_of_nonneg hlo (by linarith))
  obtain ⟨KU, hKU, hUbound⟩ : ∃ KU : ℝ≥0∞, KU < ⊤ ∧
      ∀ (α : Fin N → ℝ) (αinf : ℝ), (∀ i, |α i| ≤ A) → |αinf| ≤ A →
        hi * q + g ≤ 4 / γ ^ 2 →
        (∀ i, hi * q + g ≤ 2 / γ * (Q γ - α i)) →
        hi * q + g ≤ 2 / γ * (Q γ - αinf) →
        (∫⁻ ω, coulombMass γ (M ω) α z αinf ^ (hi * q) ∂P) ≤ KU := by
    by_cases hzero : hi = 0
    · refine ⟨1, ENNReal.one_lt_top, fun α αinf _ _ _ _ _ => ?_⟩
      simp only [hzero, zero_mul, ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one]
      exact le_rfl
    · obtain ⟨KU, hKU, hb⟩ := coulombMass_moment_uniform_pos
        P X hX γ hγ hγ2 M hM N hδ hδ8 hR (A := A) hZs hg
      refine ⟨KU, hKU, fun α αinf hα hinf hbulk hroot hinfty => ?_⟩
      exact hb z α αinf (hi * q) hsep hzn hzR hα hinf
        (mul_pos (lt_of_le_of_ne hhi (Ne.symm hzero)) (by linarith)) hbulk hroot hinfty
  refine ⟨(2 : ℝ≥0∞) ^ (q - 1) * (KL + KU), ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by linarith) (by norm_num))
    (ENNReal.add_lt_top.mpr ⟨hKL, hKU⟩), ?_⟩
  intro α αinf hα hinf ha hiinf hbulk hroot hinfty
  exact mass_envelope_moment_le P L
    (fun ω => coulombMass γ (M ω) α z αinf) hLm
    (gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM α z αinf) hLp
    (coulomb_mass_pos_finite_ae P X hX γ hγ hγ2 M hM z hz α αinf ha hiinf)
    lo hi q hq KL KU le_rfl (hUbound α αinf hα hinf hbulk hroot hinfty)

end DOZZ.Proofs
