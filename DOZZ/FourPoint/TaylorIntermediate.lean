/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorIntermediateScalar
public import DOZZ.FourPoint.TaylorLocalKernel
public import DOZZ.FourPoint.TaylorMixedMoments
public import DOZZ.FourPoint.TaylorExterior

/-! The actual intermediate Taylor region: local square reduction and sharp weighted moments. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Removing the near-root disk bounds the absolute denominator by d^{-1}. -/
theorem intermediate_numerator_bound {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) (ρ d : ℝ) (hd : 0 < d) :
    gammaHalfRootMajorantOn M γ α₁ α₂ α₃ ω z
      (Metric.ball 0 ρ \ Metric.ball z d) ≤ ENNReal.ofReal d⁻¹ *
        ∫⁻ x in Metric.ball 0 ρ \ Metric.ball z d,
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω := by
  calc
    _ ≤ ∫⁻ x in Metric.ball 0 ρ \ Metric.ball z d,
        ENNReal.ofReal d⁻¹ * ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω := by
      apply setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball)
      intro x hx
      have hdist : d ≤ ‖x - z‖ := by
        simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hx.2
      have hk := gammaHalfKernel_nonneg γ α₁ α₂ α₃ z x
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hd.le)]
      apply ENNReal.ofReal_le_ofReal
      have hh := div_le_div_of_nonneg_left hk hd hdist
      simpa only [div_eq_mul_inv, mul_comm] using hh
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The supplied-GMC intermediate square has its full Holder/radius exponent. The constant
precedes z, rho and the deleted near-root radius d. -/
theorem twoRooted_intermediate_physical_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p s q : ℝ) (hα₁ : α₁ < Q γ) (hp : 0 ≤ p)
    (hs : 0 < s) (hs2 : s ≤ 2) (hq : 1 < q)
    (hrange : q * s < min (4 / γ ^ 2) (2 / γ * (Q γ - α₁))) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 →
      ∀ z : ℂ, ‖z‖ ≤ ρ → ∀ d : ℝ, 0 < d →
        gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z
          (Metric.ball 0 ρ \ Metric.ball z d) ≤ ENNReal.ofReal
            (C * (d⁻¹) ^ 2 * ρ ^ ((γ ^ 2 / 2) * s +
              (γ * (Q γ - α₁) * (q * s) - γ ^ 2 * (q * s) ^ 2 / 2) / q)) := by
  obtain ⟨Cmix, hCmix, hmixed⟩ := weighted_ball_coulomb_mixed_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ p s q hα₁ hp hs hq hrange
  let E : ℝ := γ * (Q γ - α₁) * (q * s) - γ ^ 2 * (q * s) ^ 2 / 2
  let T : ℝ := (2 : ℝ) ^ (|γ * α₂| * s + (γ ^ 2 / 2) * s)
  let C : ℝ := T * Cmix
  have hT : 0 < T := by dsimp only [T]; positivity
  have hC : 0 < C := mul_pos hT hCmix
  refine ⟨C, hC, ?_⟩
  intro ρ hρ hρ4 z hz d hd
  have hρ2 : ρ ≤ 1 / 2 := hρ4.trans (by norm_num)
  let S : Set ℂ := Metric.ball 0 ρ \ Metric.ball z d
  let L : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in S, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω
  let I : Ω → ℝ≥0∞ := fun ω => coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃
  let W : Ω → ℝ≥0∞ := fun ω => weightedGmcBallMass γ (M ω) α₁ 0 ρ
  let w : ℝ := (2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2)
  have hw : 0 < w := by dsimp only [w]; positivity
  have hpoint : ∀ᵐ ω ∂P,
      (gammaHalfRootMajorantOn M γ α₁ α₂ α₃ ω z S) ^ 2 * I ω ^ (-p - 2) ≤
        ENNReal.ofReal ((d⁻¹) ^ 2 * w ^ s) * (W ω ^ s * I ω ^ (-p - s)) := by
    filter_upwards [gammaHalfMass_eq_coulombMass_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ z,
      gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ2 M hM 0] with ω hmass h0
    have hA := intermediate_numerator_bound M γ α₁ α₂ α₃ ω z ρ d hd
    have hLI : L ω ≤ I ω := by
      dsimp only [I]
      rw [← hmass]
      exact setLIntegral_le_lintegral _ _
    have hLW : L ω ≤ ENNReal.ofReal w * W ω :=
      (lintegral_mono_set Set.sdiff_subset).trans
        (gammaHalf_local_mass_bound γ α₁ α₂ α₃ z ρ hρ hρ2 hz (M ω) h0)
    exact intermediate_scalar_bound _ (L ω) (I ω) (W ω) d w p s hd hw hp hs hs2 hA hLI hLW
  have hconst : 0 ≤ (d⁻¹) ^ 2 * w ^ s := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hw.le _)
  have hbound := (lintegral_mono_ae hpoint).trans_eq
    (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
  have htotal := hbound.trans (mul_le_mul' le_rfl (hmixed z (hz.trans hρ4) ρ hρ hρ2))
  have hwscale : w ^ s = T * ρ ^ ((γ ^ 2 / 2) * s) := by
    dsimp only [w, T]
    rw [Real.mul_rpow (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by positivity) _),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul (by positivity : 0 ≤ 2 * ρ),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hρ.le, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  calc
    _ ≤ ENNReal.ofReal ((d⁻¹) ^ 2 * w ^ s) * ENNReal.ofReal (Cmix * ρ ^ (E / q)) := htotal
    _ = _ := by
      rw [← ENNReal.ofReal_mul hconst, hwscale]
      congr 1
      rw [Real.rpow_add hρ]
      dsimp only [C]
      ring

end DOZZ.Proofs
