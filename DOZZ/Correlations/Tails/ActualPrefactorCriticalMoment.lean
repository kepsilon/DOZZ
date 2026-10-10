/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GaussianPrefactor
public import DOZZ.Correlations.Tails.OffCenterPinLaw

/-! The exact critical moment of the actual independent pin prefactor. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem actual_prefactor_critical_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ α f : ℝ) (hγ : γ ≠ 0) (hf : 0 < f) :
    (∫⁻ ω, ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
      Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))^(reflectionExponent γ α) ∂P).toReal =
        ‖z‖^(-4*α*(Q γ-α))*f^(reflectionExponent γ α) := by
  have hN := offCenter_pin_law P X Xc hX hc z hz
  have hm : (∫ ω, Xc ω z 0 ∂P) = 0 := by
    simpa only [integral_id_gaussianReal] using hN.integral_eq
  have hv : variance (fun ω => Xc ω z 0) P = 2*Real.log ‖z‖ := by
    simpa only [variance_id_gaussianReal,
      Real.coe_toNNReal _ (offCenter_pin_variance_pos z hz).le] using hN.variance_eq
  have hp : Measurable (fun ω => Xc ω z 0) :=
    (hc.1 0).comp (measurable_id.prodMk measurable_const)
  have he : Measurable (fun ω => ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
      Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))) :=
    (((hp.const_mul γ).sub_const _).exp.const_mul _).ennreal_ofReal
  have hfinite' (ω : Ω) : ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
      Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (mul_pos (mul_pos hf
      (Real.rpow_pos_of_pos (by linarith only [hz]) _)) (Real.exp_pos _))).ne'
  have hfinite (ω : Ω) : ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
      Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))^(reflectionExponent γ α) < ⊤ :=
    (ENNReal.rpow_ne_top_of_ne_zero (hfinite' ω) ENNReal.ofReal_ne_top).lt_top
  rw [← integral_toReal (he.aemeasurable.pow_const _) (ae_of_all _ hfinite)]
  simp_rw [← ENNReal.toReal_rpow,ENNReal.toReal_ofReal (mul_nonneg
    (mul_nonneg hf.le (Real.rpow_nonneg (norm_nonneg _) _)) (Real.exp_nonneg _))]
  have hzn : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt (by linarith only [hz] : 0 < ‖z‖))
  have hmoment := offCenter_prefactor_moment P (fun ω => Xc ω z 0)
    hN.hasGaussianLaw hm γ α f hγ hf z hzn hv
  have hvarterm : γ^2*variance (fun ω => Xc ω z 0) P/2 = γ^2*Real.log ‖z‖ := by rw [hv]; ring
  simpa only [hvarterm] using hmoment


end DOZZ.Proofs
