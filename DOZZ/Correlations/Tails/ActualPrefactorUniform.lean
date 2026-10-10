/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CompleteEnvelopeUniform
public import DOZZ.Correlations.Tails.OffCenterPinLaw

/-! Uniform positive moments of the literal independent pin prefactor. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem actual_prefactor_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (K : Set ℂ) (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    (γ b R : ℝ) (hb : 0 ≤ b) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ f : ℝ, 0 ≤ f → f ≤ b →
      ∀ r : ℝ, 0 < r → r ≤ R →
        (∫⁻ ω, ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*
          Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))^r ∂P) ≤ C := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨C,hC,hbound⟩ := complete_envelope_moment_uniform_compact P
    K hK hz γ b 0 R hb le_rfl hR
  refine ⟨C,hC,?_⟩
  intro z hzk f hf hfb r hr hrR
  have hN := offCenter_pin_law P X Xc hX hc z (hz z hzk)
  have hm : (∫ ω, Xc ω z 0 ∂P) = 0 := by
    simpa only [integral_id_gaussianReal] using hN.integral_eq
  have hv : variance (fun ω => Xc ω z 0) P = 2*Real.log ‖z‖ := by
    simpa only [variance_id_gaussianReal,
      Real.coe_toNNReal _ (offCenter_pin_variance_pos z (hz z hzk)).le] using hN.variance_eq
  have h := hbound z hzk _ _ hN.hasGaussianLaw hN.hasGaussianLaw hm hm hv hv r hr hrR
  apply le_trans (lintegral_mono fun ω => ?_) h
  apply ENNReal.rpow_le_rpow _ hr.le
  apply ENNReal.ofReal_le_ofReal
  have hn : ‖z‖^(-4 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hz z hzk]) (by norm_num)
  have hD : pinCorrectionEnvelope z γ (Xc ω z 0) (Xc ω z 0) = γ^2 := by
    unfold pinCorrectionEnvelope
    simp only [sub_self,abs_zero,mul_zero,zero_add]
  simp only [zero_mul,add_zero,hD]
  have he : 1 ≤ Real.exp (γ^2+4) := Real.one_le_exp_iff.mpr (by positivity)
  have hfb' : f*‖z‖^(-4 : ℝ) ≤ b :=
    (mul_le_of_le_one_right hf hn).trans hfb
  have hbb : b ≤ b*Real.exp (γ^2+4) := le_mul_of_one_le_right hb he
  calc
    _ ≤ b*Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖) :=
      mul_le_mul_of_nonneg_right hfb' (Real.exp_nonneg _)
    _ ≤ (b*Real.exp (γ^2+4))*Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖) :=
      mul_le_mul_of_nonneg_right hbb (Real.exp_nonneg _)
    _ = _ := mul_comm _ _


end DOZZ.Proofs
