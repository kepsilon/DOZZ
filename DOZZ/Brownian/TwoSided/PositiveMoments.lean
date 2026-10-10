/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.Moments

/-! Uniform Brownian block envelopes and positive reflection moments across charge ranges. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The negative endpoint uses the smallest charge, while the unit oscillation uses the
largest charge. Hölder then gives one geometric envelope for the entire charge range. -/
theorem twosided_conditioned_block_envelope_uniform
    (θ₀ Θ ν₀ N : ℝ) (hθ₀ : 0 < θ₀) (hν₀ : 0 < ν₀) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧
      ∀ θ : ℝ, θ₀ ≤ θ → θ ≤ Θ → ∀ ν : ℝ, ν₀ ≤ ν → ν ≤ N →
        ∀ Q : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν Q → ∀ n : ℕ,
          (∫⁻ p, positiveBlockEnvelope θ n p ∂Q) ≤
            ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / (5 / 4 : ℝ)) *
              C ^ (((5 / 4 : ℝ) - 1) / (5 / 4 : ℝ)) := by
  let r : ℝ := 5 / 4
  have hr : 1 < r := by norm_num [r]
  have hr0 : 0 < r := by norm_num [r]
  obtain ⟨K, c, hK, hc, hEval⟩ := isNegativeConditionedBrownianLaw_exp_eval_le_exp
    (ν₂ := N) hν₀ (mul_pos hr0 hθ₀)
  obtain ⟨C, hC, hOsc⟩ := isNegativeConditionedBrownianLaw_unitIncrement_exp_le
    (r / (r - 1) * max Θ 0) N (by positivity)
  refine ⟨K, c, hK, hc, C, hC, ?_⟩
  intro θ hθ₀θ hθΘ ν hν₀ν hνN Q hQ n
  have hθ : 0 < θ := lt_of_lt_of_le hθ₀ hθ₀θ
  have hE : (∫⁻ p, ENNReal.ofReal (Real.exp (r * θ * p (n : ℝ≥0))) ∂Q) ≤
      ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) := by
    apply le_trans _ (hEval ν hν₀ν hνN Q hQ n)
    apply lintegral_mono_ae
    filter_upwards [isNegativeConditionedBrownianLaw_ae_nonpos hQ] with p hp
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_left hθ₀θ hr0.le) (hp n)
  have hO : (∫⁻ p, ENNReal.ofReal (Real.exp (r / (r - 1) * θ *
      brownianUnitNorm (brownianShiftPath n p))) ∂Q) ≤ C := by
    apply le_trans _ (hOsc ν hνN Q hQ n)
    apply lintegral_mono
    intro p
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact mul_le_mul_of_nonneg_left (hθΘ.trans (le_max_left _ _))
      (div_nonneg hr0.le (sub_pos.mpr hr).le)
  exact (positiveBlockEnvelope_lintegral_le Q θ r hθ.le hr n).trans
    (mul_le_mul' (ENNReal.rpow_le_rpow hE (one_div_nonneg.mpr hr0.le))
      (ENNReal.rpow_le_rpow hO (div_nonneg (sub_pos.mpr hr).le hr0.le)))

/-- One lateral unit moment and uniform positive parameter bounds give a common full
two-sided moment. The same lateral measure is used on both halves. -/
theorem twosided_positive_moment_uniform_from_lateral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν : Set ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (q γ₀ G ν₀ N : ℝ) (hq : 0 < q) (hγ₀ : 0 < γ₀) (hν₀ : 0 < ν₀)
    (hγbound : ∀ γ ∈ Kγ, γ₀ ≤ γ ∧ γ ≤ G)
    (hνbound : ∀ ν ∈ Kν, ν₀ ≤ ν ∧ ν ≤ N)
    (L : ℝ≥0∞) (hL : L < ⊤)
    (hUnit : ∀ γ ∈ Kγ, (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ q ∂P) ≤ L) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) (Z γ) ω) q ∂P) ≤ C := by
  let r : ℝ := 5 / 4
  have hr0 : 0 < r := by norm_num [r]
  have he : 0 ≤ (r - 1) / r := by norm_num [r]
  obtain ⟨K, c, hK, hc, C, hC, hEnvelope⟩ := twosided_conditioned_block_envelope_uniform
    (q * γ₀) (q * G) ν₀ N (mul_pos hq hγ₀) hν₀
  let g : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r)
  have hSum : halfLineBlockBound q L g < ⊤ := by
    refine halfLineBlockBound_lt_top hq hL (fun _ => ?_) (fun _ => ?_)
    · exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC hr0 he
    · simp_rw [g, exp_envelope_rpow_eq K c r ((r - 1) / r) q C hr0 hq]
      exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC (mul_pos hr0 hq)
        (div_nonneg he hq.le)
  refine ⟨3 ^ q * (halfLineBlockBound q L g + halfLineBlockBound q L g),
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq.le (by norm_num))
      (ENNReal.add_lt_top.mpr ⟨hSum, hSum⟩), ?_⟩
  intro γ hγ ν hν
  obtain ⟨hB, hZ, hi⟩ := hData γ hγ ν hν
  have hγp : 0 < γ := lt_of_lt_of_le hγ₀ (hγbound γ hγ).1
  apply twoSidedReflectionMass_rpow_lintegral_le_blockBound P γ q hγp.le hq (B ν) (Z γ)
    (aemeasurable_of_twoSidedConditioned hB) hZ.2.2.2.1 hZ.2.2.2.2.1
    (lateralGMC_singleton_ae P γ (Z γ) hZ 0) hi L
    (fun a => (lateralGMC_Icc_unit_moment_le P γ q (Z γ) hZ a).trans (hUnit γ hγ)) g
  · intro n
    rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.1.1]
    exact hEnvelope (q * γ) (mul_le_mul_of_nonneg_left (hγbound γ hγ).1 hq.le)
      (mul_le_mul_of_nonneg_left (hγbound γ hγ).2 hq.le) ν
      (hνbound ν hν).1 (hνbound ν hν).2 _ hB.1.2 n
  · intro n
    rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.2.1.1]
    exact hEnvelope (q * γ) (mul_le_mul_of_nonneg_left (hγbound γ hγ).1 hq.le)
      (mul_le_mul_of_nonneg_left (hγbound γ hγ).2 hq.le) ν
      (hνbound ν hν).1 (hνbound ν hν).2 _ hB.2.1.2 n

end DOZZ.Proofs
