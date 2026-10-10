/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PowerTailBound

/-! Event comparison for the maximum-dependent retained amplitude in the one-insertion tail
estimate. -/

@[expose] public section
open MeasureTheory Set

namespace DOZZ.Proofs

/-- The retained amplitude is bounded above by the full one and, above the cut level,
bounded below by the fixed-cut amplitude. The excluded event is a marginal amplitude tail. -/
theorem truncated_williams_tail_sandwich
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) (P : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (A : ℝ × Ω → ℝ) (J Jc : Ω → ℝ) (hJc0 : ∀ ω, 0 ≤ Jc ω)
    (γ c x : ℝ) (hγ : 0 < γ)
    (hupper : ∀ᵐ q ∂μ.prod P, A q ≤ J q.2)
    (hlower : ∀ᵐ q ∂μ.prod P, c ≤ q.1 → Jc q.2 ≤ A q) :
    (μ.prod P).real {q | x < A q*Real.exp (γ*q.1)} ≤
        (μ.prod P).real {q | x < J q.2*Real.exp (γ*q.1)} ∧
      (μ.prod P).real {q | x < Jc q.2*Real.exp (γ*q.1)} -
        P.real {ω | x*Real.exp (-γ*c) < Jc ω} ≤
          (μ.prod P).real {q | x < A q*Real.exp (γ*q.1)} := by
  constructor
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hupper] with q hq
    intro he
    exact he.trans_le (mul_le_mul_of_nonneg_right hq (Real.exp_nonneg _))
  · let E := {q : ℝ × Ω | x < A q*Real.exp (γ*q.1)}
    let Ec := {q : ℝ × Ω | x < Jc q.2*Real.exp (γ*q.1)}
    let T := {ω | x*Real.exp (-γ*c) < Jc ω}
    have hinc : Ec ≤ᵐ[μ.prod P] E ∪ (univ ×ˢ T) := by
      filter_upwards [hlower] with q hq
      intro he
      by_cases hc : c ≤ q.1
      · exact Or.inl (he.trans_le (mul_le_mul_of_nonneg_right (hq hc) (Real.exp_nonneg _)))
      · have hm : q.1 < c := lt_of_not_ge hc
        have h : x < Jc q.2*Real.exp (γ*c) := he.trans_le
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hm.le hγ.le)) (hJc0 q.2))
        have hh := mul_lt_mul_of_pos_right h (Real.exp_pos (-γ*c))
        have hexp : γ*c+(-γ*c) = 0 := by ring
        rw [mul_assoc, ← Real.exp_add, hexp, Real.exp_zero, mul_one] at hh
        exact Or.inr ⟨mem_univ _, hh⟩
    have hprob : (μ.prod P).real Ec ≤ (μ.prod P).real (E ∪ (univ ×ˢ T)) :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hinc)
    have hu := measureReal_union_le (μ := μ.prod P) E (univ ×ˢ T)
    have ht : (μ.prod P).real (univ ×ˢ T) = P.real T := by
      rw [measureReal_prod_prod]
      simp only [Measure.real_def, measure_univ, ENNReal.toReal_one, one_mul]
    rw [ht] at hu
    linarith


end DOZZ.Proofs
