/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ThresholdENNReal

/-! A concrete shrinking threshold yields a positive geometric rate. -/

@[expose] public section
open scoped ENNReal
namespace DOZZ.Proofs

/-- Any positive annular moment decay rate, finite envelopes, and strict Hölder exponent yield
an exponentially decaying threshold bound. The chosen threshold is `exp(-rate*r/(2*m))`. -/
theorem threshold_finite_constants (D B C : ℝ≥0∞)
    (hD : D ≠ ⊤) (hB : B ≠ ⊤) (hC : C ≠ ⊤)
    (rate m q : ℝ) (hrate : 0 < rate) (hm : 0 < m) (hq : 1 < q) :
    ∃ K κ : ℝ, 0 ≤ K ∧ 0 < κ ∧ ∀ r : ℝ, 0 ≤ r →
      ENNReal.ofReal (Real.exp (-(rate / (2 * m)) * r)) * D +
        B * ((ENNReal.ofReal (Real.exp (-rate * r)) * C) /
          (ENNReal.ofReal (Real.exp (-(rate / (2 * m)) * r))) ^ m) ^
            (1 / (q / (q - 1))) ≤ ENNReal.ofReal (K * Real.exp (-κ * r)) := by
  let τ := rate / (2 * m)
  let h := 1 / (q / (q - 1))
  have hτ : 0 < τ := div_pos hrate (mul_pos (by norm_num) hm)
  have hh : 0 < h := one_div_pos.mpr (div_pos (by linarith) (by linarith))
  have hres : rate - τ * m = rate / 2 := by
    dsimp only [τ]
    field_simp
    ring
  let κ := min τ ((rate - τ * m) * h)
  have hκ : 0 < κ := lt_min hτ (by rw [hres]; positivity)
  let K := D.toReal + B.toReal * C.toReal ^ h
  have hK : 0 ≤ K := add_nonneg ENNReal.toReal_nonneg
    (mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  refine ⟨K, κ, hK, hκ, fun r hr => ?_⟩
  have hb := threshold_ennreal_bound D.toReal B.toReal C.toReal rate τ m h r
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hh.le hr
  simpa only [ENNReal.ofReal_toReal hD, ENNReal.ofReal_toReal hB,
    ENNReal.ofReal_toReal hC] using hb

end DOZZ.Proofs
