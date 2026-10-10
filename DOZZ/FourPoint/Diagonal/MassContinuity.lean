/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.Mass
import DOZZ.FourPoint.BPZ.SoftMassDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Continuity at the colliding degenerate insertion. A fixed softened mass
dominates the real negative-insertion kernel near zero. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- In the half-unit disk, a fixed softened kernel dominates the unsoftened
negative insertion. Its reference point is separated from both fixed roots. -/
theorem diagonal_bpz_weight_bound
    (γ χ a b c : ℝ) (hγχ : 0 ≤ γ * χ) (z x : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ENNReal.ofReal (bpzSoftWeight γ χ a b c 0 z x) ≤
      ENNReal.ofReal (4 ^ |γ * χ / 2|) *
        ENNReal.ofReal (bpzSoftWeight γ χ a b c 1 (1 / 2) x) := by
  have he : 0 ≤ γ * χ / 2 := div_nonneg hγχ (by norm_num)
  have hzz : ‖(1 / 2 : ℂ) - z‖ ≤ 1 := by
    have h := norm_sub_le (1 / 2 : ℂ) z
    norm_num at h
    linarith
  have hplain : bpzSoftWeight γ χ a b c 0 z x ≤ bpzSoftWeight γ χ a b c 1 z x := by
    unfold bpzSoftWeight
    apply mul_le_mul_of_nonneg_right _ (bpzBaseWeight_nonneg x)
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), one_pow, add_zero]
    exact Real.rpow_le_rpow (Complex.normSq_nonneg _) (by linarith) he
  have hcmp := bpzSoft_rpow_le_of_norm_le_one (ε := 1) (by norm_num)
    (γ * χ / 2) hzz x
  have hcomp : bpzSoftWeight γ χ a b c 1 z x ≤
      4 ^ |γ * χ / 2| * bpzSoftWeight γ χ a b c 1 (1 / 2) x := by
    unfold bpzSoftWeight
    have hh := mul_le_mul_of_nonneg_right hcmp (bpzBaseWeight_nonneg (γ := γ)
      (χ := χ) (α₁ := a) (α₂ := b) (α₃ := c) x)
    simpa only [one_pow, div_one, one_add_one_eq_two,
      show (2 : ℝ) * 2 = 4 by norm_num, mul_assoc] using hh
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  exact ENNReal.ofReal_le_ofReal (hplain.trans hcomp)

/-- A finite softened reference mass gives continuity of the unsoftened mass at
zero, including the coincident insertion. -/
theorem diagonal_bpzMass_continuousAt_zero
    (γ χ a b c : ℝ) (hγχ : 0 ≤ γ * χ) (m : Measure ℂ)
    (hfinite : bpzMass γ χ a b c 1 m (1 / 2) < ⊤) :
    ContinuousAt (fun z : ℂ => bpzMass γ χ a b c 0 m z) 0 := by
  let bound : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (4 ^ |γ * χ / 2|) *
    ENNReal.ofReal (bpzSoftWeight γ χ a b c 1 (1 / 2) x)
  have hfin : ∫⁻ x, bound x ∂m ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinite.ne
  apply tendsto_lintegral_filter_of_dominated_convergence bound
  · exact Eventually.of_forall fun z => ENNReal.measurable_ofReal.comp
      (measurable_bpzSoftWeight 0 z)
  · have hnear : ∀ᶠ z : ℂ in 𝓝 0, ‖z‖ ≤ 1 / 2 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)]
        with z hz
      exact (show ‖z‖ < 1 / 2 by simpa only [Metric.mem_ball, dist_zero_right] using hz).le
    filter_upwards [hnear] with z hz
    exact ae_of_all m fun x => diagonal_bpz_weight_bound γ χ a b c hγχ z x hz
  · exact hfin
  · apply ae_of_all
    intro x
    have hbase : Continuous (fun z : ℂ => Complex.normSq (x - z) + (0 : ℝ) ^ 2) := by
      fun_prop
    have hcont : Continuous (fun z : ℂ => bpzSoftWeight γ χ a b c 0 z x) := by
      unfold bpzSoftWeight
      exact (hbase.rpow_const (fun _ => Or.inr (div_nonneg hγχ (by norm_num)))).mul
        continuous_const
    exact (ENNReal.continuous_ofReal.comp hcont).continuousAt.tendsto

end DOZZ.Proofs
