/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionNestedConfiguration
public import DOZZ.FourPoint.RetainedAnnuliUniformOrders

/-! A single retained fusion scale and the separated fixed disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The one-scale retained estimate supplies comparable-scale branches of fusion. -/
theorem fusion_single_scale_physical_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (B r₀ A : ℝ) (hB : 0 ≤ B) (hr₀ : 0 < r₀) (hr₀8 : r₀ ≤ 1 / 8) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a s : ℝ), 0 ≤ a → a ≤ A → 0 ≤ s → s ≤ A →
      ∀ z : ℂ, ‖z‖ ≤ B → ∀ t : ℝ, 0 < t → t ≤ r₀ → ∀ j k : Fin 5,
        ∀ (I : Ω → ℝ≥0∞) (wA wD : ℝ), 0 < wA → 0 < wD →
          (∀ ω, ENNReal.ofReal wA * M ω
            (Metric.ball (z + (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)) (t / 100)) ≤ I ω) →
          (∀ ω, ENNReal.ofReal wD * M ω
            (Metric.ball (z + (((12 + (k.val : ℝ) / 5) * r₀ : ℝ) : ℂ)) (r₀ / 100)) ≤ I ω) →
          (∫⁻ ω, I ω ^ (-(a + s)) ∂P) ≤
            ENNReal.ofReal (C * (wA ^ (-a) * wD ^ (-s)) *
              t ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  let L : ℝ := B + 14 * r₀
  obtain ⟨Cb, hCb, hball⟩ := ball_inverse_moment_uniform_orders P X hX γ hγ hγ2 M hM
    L A (by dsimp only [L]; positivity) hA
  let ξ : ℝ := γ * Q γ * (-A) - γ ^ 2 * A ^ 2 / 2
  let K : ℝ := Real.exp (γ ^ 2 * max 0 (Real.log (1 / r₀) + gmcCircleChartRemainder L) / 2 *
    ((2 * A) ^ 2 + 2 * A))
  let C : ℝ := K * Cb ^ 2 * (1 / 100 : ℝ) ^ ξ * (r₀ / 100) ^ ξ
  have hC : 0 < C := by dsimp only [C, K]; positivity
  refine ⟨C, hC, ?_⟩
  intro a s ha haA hs hsA z hz t ht ht0 j k I wA wD hwA hwD hlA hlD
  let u : ℂ := z + (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)
  let w : ℂ := z + (((12 + (k.val : ℝ) / 5) * r₀ : ℝ) : ℂ)
  have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hj4 : (j.val : ℝ) ≤ 4 := by exact_mod_cast (show j.val ≤ 4 by omega)
  have hk0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hk4 : (k.val : ℝ) ≤ 4 := by exact_mod_cast (show k.val ≤ 4 by omega)
  have huL : ‖u‖ + t / 100 ≤ L := by
    have hh := norm_add_le z (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hh
    dsimp only [u, L]
    nlinarith only [hh, hz, hj4, ht, ht0, hr₀]
  have hwL : ‖w‖ + r₀ / 100 ≤ L := by
    have hh := norm_add_le z (((12 + (k.val : ℝ) / 5) * r₀ : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hh
    dsimp only [w, L]
    nlinarith only [hh, hz, hk4, hr₀]
  have hgap : t / 100 + r₀ / 100 + r₀ ≤ ‖u - w‖ := by
    have he : u - w = ((((4 + (j.val : ℝ) / 5) * t -
        (12 + (k.val : ℝ) / 5) * r₀ : ℝ)) : ℂ) := by dsimp only [u, w]; push_cast; abel
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    have hn : (4 + (j.val : ℝ) / 5) * t - (12 + (k.val : ℝ) / 5) * r₀ < 0 := by
      nlinarith only [hj4, hk0, ht, ht0, hr₀]
    rw [abs_of_neg hn]
    nlinarith only [hj4, hk0, ht, ht0, hr₀]
  have hfinite (ω : Ω) (U : Set ℂ) : M ω U ≠ ⊤ := by
    let _ := hM.1 ω
    exact measure_ne_top _ _
  have halloc := retained_moment_allocation P I
    (fun ω => M ω (Metric.ball u (t / 100))) (fun ω => M ω (Metric.ball w (r₀ / 100)))
    (fun ω => hfinite ω _) (fun ω => hfinite ω _) wA wD a s hwA hwD ha hs hlA hlD
  have ht8 : t / 100 ≤ 1 / 8 := by linarith only [ht0, hr₀8]
  have hr8 : r₀ / 100 ≤ 1 / 8 := by linarith only [hr₀8]
  have hjoint := joint_retained_annuli_inverse_bound P X hX γ hγ hγ2 M hM
    u w (t / 100) (r₀ / 100) L r₀ a s (by positivity) (by positivity) ht8 hr8
    (by dsimp only [L]; positivity) hr₀ huL hwL hgap ha hs
  have hcost := inverse_gaussian_bill_mono γ
    (max 0 (Real.log (1 / r₀) + gmcCircleChartRemainder L)) (a + s) (2 * A)
    (le_max_left _ _) (add_nonneg ha hs) (by linarith only [haA, hsA])
  have hma := hball a ha haA u (by linarith only [huL, ht]) (t / 100) (by positivity) ht8
  have hmd := hball s hs hsA w (by linarith only [hwL, hr₀]) (r₀ / 100) (by positivity) hr8
  have hma' : gmcMassMoment P M (Metric.ball u (t / 100)) (-a) ≤
      ENNReal.ofReal (Cb * (1 / 100 : ℝ) ^ ξ * t ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
    refine hma.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [show t / 100 = (1 / 100 : ℝ) * t by ring, Real.mul_rpow (by norm_num) ht.le]
    have hpow : (1 / 100 : ℝ) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) ≤ (1 / 100 : ℝ) ^ ξ :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (inverse_scale_exponent_antitone γ a A hγ ha haA)
    have hm := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_pos_of_pos ht (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)).le) hCb.le
    convert hm using 1
    ring
  have hmd' : gmcMassMoment P M (Metric.ball w (r₀ / 100)) (-s) ≤
      ENNReal.ofReal (Cb * (r₀ / 100) ^ ξ) := by
    refine hmd.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge (by positivity)
      (by linarith only [hr₀8]) (inverse_scale_exponent_antitone γ s A hγ hs hsA)) hCb.le
  simp only [add_assoc] at hjoint hcost
  have hh := halloc.trans (mul_le_mul' le_rfl
    (hjoint.trans (mul_le_mul' (mul_le_mul' hcost hma') hmd')))
  refine hh.trans_eq ?_
  simp only [← mul_assoc]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [C]
  ring

end DOZZ.Proofs
