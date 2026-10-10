/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionNestedConfiguration
public import DOZZ.FourPoint.RetainedAnnuliWeighted

/-! Joint inverse bounds in the literal selected fusion disks. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The physical two-scale fusion estimate, with constants before orders, scales, centers,
candidate choices and positive deterministic lower weights. -/
theorem fusion_retained_physical_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (B r₀ A : ℝ) (hB : 0 ≤ B) (hr₀ : 0 < r₀) (hr₀8 : r₀ ≤ 1 / 8) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b s : ℝ), 0 ≤ a → a ≤ A → 0 ≤ b → b ≤ A →
      0 ≤ s → s ≤ A → ∀ z : ℂ, ‖z‖ ≤ B → ∀ r t : ℝ,
        0 < r → 0 < t → 100 * r ≤ t → t ≤ r₀ → ∀ j k : Fin 5,
          ∀ (I : Ω → ℝ≥0∞) (wA wB wD : ℝ), 0 < wA → 0 < wB → 0 < wD →
            (∀ ω, ENNReal.ofReal wA * M ω
              (Metric.ball (z + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) ≤ I ω) →
            (∀ ω, ENNReal.ofReal wB * M ω
              (Metric.ball (z + (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)) (t / 100)) ≤ I ω) →
            (∀ ω, ENNReal.ofReal wD * M ω
              (Metric.ball (z + (((12 + (k.val : ℝ) / 5) * r₀ : ℝ) : ℂ)) (r₀ / 100)) ≤ I ω) →
            (∫⁻ ω, I ω ^ (-(a + b + s)) ∂P) ≤
              ENNReal.ofReal (C * (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) *
                t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
                (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  let d : ℝ := min r₀ (1 / 4)
  have hd : 0 < d := lt_min hr₀ (by norm_num)
  obtain ⟨C₀, hC₀, hbound⟩ := weighted_nested_retained_inverse_bound
    P X hX γ hγ hγ2 M hM (B + 14 * r₀) (3 / 4) (6 * r₀) (1 / 800)
    (r₀ / 100) d A (by positivity) (by norm_num) (by norm_num) (by positivity)
    (by norm_num) (by norm_num) (by positivity) (by linarith only [hr₀8]) hd hA
  let K : ℝ := (1 / 800 : ℝ) ^ (γ * Q γ * (-A) - γ ^ 2 * A ^ 2 / 2)
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨C₀ * K, mul_pos hC₀ hK, ?_⟩
  intro a b s ha haA hb hbA hs hsA z hz r t hr ht hrt ht0 j k I wA wB wD hwA hwB hwD hlA hlB hlD
  let w : ℂ := z + (((12 + (k.val : ℝ) / 5) * r₀ : ℝ) : ℂ)
  have hkn : (k.val : ℝ) ≤ 4 := by exact_mod_cast (show k.val ≤ 4 by omega)
  have hkn0 : 0 ≤ (k.val : ℝ) := Nat.cast_nonneg _
  have hwn : ‖w‖ ≤ B + 14 * r₀ := by
    have hh := norm_add_le z (((12 + (k.val : ℝ) / 5) * r₀ : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at hh
    dsimp only [w]
    nlinarith only [hh, hz, hkn, hr₀]
  have hz' : ‖z‖ ≤ B + 14 * r₀ := by linarith only [hz, hr₀]
  obtain ⟨hρ, hρ8, hu, hv, hsep⟩ := fusion_normalized_disks r t d hr ht hrt
    (min_le_right _ _) j
  have hc : 0 < 8 * t := by positivity
  have hc1 : 8 * t ≤ 1 := by linarith only [ht0, hr₀8]
  have hcR : (8 * t) * (3 / 4) ≤ 6 * r₀ := by linarith only [ht0]
  have hgap := fusion_fixed_disk_gap z r₀ d hr₀ (min_le_left _ _) k
  have heq := fusion_normalized_disk_eq z r t ht j
  have hlA' : ∀ ω, ENNReal.ofReal wA * M ω
      (Metric.ball (z + (8 * t) • (((9 / 16 : ℝ) * (r / t) : ℝ) : ℂ))
        ((8 * t) * ((r / t) / 800))) ≤ I ω := by simpa only [heq.1] using hlA
  have hlB' : ∀ ω, ENNReal.ofReal wB * M ω
      (Metric.ball (z + (8 * t) • (((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ))
        ((8 * t) * (1 / 800))) ≤ I ω := by simpa only [heq.2] using hlB
  have hh := hbound a b s ha haA hb hbA hs hsA z w hz' hwn hgap (8 * t) hc hc1 hcR
    (((9 / 16 : ℝ) * (r / t) : ℝ) : ℂ) (((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ)
    ((r / t) / 800) hρ hρ8 hu hv hsep I wA wB wD hwA hwB hwD hlA' hlB' hlD
  have hξ : γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2 ≤ 0 := by
    simpa using inverse_scale_exponent_antitone γ 0 (a + b) hγ (by norm_num) (add_nonneg ha hb)
  have htScale := Real.rpow_le_rpow_of_nonpos ht (show t ≤ 8 * t by linarith only [ht]) hξ
  have hρScale : ((r / t) / 800) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) ≤
      K * (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) := by
    rw [show (r / t) / 800 = (1 / 800 : ℝ) * (r / t) by ring,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 800) (div_pos hr ht).le]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
        (inverse_scale_exponent_antitone γ a A hγ ha haA)) (Real.rpow_pos_of_pos (div_pos hr ht) _).le
  refine hh.trans (ENNReal.ofReal_le_ofReal ?_)
  have hp : 0 ≤ C₀ * (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) := by positivity
  have hbnd := mul_le_mul_of_nonneg_left
    (mul_le_mul htScale hρScale (Real.rpow_pos_of_pos (by positivity) _).le
      (Real.rpow_pos_of_pos ht _).le) hp
  convert hbnd using 1 <;> ring

end DOZZ.Proofs
