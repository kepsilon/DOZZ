/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMomentBound

/-! # Moments of a quantity dominated by root, bulk and exterior pieces

A positive moment of a random variable bounded almost surely by a combination of finitely many
root pieces, a bulk piece and an exterior piece is bounded by the same combination of the moments
of the pieces, with factors `2 ^ t` and `N ^ t`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Positive moments of a quantity dominated by root, bulk and exterior pieces. -/
theorem lintegral_rpow_le_of_le_pieces
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    (Y : Ω → ℝ≥0∞) (Xr : Fin N → Ω → ℝ≥0∞) (B V : Ω → ℝ≥0∞) (a : Fin N → ℝ≥0∞) (b e : ℝ≥0∞)
    (hXr : ∀ k, AEMeasurable (Xr k) P) (hB : AEMeasurable B P) (hV : AEMeasurable V P)
    (hY : ∀ᵐ ω ∂P, Y ω ≤ ∑ k, a k * Xr k ω + b * B ω + e * V ω) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, Y ω ^ t ∂P ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * ∫⁻ ω, Xr k ω ^ t ∂P +
        b ^ t * ∫⁻ ω, B ω ^ t ∂P) + e ^ t * ∫⁻ ω, V ω ^ t ∂P) := by
  have hcard : ((Finset.univ : Finset (Fin N)).card : ℝ≥0∞) = N := by
    rw [Finset.card_univ, Fintype.card_fin]
  have hpt : ∀ᵐ ω ∂P, Y ω ^ t ≤
      2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t + b ^ t * B ω ^ t) +
        e ^ t * V ω ^ t) := by
    filter_upwards [hY] with ω hω
    calc Y ω ^ t ≤ ((∑ k, a k * Xr k ω + b * B ω) + e * V ω) ^ t :=
          ENNReal.rpow_le_rpow hω ht.le
      _ ≤ 2 ^ t * ((∑ k, a k * Xr k ω + b * B ω) ^ t + (e * V ω) ^ t) :=
          ennreal_add_rpow_le_two_rpow_mul _ _ ht.le
      _ ≤ 2 ^ t * (2 ^ t * ((∑ k, a k * Xr k ω) ^ t + (b * B ω) ^ t) + (e * V ω) ^ t) := by
          gcongr
          exact ennreal_add_rpow_le_two_rpow_mul _ _ ht.le
      _ ≤ 2 ^ t * (2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, (a k * Xr k ω) ^ t + (b * B ω) ^ t) +
            (e * V ω) ^ t) := by
          gcongr
          rw [← hcard]
          exact ennreal_finset_sum_rpow_le_card_rpow_sum_of_pos _ _ ht
      _ = _ := by simp only [ENNReal.mul_rpow_of_nonneg _ _ ht.le]
  have hXk : ∀ k ∈ (Finset.univ : Finset (Fin N)),
      AEMeasurable (fun ω => a k ^ t * Xr k ω ^ t) P := fun k _ =>
    aemeasurable_const.mul ((hXr k).pow_const t)
  have hS : AEMeasurable (fun ω => ∑ k, a k ^ t * Xr k ω ^ t) P :=
    Finset.aemeasurable_fun_sum _ hXk
  have hA : AEMeasurable (fun ω => (N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t) P :=
    aemeasurable_const.mul hS
  have hAB : AEMeasurable (fun ω => (N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t +
      b ^ t * B ω ^ t) P := hA.add (aemeasurable_const.mul (hB.pow_const t))
  have hLAB : AEMeasurable (fun ω => 2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t +
      b ^ t * B ω ^ t)) P := aemeasurable_const.mul hAB
  have hall : AEMeasurable (fun ω => 2 ^ t * ((N : ℝ≥0∞) ^ t * ∑ k, a k ^ t * Xr k ω ^ t +
      b ^ t * B ω ^ t) + e ^ t * V ω ^ t) P :=
    hLAB.add (aemeasurable_const.mul (hV.pow_const t))
  refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
  rw [lintegral_const_mul'' _ hall, lintegral_add_left' hLAB, lintegral_const_mul'' _ hAB,
    lintegral_add_left' hA, lintegral_const_mul'' _ hS, lintegral_finsetSum' _ hXk,
    lintegral_const_mul'' _ (hB.pow_const t), lintegral_const_mul'' _ (hV.pow_const t)]
  have hk : ∀ k, ∫⁻ ω, a k ^ t * Xr k ω ^ t ∂P = a k ^ t * ∫⁻ ω, Xr k ω ^ t ∂P := fun k =>
    lintegral_const_mul'' _ ((hXr k).pow_const t)
  simp only [hk]

/-- A power with exponent in `[0, tm]` is at most the `tm`th power of the larger of the base and
one. -/
theorem ennreal_rpow_le_max_one_rpow (x : ℝ≥0∞) {t tm : ℝ} (ht : 0 ≤ t) (htm : t ≤ tm) :
    x ^ t ≤ max 1 x ^ tm :=
  (ENNReal.rpow_le_rpow (le_max_right 1 x) ht).trans
    (ENNReal.rpow_le_rpow_of_exponent_le (le_max_left 1 x) htm)

end DOZZ.Proofs
