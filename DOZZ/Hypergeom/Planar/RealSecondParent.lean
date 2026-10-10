/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RealSecondDifference
public import DOZZ.Hypergeom.Planar.TaylorParentScaling
public import DOZZ.Hypergeom.Planar.DifferenceScale

/-! Recover the normalized parent's real second derivative by dominated convergence. -/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- Generic real second-derivative identification for a scaled, integrable parent. -/
theorem realSecondDifferenceLimit_integral_eq (k β α A : ℝ)
    (hk : 0 < k) (hβ : k < β) (hβ₂ : β < 2) (F : ℂ → ℂ → ℝ)
    (hFint : ∀ z : ℂ, Integrable (F z) volume)
    (hFscale : ∀ z : ℂ, (∫ u : ℂ, F z u) = ‖z‖ ^ α * A)
    (hpoint : ∀ t : ℝ, t ≠ 0 → ∀ u : ℂ, u ≠ 0 →
      planarRealSecondDifferenceQuotient k β t u =
        (F (1 + (t : ℂ)) u + F (1 - (t : ℂ)) u - 2 * F 1 u) / t ^ 2) :
    (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) = α * (α - 1) * A := by
  let l : Filter ℝ := 𝓝[≠] (0 : ℝ)
  let P : ℝ → ℝ := fun t =>
    ((∫ u : ℂ, F (1 + (t : ℂ)) u) + (∫ u : ℂ, F (1 - (t : ℂ)) u) -
      2 * (∫ u : ℂ, F 1 u)) / t ^ 2
  let A₀ : ℝ := ∫ u : ℂ, F 1 u
  have hA₀ : A₀ = A := by
    simpa [A₀, norm_one, Real.one_rpow] using hFscale (1 : ℂ)
  have hParentEq : P =ᶠ[l]
      fun t => A₀ * normPowerRealSecondDifference α t 1 := by
    filter_upwards [] with t
    have h₁ := hFscale (1 + (t : ℂ))
    have h₂ := hFscale (1 - (t : ℂ))
    have h₀ := hFscale (1 : ℂ)
    change ((∫ u : ℂ, F (1 + (t : ℂ)) u) +
      (∫ u : ℂ, F (1 - (t : ℂ)) u) - 2 * (∫ u : ℂ, F 1 u)) / t ^ 2 = _
    rw [h₁, h₂, h₀, hA₀]
    simp only [normPowerRealSecondDifference, norm_one, Real.one_rpow]
    ring
  have hRad := norm_rpow_real_centered_difference_tendsto α (1 : ℂ) (by norm_num)
  have hRad' : Tendsto (fun t : ℝ => normPowerRealSecondDifference α t 1) l
      (𝓝 (α * (α - 1))) := by
    convert hRad using 1
    · simp [normPowerRealSecondDifference, norm_one, Real.one_rpow]
    · simp [norm_one, Real.one_rpow]
      ring
  have hScaled : Tendsto (fun t : ℝ => A₀ * normPowerRealSecondDifference α t 1) l
      (𝓝 (A₀ * (α * (α - 1)))) := tendsto_const_nhds.mul hRad'
  have hParentLimit : Tendsto P l (𝓝 (α * (α - 1) * A₀)) := by
    have h := hScaled.congr' hParentEq.symm
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  have hDct := planarRealSecondDifferenceQuotient_integral_tendsto k β
    hk hβ hβ₂
  have hQEq :
      (fun t : ℝ => ∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u) =ᶠ[l] P := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    let N : ℂ → ℝ := fun u => F (1 + (t : ℂ)) u + F (1 - (t : ℂ)) u - 2 * F 1 u
    have hplus := hFint (1 + (t : ℂ))
    have hminus := hFint (1 - (t : ℂ))
    have hzero := hFint 1
    have hN : Integrable N volume := by
      dsimp [N]
      exact (hplus.add hminus).sub (hzero.const_mul 2)
    have hpointAE : planarRealSecondDifferenceQuotient k β t =ᵐ[volume]
        fun u => (N u) / t ^ 2 := by
      filter_upwards [Measure.ae_ne volume (0 : ℂ)] with u hu
      exact hpoint t ht0 u hu
    have hsum : (∫ u : ℂ, N u) =
        (∫ u : ℂ, F (1 + (t : ℂ)) u) +
          (∫ u : ℂ, F (1 - (t : ℂ)) u) - 2 * (∫ u : ℂ, F 1 u) := by
      dsimp [N]
      calc
        (∫ u : ℂ, F (1 + (t : ℂ)) u + F (1 - (t : ℂ)) u -
            2 * F 1 u) =
            (∫ u : ℂ, F (1 + (t : ℂ)) u + F (1 - (t : ℂ)) u) -
              (∫ u : ℂ, 2 * F 1 u) := by
                exact integral_sub (hplus.add hminus) (hzero.const_mul 2)
        _ = (∫ u : ℂ, F (1 + (t : ℂ)) u) +
              (∫ u : ℂ, F (1 - (t : ℂ)) u) -
              2 * (∫ u : ℂ, F 1 u) := by
                rw [integral_add hplus hminus, integral_const_mul]
    have hIntEq : (∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u) =
        (∫ u : ℂ, N u) / t ^ 2 := by
      calc
        _ = ∫ u : ℂ, N u / t ^ 2 := integral_congr_ae hpointAE
        _ = (t ^ 2)⁻¹ * (∫ u : ℂ, N u) := by
          rw [show (fun u : ℂ => N u / t ^ 2) =
            fun u => (t ^ 2)⁻¹ * N u by funext u; simp [div_eq_mul_inv, mul_comm],
            integral_const_mul]
        _ = _ := by simp [div_eq_mul_inv, mul_comm]
    change (∫ u : ℂ, planarRealSecondDifferenceQuotient k β t u) =
      ((∫ u : ℂ, F (1 + (t : ℂ)) u) +
        (∫ u : ℂ, F (1 - (t : ℂ)) u) -
        2 * (∫ u : ℂ, F 1 u)) / t ^ 2
    rw [hIntEq, hsum]
  have hDctP := hDct.congr' hQEq
  have hlim := tendsto_nhds_unique hDctP hParentLimit
  rw [hA₀] at hlim
  simpa [mul_assoc, mul_left_comm, mul_comm] using hlim

private noncomputable def planarTaylorLinearCounterterm (u z : ℂ) : ℝ :=
  (z / u + star z / star u).re

private theorem planarTaylorLinearCounterterm_add (u z w : ℂ) :
    planarTaylorLinearCounterterm u (z + w) =
      planarTaylorLinearCounterterm u z + planarTaylorLinearCounterterm u w := by
  simp only [planarTaylorLinearCounterterm, add_div, star_add, Complex.add_re]
  ring

private theorem planarTaylorLinearCounterterm_centered (u : ℂ) (t : ℝ) :
    planarTaylorLinearCounterterm u (1 + (t : ℂ)) +
      planarTaylorLinearCounterterm u (1 - (t : ℂ)) -
        2 * planarTaylorLinearCounterterm u 1 = 0 := by
  have hsum : (1 : ℂ) + (t : ℂ) + (1 - (t : ℂ)) = 2 := by ring
  calc
    _ = planarTaylorLinearCounterterm u
          ((1 : ℂ) + (t : ℂ) + (1 - (t : ℂ))) -
        2 * planarTaylorLinearCounterterm u 1 := by
          rw [← planarTaylorLinearCounterterm_add]
    _ = planarTaylorLinearCounterterm u 2 -
        2 * planarTaylorLinearCounterterm u 1 := by rw [hsum]
    _ = 0 := by
      have htwo : (2 : ℂ) = 1 + 1 := by norm_num
      rw [htwo, planarTaylorLinearCounterterm_add]
      ring

private theorem planarTaylorRealSecondDifference_pointwise (k β t : ℝ) (u : ℂ)
    (hu : u ≠ 0) (ht : t ≠ 0) :
    planarRealSecondDifferenceQuotient k β t u =
      (DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
        DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u -
        2 * DOZZ.planarTaylorRemainder k β 1 u) / t ^ 2 := by
  have h₁ : u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) := by ring
  have h₂ : u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) := by ring
  have hlinear := planarTaylorLinearCounterterm_centered u t
  have hnum :
      (‖u - (1 + (t : ℂ))‖ ^ k - ‖u‖ ^ k +
          (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u (1 + (t : ℂ))) +
        (‖u - (1 - (t : ℂ))‖ ^ k - ‖u‖ ^ k +
          (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u (1 - (t : ℂ))) -
        2 * (‖u - 1‖ ^ k - ‖u‖ ^ k +
          (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u 1) =
      ‖(u - 1) + (t : ℂ)‖ ^ k + ‖(u - 1) - (t : ℂ)‖ ^ k -
        2 * ‖u - 1‖ ^ k := by
    rw [h₁, h₂]
    linear_combination (k / 2 * ‖u‖ ^ k) * hlinear
  rw [h₁, h₂] at hnum
  have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos (norm_pos_iff.mpr hu) β
  have hparent :
      DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
        DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u -
          2 * DOZZ.planarTaylorRemainder k β 1 u =
        (‖u - 1 + (t : ℂ)‖ ^ k + ‖u - 1 - (t : ℂ)‖ ^ k -
          2 * ‖u - 1‖ ^ k) / ‖u‖ ^ β := by
    unfold DOZZ.planarTaylorRemainder
    rw [h₁, h₂]
    let Nplus : ℝ := ‖u - 1 - (t : ℂ)‖ ^ k - ‖u‖ ^ k +
      (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u (1 + (t : ℂ))
    let Nminus : ℝ := ‖u - 1 + (t : ℂ)‖ ^ k - ‖u‖ ^ k +
      (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u (1 - (t : ℂ))
    let Nzero : ℝ := ‖u - 1‖ ^ k - ‖u‖ ^ k +
      (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u 1
    change (Nplus / ‖u‖ ^ β + Nminus / ‖u‖ ^ β -
        2 * (Nzero / ‖u‖ ^ β)) = _
    rw [← add_div, ← mul_div_assoc, ← sub_div]
    congr 1
  change ‖u‖ ^ (-β) *
      ((‖u - 1 + (t : ℂ)‖ ^ k + ‖u - 1 - (t : ℂ)‖ ^ k -
        2 * ‖u - 1‖ ^ k) / t ^ 2) = _
  rw [Real.rpow_neg (norm_nonneg u) β]
  rw [hparent]
  field_simp [hden.ne', ht]

theorem planarTaylor_real_second_derivative_relation (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      (2 + k - β) * (1 + k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
  let α : ℝ := 2 + k - β
  let A : ℝ := ∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u
  have hα : 0 < α := by dsimp [α]; linarith
  have hFint : ∀ z : ℂ, Integrable (DOZZ.planarTaylorRemainder k β z) volume :=
    integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
  have hFscale (z : ℂ) :
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) = ‖z‖ ^ α * A := by
    simpa [α, A] using
      planarTaylorRemainder_integral_scale_norm k β hk hβ hβ₂ z
  have hpoint : ∀ t : ℝ, t ≠ 0 → ∀ u : ℂ, u ≠ 0 →
      planarRealSecondDifferenceQuotient k β t u =
        (DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
          DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u -
          2 * DOZZ.planarTaylorRemainder k β 1 u) / t ^ 2 := by
    intro t ht u hu
    exact planarTaylorRealSecondDifference_pointwise k β t u hu ht
  have hresult := realSecondDifferenceLimit_integral_eq k β α A hk hβ hβ₂
    (DOZZ.planarTaylorRemainder k β) hFint hFscale hpoint
  calc
    (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) = α * (α - 1) * A := hresult
    _ = (2 + k - β) * (1 + k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
          dsimp [α, A]
          ring

theorem planarDifference_real_second_derivative_relation (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) :
    (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) =
      (2 + k - β) * (1 + k - β) *
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
  let α : ℝ := 2 + k - β
  let A : ℝ := ∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u
  have hα : 0 < α := by dsimp [α]; linarith
  have hFint : ∀ z : ℂ, Integrable (DOZZ.planarDifferenceKernel k β z) volume :=
    integrable_planarDifferenceKernel k β hk hβ hβ₂ hβtail
  have hFscale (z : ℂ) :
      (∫ u : ℂ, DOZZ.planarDifferenceKernel k β z u) = ‖z‖ ^ α * A := by
    simpa [α, A] using
      planarDifferenceKernel_integral_scale_norm k β hk hβ hβ₂ z
  have hpoint : ∀ t : ℝ, t ≠ 0 → ∀ u : ℂ, u ≠ 0 →
      planarRealSecondDifferenceQuotient k β t u =
        (DOZZ.planarDifferenceKernel k β (1 + (t : ℂ)) u +
          DOZZ.planarDifferenceKernel k β (1 - (t : ℂ)) u -
          2 * DOZZ.planarDifferenceKernel k β 1 u) / t ^ 2 := by
    intro t ht u hu
    have h₁ : u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) := by ring
    have h₂ : u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) := by ring
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos (norm_pos_iff.mpr hu) β
    change ‖u‖ ^ (-β) *
        ((‖u - 1 + (t : ℂ)‖ ^ k + ‖u - 1 - (t : ℂ)‖ ^ k -
          2 * ‖u - 1‖ ^ k) / t ^ 2) = _
    rw [Real.rpow_neg (norm_nonneg u) β]
    simp only [DOZZ.planarDifferenceKernel]
    rw [h₁, h₂]
    field_simp [hden.ne', ht]
    ring
  have hresult := realSecondDifferenceLimit_integral_eq k β α A hk hβ hβ₂
    (DOZZ.planarDifferenceKernel k β) hFint hFscale hpoint
  calc
    (∫ u : ℂ, planarRealSecondDifferenceLimit k β u) = α * (α - 1) * A := hresult
    _ = (2 + k - β) * (1 + k - β) *
        (∫ u : ℂ, DOZZ.planarDifferenceKernel k β 1 u) := by
          dsimp [α, A]
          ring

end DOZZ.Proofs
