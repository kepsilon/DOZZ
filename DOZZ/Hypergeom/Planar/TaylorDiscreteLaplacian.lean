/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorFiniteDifference
public import DOZZ.Hypergeom.Planar.TaylorParentScaling
public import DOZZ.Hypergeom.Planar.RieszNormalization
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! A dominated discrete-Laplacian limit for the corrected Taylor parent integral. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ.Proofs

/-- The four-direction discrete Laplacian of the corrected Taylor integral kernel, divided by
the squared step. -/
noncomputable def planarTaylorDiscreteQuotient (k β : ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  (DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
    DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
    DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
    DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
    4 * DOZZ.planarTaylorRemainder k β 1 u) / t ^ 2

private noncomputable def planarTaylorLinearCounterterm (u z : ℂ) : ℝ :=
  (z / u + star z / star u).re

private noncomputable def planarTaylorNumerator (k : ℝ) (z u : ℂ) : ℝ :=
  ‖u - z‖ ^ k - ‖u‖ ^ k +
    (k / 2) * ‖u‖ ^ k * planarTaylorLinearCounterterm u z

/-- Four-direction second-difference quotient of the radial power. -/
noncomputable def normPowerDiscreteLaplacian (k : ℝ) (t : ℝ) (x : ℂ) : ℝ :=
  (‖x + (t : ℂ)‖ ^ k + ‖x - (t : ℂ)‖ ^ k +
    ‖x + (t : ℂ) * Complex.I‖ ^ k + ‖x - (t : ℂ) * Complex.I‖ ^ k -
    4 * ‖x‖ ^ k) / t ^ 2

private theorem planarTaylorLinearCounterterm_add (u z w : ℂ) :
    planarTaylorLinearCounterterm u (z + w) =
      planarTaylorLinearCounterterm u z + planarTaylorLinearCounterterm u w := by
  simp only [planarTaylorLinearCounterterm, add_div, star_add, Complex.add_re]
  ring

private theorem planarTaylorLinearCounterterm_four_shifts (u : ℂ) (t : ℝ) :
    planarTaylorLinearCounterterm u (1 + (t : ℂ)) +
        planarTaylorLinearCounterterm u (1 - (t : ℂ)) +
        planarTaylorLinearCounterterm u (1 + (t : ℂ) * Complex.I) +
        planarTaylorLinearCounterterm u (1 - (t : ℂ) * Complex.I) -
        4 * planarTaylorLinearCounterterm u 1 = 0 := by
  have hreal : (1 : ℂ) + (t : ℂ) + (1 - (t : ℂ)) = 2 := by ring
  have himag : (1 : ℂ) + (t : ℂ) * Complex.I +
      (1 - (t : ℂ) * Complex.I) = 2 := by ring
  have htwo : (2 : ℂ) = 1 + 1 := by norm_num
  calc
    _ = (planarTaylorLinearCounterterm u (1 + (t : ℂ)) +
          planarTaylorLinearCounterterm u (1 - (t : ℂ))) +
        (planarTaylorLinearCounterterm u (1 + (t : ℂ) * Complex.I) +
          planarTaylorLinearCounterterm u (1 - (t : ℂ) * Complex.I)) -
        4 * planarTaylorLinearCounterterm u 1 := by ring
    _ = planarTaylorLinearCounterterm u
          ((1 : ℂ) + (t : ℂ) + (1 - (t : ℂ))) +
        planarTaylorLinearCounterterm u
          ((1 : ℂ) + (t : ℂ) * Complex.I + (1 - (t : ℂ) * Complex.I)) -
        4 * planarTaylorLinearCounterterm u 1 := by
          rw [← planarTaylorLinearCounterterm_add, ← planarTaylorLinearCounterterm_add]
    _ = planarTaylorLinearCounterterm u 2 + planarTaylorLinearCounterterm u 2 -
        4 * planarTaylorLinearCounterterm u 1 := by rw [hreal, himag]
    _ = 0 := by
      rw [htwo, planarTaylorLinearCounterterm_add]
      ring

private theorem integrable_planarTaylorDiscreteNumerator (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) (t : ℝ) :
    Integrable (fun u : ℂ =>
      DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
        DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
        DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
        DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
        4 * DOZZ.planarTaylorRemainder k β 1 u) volume := by
  have h₁ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
    (1 + (t : ℂ))
  have h₂ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
    (1 - (t : ℂ))
  have h₃ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
    (1 + (t : ℂ) * Complex.I)
  have h₄ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
    (1 - (t : ℂ) * Complex.I)
  have h₀ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin 1
  exact (((h₁.add h₂).add h₃).add h₄).sub (h₀.const_mul 4)

/-- The discrete quotient is integrable for every step. -/
theorem integrable_planarTaylorDiscreteQuotient (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) (t : ℝ) :
    Integrable (planarTaylorDiscreteQuotient k β t) volume := by
  have hN := integrable_planarTaylorDiscreteNumerator k β hk hβ hβ₂ hβlin t
  change Integrable (fun u : ℂ =>
    (DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
      DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
      DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
      DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
      4 * DOZZ.planarTaylorRemainder k β 1 u) / t ^ 2)
  exact hN.div_const (t ^ 2)

/-- Integrating the discrete quotient gives the same quotient of parent integrals. -/
theorem integral_planarTaylorDiscreteQuotient (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) (t : ℝ) :
    (∫ u : ℂ, planarTaylorDiscreteQuotient k β t u) =
      ((∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u)) / t ^ 2 := by
  have h₁ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 + (t : ℂ))
  have h₂ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin (1 - (t : ℂ))
  have h₃ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
    (1 + (t : ℂ) * Complex.I)
  have h₄ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin
    (1 - (t : ℂ) * Complex.I)
  have h₀ := integrable_planarTaylorRemainder k β hk hβ hβ₂ hβlin 1
  let N : ℂ → ℝ := fun u =>
    DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u +
      DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u +
      DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u +
      DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u -
      4 * DOZZ.planarTaylorRemainder k β 1 u
  let f₁ : ℂ → ℝ := DOZZ.planarTaylorRemainder k β (1 + (t : ℂ))
  let f₂ : ℂ → ℝ := DOZZ.planarTaylorRemainder k β (1 - (t : ℂ))
  let f₃ : ℂ → ℝ := DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I)
  let f₄ : ℂ → ℝ := DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I)
  let f₀ : ℂ → ℝ := DOZZ.planarTaylorRemainder k β 1
  have hf₁ : Integrable f₁ volume := by simpa [f₁] using h₁
  have hf₂ : Integrable f₂ volume := by simpa [f₂] using h₂
  have hf₃ : Integrable f₃ volume := by simpa [f₃] using h₃
  have hf₄ : Integrable f₄ volume := by simpa [f₄] using h₄
  have hf₀ : Integrable f₀ volume := by simpa [f₀] using h₀
  have hN : Integrable N volume := integrable_planarTaylorDiscreteNumerator
    k β hk hβ hβ₂ hβlin t
  have h₁₂ : (∫ u : ℂ, f₁ u + f₂ u) = (∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u) :=
    integral_add hf₁ hf₂
  have h₁₂₃ : (∫ u : ℂ, (f₁ u + f₂ u) + f₃ u) =
      ((∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u)) + (∫ u : ℂ, f₃ u) := by
    calc
      _ = (∫ u : ℂ, f₁ u + f₂ u) + (∫ u : ℂ, f₃ u) := by
        simpa only [Pi.add_apply] using integral_add (hf₁.add hf₂) hf₃
      _ = _ := by rw [h₁₂]
  have h₁₂₃₄ : (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) =
      (((∫ u : ℂ, f₁ u) + (∫ u : ℂ, f₂ u)) + (∫ u : ℂ, f₃ u)) +
        (∫ u : ℂ, f₄ u) := by
    calc
      _ = (∫ u : ℂ, (f₁ u + f₂ u) + f₃ u) + (∫ u : ℂ, f₄ u) := by
        simpa only [Pi.add_apply] using integral_add ((hf₁.add hf₂).add hf₃) hf₄
      _ = _ := by rw [h₁₂₃]
  have hsum : (∫ u : ℂ, N u) =
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ)) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 + (t : ℂ) * Complex.I) u) +
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β (1 - (t : ℂ) * Complex.I) u) -
        4 * (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
    have hNfun : N = fun u => ((f₁ u + f₂ u) + f₃ u) + f₄ u - 4 * f₀ u := by
      funext u
      dsimp [N, f₁, f₂, f₃, f₄, f₀]
    calc
      (∫ u : ℂ, N u) =
          (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u - 4 * f₀ u) := by rw [hNfun]
      _ = (∫ u : ℂ, ((f₁ u + f₂ u) + f₃ u) + f₄ u) -
          (∫ u : ℂ, 4 * f₀ u) := integral_sub
            (((hf₁.add hf₂).add hf₃).add hf₄) (hf₀.const_mul 4)
      _ = _ := by rw [h₁₂₃₄, integral_const_mul]
  have hQ : (fun u : ℂ => planarTaylorDiscreteQuotient k β t u) =
      fun u => (t ^ 2)⁻¹ * N u := by
    funext u
    exact div_eq_inv_mul _ _
  rw [hQ, integral_const_mul, hsum]
  simp [div_eq_mul_inv, mul_comm]

/-- Away from the fixed denominator singularity, the Taylor counterterms cancel from the
discrete Laplacian and leave the positive radial kernel. -/
theorem planarTaylorDiscreteQuotient_eq_kernel (k β : ℝ) (t : ℝ) (u : ℂ) :
    planarTaylorDiscreteQuotient k β t u =
      ‖u‖ ^ (-β) * normPowerDiscreteLaplacian k t (u - 1) := by
  have hcounter := planarTaylorLinearCounterterm_four_shifts u t
  have hnum :
      planarTaylorNumerator k (1 + (t : ℂ)) u +
        planarTaylorNumerator k (1 - (t : ℂ)) u +
        planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u +
        planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u -
        4 * planarTaylorNumerator k 1 u =
        (‖u - (1 + (t : ℂ))‖ ^ k + ‖u - (1 - (t : ℂ))‖ ^ k +
          ‖u - (1 + (t : ℂ) * Complex.I)‖ ^ k +
          ‖u - (1 - (t : ℂ) * Complex.I)‖ ^ k - 4 * ‖u - 1‖ ^ k) := by
    simp only [planarTaylorNumerator]
    linear_combination (k / 2 * ‖u‖ ^ k) * hcounter
  have hR (z : ℂ) : DOZZ.planarTaylorRemainder k β z u =
      planarTaylorNumerator k z u / ‖u‖ ^ β := by
    simp [DOZZ.planarTaylorRemainder, planarTaylorNumerator,
      planarTaylorLinearCounterterm]
  have hcombine :
      (planarTaylorNumerator k (1 + (t : ℂ)) u / ‖u‖ ^ β +
        planarTaylorNumerator k (1 - (t : ℂ)) u / ‖u‖ ^ β +
        planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u / ‖u‖ ^ β +
        planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u / ‖u‖ ^ β -
        4 * (planarTaylorNumerator k 1 u / ‖u‖ ^ β)) =
      (planarTaylorNumerator k (1 + (t : ℂ)) u +
        planarTaylorNumerator k (1 - (t : ℂ)) u +
        planarTaylorNumerator k (1 + (t : ℂ) * Complex.I) u +
        planarTaylorNumerator k (1 - (t : ℂ) * Complex.I) u -
        4 * planarTaylorNumerator k 1 u) / ‖u‖ ^ β := by ring
  rw [planarTaylorDiscreteQuotient, hR, hR, hR, hR, hR, hcombine, hnum]
  have h₁ : u - (1 + (t : ℂ)) = (u - 1) - (t : ℂ) := by ring
  have h₂ : u - (1 - (t : ℂ)) = (u - 1) + (t : ℂ) := by ring
  have h₃ : u - (1 + (t : ℂ) * Complex.I) =
      (u - 1) - (t : ℂ) * Complex.I := by ring
  have h₄ : u - (1 - (t : ℂ) * Complex.I) =
      (u - 1) + (t : ℂ) * Complex.I := by ring
  rw [h₁, h₂, h₃, h₄]
  rw [Real.rpow_neg (norm_nonneg u) β]
  simp only [normPowerDiscreteLaplacian]
  ring

/-- The pointwise limit of the corrected parent quotient is the positive Riesz kernel. -/
theorem planarTaylorDiscreteQuotient_tendsto (k β : ℝ) (u : ℂ) (hu : u ≠ 1) :
    Tendsto (fun t : ℝ => planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  let w : ℝ := ‖u‖ ^ (-β)
  have hLap := norm_rpow_discrete_laplacian_tendsto k (u - 1) hx
  have hmul : Tendsto (fun t : ℝ => w * normPowerDiscreteLaplacian k t (u - 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 (w * (k ^ 2 * ‖u - 1‖ ^ (k - 2)))) :=
    tendsto_const_nhds.mul hLap
  have hEq : (fun t : ℝ => planarTaylorDiscreteQuotient k β t u) =ᶠ[𝓝[≠] (0 : ℝ)]
      fun t => w * normPowerDiscreteLaplacian k t (u - 1) := by
    filter_upwards [] with t
    exact planarTaylorDiscreteQuotient_eq_kernel k β t u
  have hlim := hmul.congr' hEq.symm
  simpa [w, mul_assoc, mul_left_comm, mul_comm] using hlim

/-- A uniform Riesz-kernel majorant for the discrete quotients, away from the null collision. -/
theorem planarTaylorDiscreteQuotient_norm_le (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hk₂ : β < 2)
    (u : ℂ) (t : ℝ) (hu : u ≠ 1) (ht : t ≠ 0) :
    ‖planarTaylorDiscreteQuotient k β t u‖ ≤
      (2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
        (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
        2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))) *
        (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by
  let C : ℝ := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) +
    2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  have hx : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  have hLap := norm_rpow_discrete_laplacian_le k hk (by linarith [hβ, hk₂])
    (u - 1) t hx ht
  have hw : 0 ≤ ‖u‖ ^ (-β) := Real.rpow_nonneg (norm_nonneg u) _
  have hkernel := planarTaylorDiscreteQuotient_eq_kernel k β t u
  rw [hkernel, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
  change ‖u‖ ^ (-β) * |normPowerDiscreteLaplacian k t (u - 1)| ≤
    C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  calc
    _ ≤ ‖u‖ ^ (-β) * (C * ‖u - 1‖ ^ (k - 2)) :=
      mul_le_mul_of_nonneg_left (by simpa [C, normPowerDiscreteLaplacian] using hLap) hw
    _ = C * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)) := by ring

/-- Dominated convergence identifies the limiting integral of the Taylor discrete quotient with
the positive Riesz convolution multiplied by `k^2`. -/
theorem planarTaylorDiscreteQuotient_integral_tendsto (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    Tendsto (fun t : ℝ => ∫ u : ℂ, planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ u : ℂ, k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
  let K : ℝ := 2 * (2 * (k * (1 + (15 / 4) * ((1 - k / 2) *
    (1 / 4 : ℝ) ^ (k / 2 - 2)))) + 2 * (3 ^ k + 2 ^ k) * 2 ^ (2 - k))
  let bound : ℂ → ℝ := fun u => K * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2))
  have hK : 0 ≤ K := by
    dsimp [K]
    have hk₂ : 0 < 1 - k / 2 := by linarith [hβ, hβ₂]
    positivity
  have hRiesz := positive_riesz_convolution_integrable k β hk hβ hβ₂ 1 (by norm_num)
  have hboundInt : Integrable bound volume := by
    simpa [bound, K, mul_assoc] using hRiesz.const_mul K
  have hmeas : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      AEStronglyMeasurable (planarTaylorDiscreteQuotient k β t) volume := by
    filter_upwards [] with t
    exact (integrable_planarTaylorDiscreteQuotient k β hk hβ hβ₂ hβlin t).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ),
      ∀ᵐ u ∂volume, ‖planarTaylorDiscreteQuotient k β t u‖ ≤ bound u := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := by simpa using ht
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    simpa [bound, K] using
      planarTaylorDiscreteQuotient_norm_le k β hk hβ hβ₂ u t hu ht0
  have hlim : ∀ᵐ u ∂volume, Tendsto
      (fun t : ℝ => planarTaylorDiscreteQuotient k β t u)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (k ^ 2 * (‖u‖ ^ (-β) * ‖u - 1‖ ^ (k - 2)))) := by
    filter_upwards [Measure.ae_ne volume (1 : ℂ)] with u hu
    exact planarTaylorDiscreteQuotient_tendsto k β u hu
  exact MeasureTheory.tendsto_integral_filter_of_dominated_convergence bound
    hmeas hbound hboundInt hlim

end DOZZ.Proofs
