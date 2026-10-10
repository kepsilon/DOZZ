/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorAnnularKernel
public import DOZZ.FourPoint.TaylorRadialTail

/-! The supplied-GMC annular contribution with the literal κ-2 radial gain. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The annular Taylor contribution, uniformly before the moving root and inner radius. -/
theorem twoRooted_annular_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) (hα : γ / 2 < α₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 2 →
      ∀ z : ℂ, ‖z‖ ≤ ρ / 2 →
        gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z
          (Metric.ball 0 (1 / 2) \ Metric.ball 0 ρ) ≤
            ENNReal.ofReal (C * ρ ^ (γ * (Q γ - α₁) - 2)) := by
  let a : ℝ := γ * (Q γ - α₁) - 4
  have ha : a < -2 := by
    have he : a = γ ^ 2 / 2 - γ * α₁ - 2 := by
      dsimp only [a]
      unfold Q
      field_simp [hγ.ne']
      ring
    rw [he]
    nlinarith only [hα, hγ]
  obtain ⟨C₀, hC₀, hsp⟩ := twoRooted_annular_spatial_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  obtain ⟨C₁, hC₁, htail⟩ := planar_radial_tail_bound a ha
  let k : ℝ := (2 : ℝ) ^ (|γ * α₂| + |γ ^ 2 / 2 - 2|)
  let C : ℝ := C₀ * k * C₁
  refine ⟨C, by dsimp only [C, k]; positivity, ?_⟩
  intro ρ hρ hρ2 z hz
  let B : Set ℂ := Metric.ball 0 (1 / 2) \ Metric.ball 0 ρ
  have hB : MeasurableSet B := measurableSet_ball.diff measurableSet_ball
  have hunit (x : ℂ) (hx : x ∈ B) : ‖x‖ ≤ 1 / 2 := by
    exact (show ‖x‖ < 1 / 2 by simpa only [Metric.mem_ball, dist_zero_right] using hx.1).le
  have hz4 : ‖z‖ ≤ 1 / 4 := by linarith only [hz, hρ2]
  have hpoint (x : ℂ) (hx : x ∈ B) :
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2) ≤
        ENNReal.ofReal k * ENNReal.ofReal (‖x‖ ^ a) := by
    have hxr : ρ ≤ ‖x‖ := by
      have hh := hx.2
      simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hh
    exact gammaHalf_annular_kernel_bound γ α₁ α₂ α₃ hγ z x (hunit x hx)
      (hρ.trans_le hxr) (by linarith only [hz, hxr])
  have hkernel : (∫⁻ x in B, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2)) ≤
      ENNReal.ofReal k * (∫⁻ x : ℂ in (Metric.ball 0 ρ)ᶜ, ENNReal.ofReal (‖x‖ ^ a)) := by
    calc
      _ ≤ ∫⁻ x in B, ENNReal.ofReal k * ENNReal.ofReal (‖x‖ ^ a) := setLIntegral_mono' hB hpoint
      _ = ENNReal.ofReal k * ∫⁻ x in B, ENNReal.ofReal (‖x‖ ^ a) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set (fun x hx => hx.2))
  calc
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal k * (∫⁻ x : ℂ in (Metric.ball 0 ρ)ᶜ, ENNReal.ofReal (‖x‖ ^ a))) :=
      (hsp z hz4 B hB hunit).trans (mul_le_mul' le_rfl hkernel)
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal k * ENNReal.ofReal (C₁ * ρ ^ (a + 2))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (htail ρ hρ))
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by dsimp only [k]; positivity), ← ENNReal.ofReal_mul hC₀.le]
      congr 1
      dsimp only [C, a]
      rw [show γ * (Q γ - α₁) - 4 + 2 = γ * (Q γ - α₁) - 2 by ring]
      ring

end DOZZ.Proofs
