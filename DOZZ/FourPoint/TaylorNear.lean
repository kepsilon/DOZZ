/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorOneRootIdentity
public import DOZZ.FourPoint.TaylorNearKernel
public import DOZZ.FourPoint.TaylorRadialBall

/-! The near-root positive Taylor contribution from weighted Jensen and one insertion. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A uniform near-root bound for the actual supplied GMC. The same fixed disk controls the
inserted inverse moment; the planar radial exponent exceeds -2 for every positive gamma. -/
theorem twoRooted_near_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      ∀ d : ℝ, 0 < d → d ≤ ‖z‖ / 2 →
        gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z (Metric.ball z d) ≤
          ENNReal.ofReal (C * ‖z‖ ^ (-γ * α₁) * d ^ (γ ^ 2 / 2)) := by
  obtain ⟨C₀, hC₀, hsp⟩ := twoRooted_annular_spatial_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  obtain ⟨C₁, hC₁, hball⟩ := planar_radial_ball_bound (γ ^ 2 / 2 - 2)
    (by nlinarith only [sq_pos_of_pos hγ])
  let k : ℝ := (2 : ℝ) ^ (|γ * α₁| + |γ * α₂|)
  let C : ℝ := C₀ * k * C₁
  refine ⟨C, by dsimp only [C, k]; positivity, ?_⟩
  intro z hz hz4 d hd hdsmall
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnear (x : ℂ) (hx : x ∈ Metric.ball z d) : ‖x - z‖ ≤ ‖z‖ / 2 :=
    (show ‖x - z‖ < d by simpa only [Metric.mem_ball, dist_eq_norm] using hx).le.trans hdsmall
  have hunit (x : ℂ) (hx : x ∈ Metric.ball z d) : ‖x‖ ≤ 1 / 2 := by
    have hh := norm_sub_norm_le x z
    have hn := hnear x hx
    linarith only [hh, hn, hz4]
  have hkernel : (∫⁻ x in Metric.ball z d, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2)) ≤
      ENNReal.ofReal (k * ‖z‖ ^ (-γ * α₁)) * ENNReal.ofReal (C₁ * d ^ (γ ^ 2 / 2)) := by
    have he : γ ^ 2 / 2 - 2 + 2 = γ ^ 2 / 2 := by ring
    calc
      _ ≤ ∫⁻ x in Metric.ball z d, ENNReal.ofReal (k * ‖z‖ ^ (-γ * α₁)) *
          ENNReal.ofReal (‖x - z‖ ^ (γ ^ 2 / 2 - 2)) :=
        setLIntegral_mono' measurableSet_ball (fun x hx => gammaHalf_near_kernel_bound
          γ α₁ α₂ α₃ hγ z x hz hz4 (hnear x hx))
      _ = ENNReal.ofReal (k * ‖z‖ ^ (-γ * α₁)) *
          (∫⁻ x in Metric.ball z d, ENNReal.ofReal (‖x - z‖ ^ (γ ^ 2 / 2 - 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl (by simpa only [he] using hball z d hd)
  calc
    _ ≤ ENNReal.ofReal C₀ * (ENNReal.ofReal (k * ‖z‖ ^ (-γ * α₁)) * ENNReal.ofReal (C₁ * d ^ (γ ^ 2 / 2))) :=
      (hsp z hz4 (Metric.ball z d) measurableSet_ball hunit).trans (mul_le_mul' le_rfl hkernel)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by dsimp only [k]; positivity), ← ENNReal.ofReal_mul hC₀.le]
      congr 1
      dsimp only [C]
      ring

end DOZZ.Proofs
