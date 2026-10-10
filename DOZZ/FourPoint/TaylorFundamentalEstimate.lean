/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorAnnular
public import DOZZ.FourPoint.TaylorNear
public import DOZZ.FourPoint.TaylorIntermediateOptimized
public import DOZZ.FourPoint.TaylorRegionCover
public import DOZZ.FourPoint.TaylorPowerTransport

/-! The positive fundamental estimate on the actual supplied GMC, with a strict Taylor gain. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- [KRV, (fundest)] with the analytic estimates of all regions proved. The near-root estimate
follows from full-mass weighted Jensen and the one-root identity rather than a local-mass inverse.
Every constant is chosen before the moving root. -/
theorem twoRooted_fundamental_estimate
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (hα₁ : γ / 2 < α₁) (hα₁2 : α₁ < 2 / γ) (hp : 0 ≤ p) :
    ∃ η C r₀ : ℝ, 0 < η ∧ 0 < C ∧ 0 < r₀ ∧
      ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ r₀ →
        gammaHalfTwoRootedMajorant P M γ α₁ α₂ α₃ p z ≤
          ENNReal.ofReal (C * ‖z‖ ^ (γ * (Q γ - α₁) - 2 + η)) := by
  let κ : ℝ := γ * (Q γ - α₁)
  let W : ℝ := (γ / 2 + Q γ - α₁) ^ 2
  obtain ⟨q, δ, ε, η₀, hq, hδ, hδ1, hε, hη₀, hηκ₀, hηd₀, _, hmid₀⟩ :=
    twoRooted_region_parameters γ α₁ hγ hγsq hα₁ hα₁2
  obtain ⟨η, hη, hηκ, hηd, hηnear, hmid⟩ := taylor_common_gain
    γ κ δ ε η₀ (γ * (α₁ - γ / 2)) W q hγ hε hη₀ hηκ₀ hηd₀ hmid₀
  obtain ⟨r₀, hr₀, hr₀4, hscale⟩ := taylor_small_scales δ ε hδ hδ1 hε
  obtain ⟨Ce, hCe, he⟩ := twoRooted_exterior_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  obtain ⟨Ca, hCa, ha⟩ := twoRooted_annular_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp hα₁
  obtain ⟨Cs, hCs, hs⟩ := twoRooted_intermediate_optimized_bound P X hX γ hγ hγ2 hγsq M hM
    α₁ α₂ α₃ p q hα₁ hα₁2 hp hq
  obtain ⟨Cn, hCn, hn⟩ := twoRooted_near_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  let C : ℝ := 16 * (Ce + Ca + Cs + Cn)
  refine ⟨η, C, r₀, hη, by dsimp only [C]; positivity, hr₀, ?_⟩
  intro z hz hzr
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hr4 : ‖z‖ ≤ 1 / 4 := hzr.trans hr₀4
  have hr1 : ‖z‖ ≤ 1 := hr4.trans (by norm_num)
  let ρ : ℝ := ‖z‖ ^ (1 - δ)
  let d : ℝ := ‖z‖ ^ (1 + ε)
  obtain ⟨hρ, hρ4, hzrhalf, hd, hdrhalf⟩ := hscale ‖z‖ hr hzr
  have hρhalf : ρ ≤ 1 / 2 := hρ4.trans (by norm_num)
  have hzrρ : ‖z‖ ≤ ρ := by linarith only [hzrhalf, hρ]
  let B : Fin 4 → Set ℂ := ![(Metric.ball 0 (1 / 2))ᶜ,
    Metric.ball 0 (1 / 2) \ Metric.ball 0 ρ,
    Metric.ball 0 ρ \ Metric.ball z d, Metric.ball z d]
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    fin_cases i
    · exact measurableSet_ball.compl
    · exact measurableSet_ball.diff measurableSet_ball
    · exact measurableSet_ball.diff measurableSet_ball
    · exact measurableSet_ball
  have hcover : ⋃ i, B i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [Set.mem_iUnion]
    by_cases hx : x ∈ Metric.ball z d
    · exact ⟨3, hx⟩
    by_cases hxρ : x ∈ Metric.ball 0 ρ
    · exact ⟨2, hxρ, hx⟩
    by_cases hxhalf : x ∈ Metric.ball 0 (1 / 2)
    · exact ⟨1, hxhalf, hxρ⟩
    · exact ⟨0, hxhalf⟩
  let E : ℝ := κ - 2 + η
  have hpow : 1 ≤ ‖z‖ ^ E := by
    have hE : E ≤ 0 := by dsimp only [E]; linarith only [hηκ]
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hr hr1 hE
  obtain ⟨hpa, hps, hpn⟩ := taylor_regional_powers γ α₁ δ ε η W q ‖z‖ hγ hr hr1 hηd hηnear hmid
  let Creg : Fin 4 → ℝ := ![Ce, Ca, Cs, Cn]
  have hregions (i : Fin 4) :
      gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z (B i) ≤
        ENNReal.ofReal (Creg i * ‖z‖ ^ E) := by
    fin_cases i
    · exact (he z hr4).trans (ENNReal.ofReal_le_ofReal (by
        change Ce ≤ Ce * ‖z‖ ^ E
        exact le_mul_of_one_le_right hCe.le hpow))
    · exact (ha ρ hρ hρhalf z hzrhalf).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hpa hCa.le))
    · have hb := hs ρ hρ hρ4 z hzrρ d hd
      exact hb.trans (ENNReal.ofReal_le_ofReal (by
        change Cs * (d⁻¹) ^ 2 * ρ ^ (W / (2 * q)) ≤ Cs * ‖z‖ ^ E
        calc
          _ = Cs * ((d⁻¹) ^ 2 * ρ ^ (W / (2 * q))) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hps hCs.le))
    · exact (hn z hz hr4 d hd hdrhalf).trans (ENNReal.ofReal_le_ofReal (by
        change Cn * ‖z‖ ^ (-γ * α₁) * d ^ (γ ^ 2 / 2) ≤ Cn * ‖z‖ ^ E
        calc
          _ = Cn * (‖z‖ ^ (-γ * α₁) * d ^ (γ ^ 2 / 2)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hpn hCn.le))
  calc
    _ ≤ 16 * ∑ i : Fin 4, ENNReal.ofReal (Creg i * ‖z‖ ^ E) :=
      (twoRooted_region_cover P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p z B hB hcover).trans
        (mul_le_mul' le_rfl (Finset.sum_le_sum (fun i _ => hregions i)))
    _ = _ := by
      rw [Fin.sum_univ_four]
      change 16 * (ENNReal.ofReal (Ce * ‖z‖ ^ E) + ENNReal.ofReal (Ca * ‖z‖ ^ E) +
        ENNReal.ofReal (Cs * ‖z‖ ^ E) + ENNReal.ofReal (Cn * ‖z‖ ^ E)) = _
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      have h16 : (16 : ℝ≥0∞) = ENNReal.ofReal (16 : ℝ) := by norm_num
      rw [h16, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
      congr 1
      dsimp only [C, E, κ]
      ring

end DOZZ.Proofs
