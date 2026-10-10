/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Continuity.MomentLimit
public import DOZZ.Statements.Defs.SExp
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- In the inverted chart the moving root approaches zero while the other finite
root stays at one. The strict ordinary Seiberg bounds provide all moment slack. -/
theorem infinity_moving_moment_continuousAt_zero
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ContinuousAt (fun v : ℂ => (∫⁻ ω,
      (coulombMass γ (M ω) ![α₃, α₂] ![v, 1] α₁) ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal) 0 := by
  classical
  obtain ⟨Mf, hMf, heq⟩ := extendGMCFamily_on_compact P X hX (fun _ => M)
    {(γ, ![α₁, α₂, α₃])} (fun q hq => by
      obtain rfl := mem_singleton_iff.mp hq
      exact hM)
  have hMfγ : Mf γ = M := heq (γ, ![α₁, α₂, α₃]) (mem_singleton _)
  obtain ⟨Xc, hc⟩ := exists_equatorGFF_circle_average_witness X hX
  let J : ℂ → ContinuityCoulombParameter 2 := fun v => (γ, (![v, 1], ![α₃, α₂], α₁))
  have hJ : Continuous J := by unfold J; fun_prop
  have hp (v : ℂ) : continuityCoulombPower (J v) = -sExp γ α₁ α₂ α₃ := by
    simp [continuityCoulombPower, J, sExp, Fin.sum_univ_two]
    ring
  have hneg : -sExp γ α₁ α₂ α₃ < 0 := neg_neg_of_pos (div_pos (sub_pos.mpr hs) hγ)
  have hadm : ∀ c ∈ J '' Metric.closedBall 0 (1 / 2),
      0 < c.1 ∧ c.1 < 2 ∧ Function.Injective c.2.1 ∧
      (∀ k, c.2.2.1 k < Q c.1) ∧ c.2.2.2 < Q c.1 ∧
      continuityCoulombPower c < 4 / c.1 ^ 2 ∧
      (∀ k, continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.1 k)) ∧
      continuityCoulombPower c < 2 / c.1 * (Q c.1 - c.2.2.2) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv1 : v ≠ 1 := by
      intro he
      rw [he, Metric.mem_closedBall, dist_zero_right, norm_one] at hv
      norm_num at hv
    refine ⟨hγ, hγ2, ?_, ?_, hα₁, ?_, ?_, ?_⟩
    · change Function.Injective (![v, 1] : Fin 2 → ℂ)
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro k
      fin_cases k
      · exact hα₃
      · exact hα₂
    · rw [hp]
      exact hneg.trans (by positivity)
    · intro k
      rw [hp]
      fin_cases k
      · exact hneg.trans (mul_pos (div_pos two_pos hγ) (sub_pos.mpr hα₃))
      · exact hneg.trans (mul_pos (div_pos two_pos hγ) (sub_pos.mpr hα₂))
    · rw [hp]
      exact hneg.trans (mul_pos (div_pos two_pos hγ) (sub_pos.mpr hα₁))
  have hm := (continuity_coulomb_moment_on_compact P X hX Xc hc Mf hMf
    (J '' Metric.closedBall 0 (1 / 2)) ((isCompact_closedBall _ _).image hJ) hadm).comp
      hJ.continuousOn (mapsTo_image J _)
  have hm' : ContinuousOn (fun v : ℂ => (∫⁻ ω,
      (coulombMass γ (M ω) ![α₃, α₂] ![v, 1] α₁) ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal)
      (Metric.closedBall 0 (1 / 2)) := by
    apply hm.congr
    intro v _
    simp only [Function.comp_apply, J, hp, hMfγ]
  exact hm'.continuousAt (Metric.closedBall_mem_nhds _ (by norm_num))

end DOZZ.Proofs
