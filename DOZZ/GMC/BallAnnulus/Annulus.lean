/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.BallAnnulus.Ball
public import DOZZ.GMC.Annulus.BallCover

/-! The weighted annulus estimate from the proved sharp ball estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- The annulus estimate of [KRV, (annulus)], including negative orders and compact-uniform
centers. -/
theorem equatorGFF_GMC_annulus_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α p : ℝ) (hp : p < 4 / γ ^ 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
          (∫⁻ x in {x : ℂ | ε < ‖x - z‖ ∧ ‖x - z‖ < 2 * ε},
            ENNReal.ofReal (‖x - z‖ ^ (-γ * α)) ∂M ω) p ∂P) ≤
        ENNReal.ofReal (C * Real.rpow ε
          (γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2)) := by
  apply gmc_source_annulus_upper_of_sharp_ball_upper P X hX γ hγ hγ2 M hM α p ?_ K hK
  intro L hL
  obtain ⟨C, hC, hbound⟩ := equatorGFF_GMC_ball_moment_bound
    P X hX γ hγ hγ2 M hM p hp L hL
  exact ⟨C, hC, fun z hz ε hε hε1 => (hbound z hz ε hε hε1).2⟩

end DOZZ.Proofs
end
