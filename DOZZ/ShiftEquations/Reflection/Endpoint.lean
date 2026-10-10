/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Reflection.MomentAssembly
import DOZZ.Brownian.Reflection.Moments
import DOZZ.Brownian.ReflectionRLimit

/-!
# The reflection endpoint at `Q`

The endpoint conjunct of `reflection_endpoint_and_gamma_continuity` ([KRV, §10.6]): along any
reflection witness family on the physical interval, the unit-volume moment tends to `1` and the full
coefficient to `-1` as `α ↑ Q`. The moment limit is the zero-drift small-power limit with exponent
`2ν/γ`, reparameterized by `ν = Q - α`; the lateral measure is almost surely nonzero by its unit
inverse moments.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The unit-volume reflection moment tends to one as `α ↑ Q`. -/
theorem reflectionBarR_tendsto_one_Q {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (hγ : 0 < γ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ => reflectionBarR P γ α (B α) Z) (𝓝[<] (Q γ)) (𝓝 1) := by
  have hQ : Q γ - γ / 2 = 2 / γ := by unfold Q; ring
  have hν₁ : 0 < Q γ - γ / 2 := by rw [hQ]; positivity
  have hdata : ∀ ν : ℝ, 0 < ν → ν < Q γ - γ / 2 →
      IsReflectionData P γ (Q γ - ν) (B (Q γ - ν)) Z := fun ν hν hν₁ =>
    hData (Q γ - ν) (by linarith) (by linarith)
  have hZ : IsLateralGMCOf P γ Z := (hdata _ (half_pos hν₁) (half_lt_self hν₁)).2.1
  have he : Tendsto (fun ν : ℝ => 2 * ν / γ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ν : ℝ => 2 * ν / γ) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hMoment := twoSidedReflectionMass_rpow_tendsto_one_of_ne_zero P γ (Q γ - γ / 2) hγ hν₁ Z
    (fun ν => B (Q γ - ν))
    (fun ν hν hν₁' => by simpa using (hdata ν hν hν₁').1) hZ
    (fun ν hν hν₁' => (hdata ν hν hν₁').2.2) (lateralGMC_ne_zero_ae P γ Z hZ) _ he
    (fun ν hν => (div_pos (mul_pos two_pos hν) hγ).le)
  have hQsub : Tendsto (fun α : ℝ => Q γ - α) (𝓝[<] (Q γ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun α : ℝ => Q γ - α) (Q γ) := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      exact sub_pos.mpr hα
  have hEq : (fun α : ℝ => reflectionBarR P γ α (B α) Z) =
      (fun α => (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ
        (B (Q γ - (Q γ - α))) Z ω) (2 * (Q γ - α) / γ) ∂P).toReal) := by
    funext α
    simp [reflectionBarR, reflectionExponent]
  rw [hEq]
  exact hMoment.comp hQsub

/-- **The endpoint conjunct of `reflection_endpoint_and_gamma_continuity`**: along any physical
witness family, `R̄ → 1` and `R → -1` as `α ↑ Q`. -/
theorem reflection_endpoint_limits {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ => reflectionBarR P γ α (B α) Z) (𝓝[<] (Q γ)) (𝓝 1) ∧
      Tendsto (fun α : ℝ => reflectionR P γ μ α (B α) Z) (𝓝[<] (Q γ)) (𝓝 (-1)) :=
  ⟨reflectionBarR_tendsto_one_Q P γ hγ B Z hData, reflectionR_tendsto_Q P γ μ hγ hγ2 hμ B Z hData⟩

end DOZZ.Proofs

end
