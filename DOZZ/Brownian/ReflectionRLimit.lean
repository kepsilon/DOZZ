/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Brownian.ReflectionExponentBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Analytic endpoint reduction for the reflection coefficient

The full zero-drift theorem supplies the small-power moment limit. This file proves the remaining
scalar limit: that moment limit forces the Brownian reflection coefficient to tend to `-1`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- If the unit-volume reflection moment tends to one at `Q`, then the full probabilistic
reflection coefficient tends to `-1`. -/
theorem reflectionR_tendsto_Q_of_reflectionBarR
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (hγ : 0 < γ) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hBar : Tendsto
      (fun α : ℝ => reflectionBarR P γ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 1)) :
    Tendsto (fun α : ℝ => reflectionR P γ μ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by
  let p : ℝ → ℝ := fun α => reflectionExponent γ α
  have hp0 : Tendsto p (𝓝[<] (Q γ)) (𝓝 0) := by
    simpa [p] using
      (tendsto_reflectionExponent_at_Q γ).mono_left nhdsWithin_le_nhds
  have hpPos : ∀ᶠ α : ℝ in 𝓝[<] (Q γ), 0 < p α := by
    filter_upwards [self_mem_nhdsWithin] with α hα
    have hαQ : α < Q γ := by simpa using hα
    dsimp [p, reflectionExponent]
    exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hαQ)) hγ
  have hnegp : Tendsto (fun α : ℝ => ((-p α : ℝ) : ℂ))
      (𝓝[<] (Q γ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hcont : Continuous (fun x : ℝ => ((-x : ℝ) : ℂ)) := by fun_prop
      convert hcont.continuousAt.tendsto.comp hp0 using 1
      · ext α
        rfl
      · simp
    · filter_upwards [hpPos] with α hα
      simp only [mem_compl_iff, mem_singleton_iff]
      exact Complex.ofReal_ne_zero.mpr (neg_ne_zero.mpr hα.ne')
  have hgammaComplex : Tendsto
      (fun α : ℝ => ((-p α : ℝ) : ℂ) * Complex.Gamma ((-p α : ℝ) : ℂ))
      (𝓝[<] (Q γ)) (𝓝 1) :=
    Complex.tendsto_self_mul_Gamma_nhds_zero.comp hnegp
  have hgammaNegReal : Tendsto
      (fun α : ℝ => -(p α * Real.Gamma (-p α)))
      (𝓝[<] (Q γ)) (𝓝 1) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hgammaComplex
    have hEq : (fun α : ℝ => Complex.re
        (((-p α : ℝ) : ℂ) * Complex.Gamma ((-p α : ℝ) : ℂ))) =
        (fun α => -(p α * Real.Gamma (-p α))) := by
      funext α
      rw [Complex.Gamma_ofReal]
      simp
    have hre' : Tendsto (fun α : ℝ => Complex.re
        (((-p α : ℝ) : ℂ) * Complex.Gamma ((-p α : ℝ) : ℂ)))
        (𝓝[<] (Q γ)) (𝓝 1) := by
      exact hre
    rw [hEq] at hre'
    exact hre'
  have hgammaReal : Tendsto
      (fun α : ℝ => p α * Real.Gamma (-p α))
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by
    have h := hgammaNegReal.neg
    simpa using h
  have hmu : Tendsto (fun α : ℝ => μ ^ p α)
      (𝓝[<] (Q γ)) (𝓝 1) := by
    have hcont :=
      (Real.continuousAt_const_rpow (a := μ) (b := 0) hμ.ne').tendsto
    simpa [Function.comp_def, Real.rpow_zero] using hcont.comp hp0
  have hprod : Tendsto
      (fun α : ℝ => μ ^ p α * (p α * Real.Gamma (-p α)) *
        reflectionBarR P γ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by
    have h := (hmu.mul hgammaReal).mul hBar
    simpa using h
  have hformula : (fun α : ℝ => reflectionR P γ μ α (B α) Z) =
      (fun α => μ ^ p α * (p α * Real.Gamma (-p α)) *
        reflectionBarR P γ α (B α) Z) := by
    funext α
    simp [reflectionR, p, reflectionExponent, mul_comm, mul_left_comm]
  rw [hformula]
  exact hprod

/-- The zero-drift moment limit (`DOZZ.reflectionMoment_zeroDrift_tendsto_one`),
reparameterized by `ν = Q γ - α`, implies the endpoint limit for the full reflection
coefficient. -/
theorem reflectionR_tendsto_Q_of_zeroDriftMoment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (hγ : 0 < γ) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hMoment : Tendsto
      (fun ν : ℝ =>
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ
          (B (Q γ - ν)) Z ω) (2 * ν / γ) ∂P).toReal)
      (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun α : ℝ => reflectionR P γ μ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by
  have hQsub : Tendsto (fun α : ℝ => Q γ - α)
      (𝓝[<] (Q γ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have hcont : ContinuousAt (fun α : ℝ => Q γ - α) (Q γ) := by fun_prop
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with α hα
      have hα' : α < Q γ := by simpa using hα
      exact sub_pos.mpr hα'
  have hBar : Tendsto
      (fun α : ℝ => reflectionBarR P γ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 1) := by
    have hcomp := hMoment.comp hQsub
    have hEq : (fun α : ℝ => reflectionBarR P γ α (B α) Z) =
        (fun α =>
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ
            (B (Q γ - (Q γ - α))) Z ω)
            (2 * (Q γ - α) / γ) ∂P).toReal) := by
      funext α
      simp [reflectionBarR, reflectionExponent]
    rw [hEq]
    exact hcomp
  exact reflectionR_tendsto_Q_of_reflectionBarR P γ μ hγ hμ B Z hBar

end DOZZ.Proofs

end
