/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Limits
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.Statements.Brownian.ReflectionBarR
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.ShiftEquations.RbarCoefficient
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.Reflection.PositiveFinite
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# The reflection coefficient at `α = γ`

The constant `c_γ = (γ²/4) μπ R(γ)` of the dual shift is the value of the meromorphic representative
`R` at `γ`. The holomorphic representation of `R̄`
(`DOZZ.reflectionBarR_holomorphic_representation`) makes the physical `R(α) = μ^ν Γ(-ν) ν R̄(α)`
(`ν = 2(Q - α)/γ`) continuous at `α = γ` when `Γ` has no pole at `-ν(γ) = 1 - 4/γ²` (`γ²`
irrational); a meromorphic function with continuous real restriction is analytic, so `R` is analytic
at `γ` with value `R(γ)`. Moreover `R(γ) ≠ 0` since `R̄(γ) > 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- `Γ` has no pole at `-ν(γ) = 1 - 4/γ²` when `γ²` is irrational. -/
theorem reflectionExponent_gamma_ne {γ : ℝ} (hγ : 0 < γ) (hγirr : Irrational (γ ^ 2))
    (m : ℕ) : -reflectionExponent γ γ ≠ -(m : ℝ) := by
  intro h
  have he : reflectionExponent γ γ = m := by linarith
  unfold reflectionExponent Q at he
  have h4 : 4 / γ ^ 2 = (m : ℝ) + 1 := by
    rw [← he]
    field_simp
    ring
  apply hγirr
  refine ⟨4 / ((m : ℚ) + 1), ?_⟩
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  push_cast
  field_simp at h4 ⊢
  linarith

/-- **The physical reflection coefficient is continuous at `α = γ`** (from
`DOZZ.reflectionBarR_holomorphic_representation`). -/
theorem tendsto_reflectionR_gamma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hγirr : Irrational (γ ^ 2))
    (hBarRRepresentation : ∀ I : Set ℝ, IsCompact I → (∀ α ∈ I, γ / 2 < α ∧ α < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              (∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ)))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR) :
    Tendsto (fun α : ℝ => reflectionR P γ μ α (BR α) ZR) (𝓝 γ)
      (𝓝 (reflectionR P γ μ γ (BR γ) ZR)) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  set δ : ℝ := min (γ / 4) ((Q γ - γ) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ γ / 4 := min_le_left _ _
  have hδ2 : δ ≤ (Q γ - γ) / 2 := min_le_right _ _
  set I : Set ℝ := Icc (γ - δ) (γ + δ) with hI
  have hIdom : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ := fun α hα =>
    ⟨by linarith [hα.1], by linarith [hα.2]⟩
  obtain ⟨B, Z, -, hBd, V, hV, hIV, f, -, -, hgd, hgv⟩ := hBarRRepresentation I isCompact_Icc hIdom
  have hγI : γ ∈ I := ⟨by linarith, by linarith⟩
  have hInhds : I ∈ 𝓝 γ := Icc_mem_nhds (by linarith) (by linarith)
  -- continuity of `R̄`
  have hgc : ContinuousAt (fun z => rbarCoefficient γ z * f z) (γ : ℂ) :=
    (hgd.differentiableAt (hV.mem_nhds (hIV γ hγI))).continuousAt
  have hRbar : Tendsto (fun α : ℝ => reflectionBarR P γ α (BR α) ZR) (𝓝 γ)
      (𝓝 (reflectionBarR P γ γ (BR γ) ZR)) := by
    have h1 : Tendsto (fun α : ℝ => (rbarCoefficient γ (α : ℂ) * f (α : ℂ)).re) (𝓝 γ)
        (𝓝 (rbarCoefficient γ (γ : ℂ) * f (γ : ℂ)).re) :=
      (Complex.continuous_re.continuousAt.tendsto).comp
        (hgc.tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto)
    have hval : ∀ α ∈ I, reflectionBarR P γ α (BR α) ZR =
        (rbarCoefficient γ (α : ℂ) * f (α : ℂ)).re := fun α hα => by
      rw [hgv α hα, Complex.ofReal_re]
      exact reflectionBarR_eq_of_isReflectionData P P γ α (BR α) ZR (B α) Z
        (hBR α (hIdom α hα).1 (hIdom α hα).2) (hBd α hα)
    rw [hval γ hγI]
    exact h1.congr' (Filter.eventually_of_mem hInhds fun α hα => (hval α hα).symm)
  -- continuity of the remaining factors
  have hp : Continuous fun α : ℝ => reflectionExponent γ α := by
    unfold reflectionExponent
    fun_prop
  have hΓ : ContinuousAt (fun α : ℝ => Real.Gamma (-reflectionExponent γ α)) γ :=
    ContinuousAt.comp (f := fun α : ℝ => -reflectionExponent γ α) (x := γ)
      ((Real.differentiableAt_Gamma (reflectionExponent_gamma_ne hγ hγirr)).continuousAt)
      hp.neg.continuousAt
  have hμp : Continuous fun α : ℝ => μ ^ reflectionExponent γ α :=
    continuous_const.rpow hp fun _ => Or.inl hμ.ne'
  unfold reflectionR
  exact ((hμp.continuousAt.tendsto.mul hΓ.tendsto).mul hp.continuousAt.tendsto).mul hRbar

/-- **The meromorphic representative is analytic at `γ`.** -/
theorem analyticAt_reflection_gamma {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hγirr : Irrational (γ ^ 2))
    (hBarRRepresentation : ∀ I : Set ℝ, IsCompact I → (∀ α ∈ I, γ / 2 < α ∧ α < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              (∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ)))
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR)
    (hRv : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (BR α) ZR : ℂ)) :
    AnalyticAt ℂ R (γ : ℂ) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have hγQ : γ < Q γ := by linarith
  refine analyticAt_of_meromorphicAt_of_tendsto_ofReal (hRm _ (ofReal_mem_horizontalStrip hhR γ))
    ?_
  have ht := tendsto_reflectionR_gamma P X M hγ hγ2 hμ hγirr hBarRRepresentation hBR
  have htc := (Complex.continuous_ofReal.tendsto _).comp ht
  rw [hRv γ (by linarith) hγQ]
  refine (htc.mono_left nhdsWithin_le_nhds).congr' ?_
  have hJ : Ioo (γ / 2) (Q γ) ∈ 𝓝 γ := Ioo_mem_nhds (by linarith) hγQ
  filter_upwards [nhdsWithin_le_nhds hJ] with α hα
  exact (hRv α hα.1 hα.2).symm

/-- **`R(γ) ≠ 0`** when `γ²` is irrational. -/
theorem reflectionR_gamma_ne_zero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ μ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ) (hγirr : Irrational (γ ^ 2))
    {B : Ω → BrownianPath × BrownianPath} {Z : Ω → Measure ℝ}
    (hB : IsReflectionData P γ γ B Z) : reflectionR P γ μ γ B Z ≠ 0 := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have hpos := (reflectionBarR_positive_finite P γ γ hγ hγ2 ⟨by linarith, by linarith⟩ B Z hB).1
  have he : 0 < reflectionExponent γ γ := by
    unfold reflectionExponent
    exact div_pos (by linarith) hγ
  unfold reflectionR
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (Real.rpow_pos_of_pos hμ _).ne' ?_) he.ne')
    hpos.ne'
  exact Real.Gamma_ne_zero (reflectionExponent_gamma_ne hγ hγirr)

end DOZZ.Proofs

end
