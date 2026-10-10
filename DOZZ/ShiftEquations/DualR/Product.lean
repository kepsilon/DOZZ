/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Tkea
public import DOZZ.ShiftEquations.DualR.Limits
import DOZZ.ShiftEquations.Strip.Lastone
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# The limit of the crossed second dual seed

Multiplying the crossed seed (`tkea`) by `η` and letting `η → 0⁺`: the left side tends to
`2 R(ε) R(Q + θ)` (zero mode), and the right side to `λ ρ (-4)`, where `λ` is the limit of `L/η`,
`ρ` that of `η R(γ/2 + η)` (first reflection shift), and `-4` that of `η C(ε, Q - η, Q - ε)`
(`DOZZ.structureConstant_lastone_limit`).
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The product identity** `2 R(ε) R(Q + θ) = λ ρ (-4)` for `ε = γ/2 - θ`. -/
theorem dualShift_product {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hSeed : ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (hShiftGluing : ∀ η : ℝ, (0 < η ∧ Q γ - 2 * η > γ) → ∀ α₂ α₃ : ℝ,
      (Q γ - η < α₂ ∧ α₂ < Q γ) → (Q γ - η < α₃ ∧ α₃ < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)))
    {hR : ℝ} (hhR : 0 < hR) {R : ℂ → ℂ} (hRm : MeromorphicOn R (horizontalStrip hR))
    {BR : ℝ → Ω → BrownianPath × BrownianPath} {ZR : Ω → Measure ℝ}
    (hBR : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (BR α) ZR)
    (hRv : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (BR α) ZR : ℂ))
    (hshift : ∀ᶠ z in codiscrete ℂ,
      R (z - γ / 2) = -(μ * Real.pi : ℂ) * R z /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    (hRγ : AnalyticAt ℂ R (γ : ℂ))
    {θ : ℝ} (hθ₁ : 0 < θ) (hθ₂ : θ < γ / 4)
    (hRe : AnalyticAt ℂ R ((γ / 2 - θ : ℝ) : ℂ)) (hRx : AnalyticAt ℂ R ((Q γ + θ : ℝ) : ℂ))
    (hg₁ : AnalyticAt ℂ Complex.Gamma (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ))) :
    R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ) * 2 =
      (-(1 / (γ : ℂ)) * lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) * lFun (1 + 4 / (γ : ℂ) ^ 2) *
        (lFun (1 - 2 * θ / γ))⁻¹) *
      (2 * (μ * Real.pi : ℂ) * R γ /
        ((γ : ℂ) * (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4)))) * (-4) := by
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  -- the crossed seed for all small `η > 0`
  have hRev : ∀ᶠ η : ℝ in 𝓝[>] 0, AnalyticAt ℂ R ((γ / 2 + η : ℝ) : ℂ) := by
    have hm : MeromorphicAt R ((γ / 2 : ℝ) : ℂ) := hRm _ (ofReal_mem_horizontalStrip hhR _)
    have hev := eventually_analyticAt_affine hm (a := 1) one_ne_zero
    filter_upwards [nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => hx.ne') hev] with η hη
    simpa using hη
  have h42 : 4 / γ = 2 * (2 / γ) := by ring
  have hpos : 0 < min (γ / 2) (4 / γ - γ) := lt_min (by linarith) (by linarith)
  have hT : ∀ᶠ η : ℝ in 𝓝[>] 0,
      R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ) *
          (structureConstant P M γ μ (Q γ - θ) (γ / 2 + η) (2 / γ + θ) : ℂ) =
        dualLC γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) *
          R ((γ / 2 + η : ℝ) : ℂ) *
            (structureConstant P M γ μ (γ / 2 - θ) (Q γ - η) (2 / γ + θ) : ℂ) := by
    filter_upwards [hRev, Ioo_mem_nhdsGT hpos] with η hRa hη
    exact tkea P X M hγ hγ2 hμ hX hM hSeed hShiftGluing hhR hRm hBR hRv hθ₁ hθ₂ hη.1
      (lt_of_lt_of_le hη.2 (min_le_left _ _)) (lt_of_lt_of_le hη.2 (min_le_right _ _)) hRe hRx
      hRa hg₁
  -- the left side
  have hL : Tendsto (fun η : ℝ => (η : ℂ) * (R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ) *
      (structureConstant P M γ μ (Q γ - θ) (γ / 2 + η) (2 / γ + θ) : ℂ))) (𝓝[>] 0)
      (𝓝 (R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ) * 2)) := by
    have h1 := tendsto_mul_structureConstant_chargeZero P X M hγ hγ2 hμ hX hM
      (a := Q γ - θ) (b := γ / 2) (c := 2 / γ + θ) (by rw [hQ]; ring) (by linarith)
      (by linarith) (by linarith)
    have h1c := (Complex.continuous_ofReal.tendsto _).comp h1
    have h := (tendsto_const_nhds (x := R ((γ / 2 - θ : ℝ) : ℂ) * R ((Q γ + θ : ℝ) : ℂ))).mul h1c
    simp only [Complex.ofReal_ofNat] at h
    refine h.congr' (Eventually.of_forall fun η => ?_)
    simp only [Function.comp_apply]
    push_cast
    ring
  -- the right side
  have hRt : Tendsto (fun η : ℝ => (η : ℂ) *
      (dualLC γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) *
        R ((γ / 2 + η : ℝ) : ℂ) *
          (structureConstant P M γ μ (γ / 2 - θ) (Q γ - η) (2 / γ + θ) : ℂ))) (𝓝[>] 0)
      (𝓝 ((-(1 / (γ : ℂ)) * lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) *
        lFun (1 + 4 / (γ : ℂ) ^ 2) * (lFun (1 - 2 * θ / γ))⁻¹) *
        (2 * (μ * Real.pi : ℂ) * R γ /
          ((γ : ℂ) * (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4)))) * (-4))) := by
    have h4 := tendsto_dualLC_div (γ := γ) hγ hθ₁
    have h3 := tendsto_mul_reflection_pole (μ := μ) hγ hγ2 hRγ hshift
    have h2 := structureConstant_lastone_limit P X M γ μ (γ / 2 - θ) hγ hγ2 hμ
      ⟨by linarith, lt_min (by linarith) (by linarith)⟩ hX hM
    have h2' : Tendsto (fun η : ℝ => η * structureConstant P M γ μ (γ / 2 - θ) (Q γ - η)
        (2 / γ + θ)) (𝓝[>] 0) (𝓝 (-4)) := by
      have e : Q γ - (γ / 2 - θ) = 2 / γ + θ := by rw [hQ]; ring
      rw [e] at h2
      exact h2
    have h2c := (Complex.continuous_ofReal.tendsto _).comp h2'
    have h := (h4.mul h3).mul h2c
    simp only [Complex.ofReal_neg, Complex.ofReal_ofNat] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
    simp only [Function.comp_apply]
    push_cast
    field_simp
  exact tendsto_nhds_unique hL (hRt.congr' (hT.mono fun η h => by simp only [h]))

end DOZZ.Proofs

end
