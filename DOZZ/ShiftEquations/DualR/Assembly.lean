/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Generic
public import DOZZ.ShiftEquations.DualR.AnalyticR
public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.ShiftEquations.Residual.Joint
import DOZZ.ShiftEquations.Gluing.Meromorphy
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# The dual shift of the reflection coefficient, from its inputs

`reflectionR_dual_shift_unknown_constant_of_deps` proves the conclusion of
`DOZZ.reflectionR_dual_shift_unknown_constant` from the conclusions of
`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionBarR_holomorphic_representation`,
`DOZZ.structureConstant_reflected_shift_and_gluing`, `DOZZ.reflectionR_inversion_meromorphic` and
`DOZZ.dual_crossing_seed_two`, at the given field, chaos, coupling and cosmological constant.

Route ([KRV, §10.5]): the dual shift holds at generic real points just below `γ/2`
(`dualShift_eventually`), hence by the identity theorem near every point of the strip of the
representative `R` from `DOZZ.reflectionR_first_shift_meromorphic`; cutting `R` off outside a
thinner strip makes it hold along the codiscrete filter of `ℂ`. The constant `c_γ = (γ²/4) μπ R(γ)`
is nonzero since `R(γ) ≠ 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **`DOZZ.reflectionR_dual_shift_unknown_constant` from its inputs.** -/
theorem reflectionR_dual_shift_unknown_constant_of_deps
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hFirstShift : ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    (hBarRRepresentation : ∀ I : Set ℝ, IsCompact I → (∀ α ∈ I, γ / 2 < α ∧ α < Q γ) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ (∀ α ∈ I, IsReflectionData P γ α (B α) Z) ∧
          ∃ V : Set ℂ, IsOpen V ∧ (∀ α ∈ I, (α : ℂ) ∈ V) ∧
            ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
              (∀ α ∈ I, f (α : ℂ) = (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
              DifferentiableOn ℂ (fun z => rbarCoefficient γ z * f z) V ∧
              (∀ α ∈ I, rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                (reflectionBarR P γ α (B α) Z : ℂ)))
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
    (hInversion : ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ, R z * R (2 * Q γ - z) = 1)
    (hSeed : ∀ α ε α' : ℝ, α < Q γ → ε < Q γ → α' < Q γ → 2 * Q γ + 2 / γ < α + ε + α' →
      ∃ Bε Bα : Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ ε Bε Z ∧
          IsReflectionData P γ α Bα Z ∧
          reflectionR P γ μ ε Bε Z * structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
            dualCrossingL γ ε α α' * reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α') :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∃ cγ : ℂ, cγ ≠ 0 ∧
                cγ = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧
                ∀ᶠ z in codiscrete ℂ,
                  R z = -cγ * R (z + 2 / γ) /
                    (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
                      lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)) := by
  obtain ⟨B, Z, hproj, hBd, h, hh, R, hRm, hRv, hshift⟩ := hFirstShift
  obtain ⟨B₅, Z₅, -, hB₅, h₅, hh₅, R₅, hR₅m, hR₅v, hinv⟩ := hInversion
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hRγ := analyticAt_reflection_gamma P X M hγ hγ2 hμ hγirr hBarRRepresentation hh hRm hBd hRv
  have hev := dualShift_eventually P X M hγ hγ2 hγirr hμ hX hM hSeed hShiftGluing hh hRm hBd hRv hshift
    hRγ hh₅ hR₅m hB₅ hR₅v hinv
  set cγ : ℂ := (γ : ℂ) ^ 2 / 4 * (μ * Real.pi : ℂ) * R γ with hcγ
  set D : ℂ → ℂ := fun z => lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
    lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ) with hD
  set G : ℂ → ℂ := fun z => -cγ * R (z + ((2 / γ : ℝ) : ℂ)) / D z with hG
  have hGm : MeromorphicOn G (horizontalStrip h) := by
    intro z hz
    have hRs := MeromorphicOn.comp_add_ofReal (h := h) hRm (2 / γ) z hz
    have hDm : MeromorphicAt D z :=
      ((meromorphicAt_lFun_comp' analyticAt_const).fun_mul
        (meromorphicAt_lFun_comp' (f := fun w : ℂ => 2 * w / γ) (by fun_prop))).fun_mul
        (meromorphicAt_lFun_comp' (f := fun w : ℂ => 2 + 4 / (γ : ℂ) ^ 2 - 2 * w / γ)
          (by fun_prop))
    exact ((MeromorphicAt.const _ z).fun_mul hRs).fun_div hDm
  -- frequent agreement near `3γ/8`
  have hfreq : ∃ᶠ z in 𝓝[≠] ((γ / 2 - γ / 8 : ℝ) : ℂ), R z = G z := by
    have ht := tendsto_affine_nhdsNE (z₀ := ((γ / 2 - γ / 8 : ℝ) : ℂ)) (a := -1) (by norm_num)
    refine ht.frequently (Eventually.frequently ?_)
    filter_upwards [hev] with u hu
    have e : ((γ / 2 - γ / 8 : ℝ) : ℂ) + (u : ℂ) * (-1) = ((γ / 2 - (γ / 8 + u) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e, hu]
    simp only [hG, hD, hcγ]
    push_cast
    ring
  have hrel : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w,
      R (z + ((0 : ℝ) : ℂ)) = (fun z => -cγ / D z) z * R (z + ((2 / γ : ℝ) : ℂ)) := by
    intro w hw
    have hg := ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hRm hGm
      (isPreconnected_horizontalStrip h) (ofReal_mem_horizontalStrip hh _) hw hfreq
    filter_upwards [hg] with z hz
    rw [Complex.ofReal_zero, add_zero, hz]
    simp only [hG]
    ring
  have hcut := cutoff_relation_codiscrete hh 0 (2 / γ) hrel
  have hRt : ∀ x : ℝ, cutoffStrip (h / 2) R (x : ℂ) = R x := fun x =>
    cutoffStrip_of_lt (by simp only [Complex.ofReal_im, abs_zero]; positivity)
  refine ⟨B, Z, hproj, hBd, h / 2, half_pos hh, cutoffStrip (h / 2) R,
    meromorphicOn_cutoffStrip hRm (half_le_self hh.le), fun α h1 h2 => by rw [hRt]; exact hRv α h1 h2,
    (γ : ℂ) ^ 2 / 4 * (μ * Real.pi : ℂ) * cutoffStrip (h / 2) R γ, ?_, rfl, ?_⟩
  · rw [hRt, hRv γ (by linarith) (by linarith)]
    have hR0 := reflectionR_gamma_ne_zero P (μ := μ) hγ hγ2 hμ hγirr (hBd γ (by linarith)
      (by linarith))
    refine mul_ne_zero (mul_ne_zero (div_ne_zero (pow_ne_zero 2 hγc) (by norm_num)) ?_)
      (Complex.ofReal_ne_zero.mpr hR0)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ.ne')
      (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  · filter_upwards [hcut] with z hz
    rw [Complex.ofReal_zero, add_zero] at hz
    rw [hz, hRt]
    simp only [hD, hcγ]
    push_cast
    ring

end DOZZ.Proofs

end
