/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.Reflected
public import DOZZ.ShiftEquations.Residual.Joint
public import DOZZ.Statements.FourPoint.FourPointT
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.ShiftEquations.Rbar.Multiplier
import DOZZ.ShiftEquations.Shift.FirstShift
import DOZZ.Hypergeom.ODE.SlitPlaneGluing
import DOZZ.Complex.Basic

/-!
# The reflected shift and gluing from the two first shifts and the two γ/2 diagonal formulas

The reflected shift `R(z + γ/2) C(2Q - z - γ/2) = -𝒜(γ/2, z, α₂, α₃) C(z - γ/2)/(πμ)` holds at real
`z` near `Q` (`reflected_coefficient_real` with the first reflection shift and the Gamma identity),
hence near every point of the common strip. With the first structure shift
(`DOZZ.structureConstant_first_shift_strip`) at `z - γ/2` it gives the gluing
`C(z) = R(z) C(2Q - z)` near every point. Cutting `C` and `R` off outside a thinner strip makes both
identities hold along the codiscrete filter of `ℂ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- **The reflected shift and gluing from its inputs.** `hFirstShift` and `hFirstStrip` are the conclusions of
`DOZZ.reflectionR_first_shift_meromorphic` and `DOZZ.structureConstant_first_shift_strip` at the
given field, chaos, coupling and charges; `hDiagonal` and `hReflected` are those of the classification
`DOZZ.degenerateFourPoint_diagonal_classification` (at `χ = γ/2`) and the reflected diagonal formula
`DOZZ.gammaHalf_reflected_formula` at the fixed `α₂, α₃`. -/
theorem structureConstant_reflected_shift_and_gluing_of_deps
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hFirstShift : ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) ∧
          ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
            MeromorphicOn R {z | |z.im| < h} ∧
            (∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ)) ∧
            ∀ᶠ z in codiscrete ℂ,
              R (z - γ / 2) =
                -(μ * Real.pi : ℂ) * R z /
                  (lFun (-((γ : ℂ) ^ 2) / 4) *
                    lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                    lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    (hFirstStrip : ∃ h : ℝ, 0 < h ∧ ∃ C : ℂ → ℂ,
      MeromorphicOn C {z | |z.im| < h} ∧
      (∀ α : ℝ, 2 * η < α → α < Q γ → C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
      ∀ᶠ z in codiscrete ℂ,
        C (z + γ / 2) =
          -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2))
    (hDiagonal : ∀ {H : ℂ → ℂ → ℂ → ℂ → ℂ}, IsGaussHypergeometricFamily H → ∀ α₁ : ℝ,
      α₁ < Q γ → 2 * Q γ + γ / 2 < α₁ + α₂ + α₃ →
      let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
      let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
      let c := gaussParameterC γ (γ / 2) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            (‖gaussFMinus H a b c z‖ ^ 2 +
              gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2))
    (hReflected : ∀ {H : ℂ → ℂ → ℂ → ℂ → ℂ}, IsGaussHypergeometricFamily H → ∀ α₁ : ℝ,
      α₁ < Q γ → 2 * Q γ + γ / 2 < α₁ + α₂ + α₃ → Q γ - α₁ < γ / 2 →
      (∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ γ * (Q γ - α₁) < ξ ∧
        γ * (Q γ - α₁) < (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2)) →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
        ∃ Z : Ω → Measure ℝ,
          IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ α₁ (B α₁) Z ∧
          let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
          let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
          let c := gaussParameterC γ (γ / 2) α₁
          ∀ z ∈ gaussCutPlane,
            fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
              structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
                  ‖gaussFMinus H a b c z‖ ^ 2 +
                reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                    ‖gaussFPlus H a b c z‖ ^ 2) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) =
                  (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                R (z + γ / 2) * C (2 * Q γ - z - γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2)) := by
  obtain ⟨hη0, hηγ⟩ := hη
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have h2γ : γ / 16 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    linarith only [mul_self_lt_mul_self hγ.le hγ2]
  obtain ⟨B, Z, hSLP, hRD, h₁, hh₁, R, hRm, hRval, hRshift⟩ := hFirstShift
  obtain ⟨h₂, hh₂, C, hCm, hCval, hCshift⟩ := hFirstStrip
  obtain ⟨H, hH⟩ := gauss_hypergeometric_exists
  set h := min h₁ h₂ with hhdef
  have hh : 0 < h := lt_min hh₁ hh₂
  have hRm' : MeromorphicOn R (horizontalStrip h) := fun z hz =>
    hRm z (show |z.im| < h₁ from lt_of_lt_of_le (show |z.im| < h from hz) (min_le_left _ _))
  have hCm' : MeromorphicOn C (horizontalStrip h) := fun z hz =>
    hCm z (show |z.im| < h₂ from lt_of_lt_of_le (show |z.im| < h from hz) (min_le_right _ _))
  -- the reflected shift at real charges near `Q`
  have hreal : ∀ α₁ : ℝ, Q γ - γ / 16 < α₁ → α₁ < Q γ →
      R ((α₁ : ℂ) + γ / 2 - γ / 2) = -(μ * Real.pi : ℂ) * R ((α₁ : ℂ) + γ / 2) /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * ((α₁ : ℂ) + γ / 2) / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * ((α₁ : ℂ) + γ / 2) / 2)) →
      R ((α₁ : ℂ) + γ / 2) * C (2 * Q γ - (α₁ : ℂ) - γ / 2) =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α₁ (α₂ : ℂ) (α₃ : ℂ) *
          C ((α₁ : ℂ) - γ / 2) := by
    intro α₁ h1 h2 hshift
    have hα₁ : γ / 2 < α₁ := by rw [hQ] at h1; linarith
    have hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃ := by linarith [hα₂.1, hα₃.1]
    have hcoef := reflected_coefficient_real P X M hγ hγ2 hDiagonal hReflected hH hRD h1 h2 hs
    have hc := gaussParameterC_half_mem hγ hγ2 h1 h2
    have hP1 := gaussCoefficientRatio_mul_eq_shiftCoeffA_half (α₂ := α₂) (α₃ := α₃) hγ
      (ne_of_lt hc.2)
    have hD : lFun (-((γ : ℂ) ^ 2) / 4) *
        lFun ((γ : ℂ) * ((α₁ : ℂ) + γ / 2) / 2 - (γ : ℂ) ^ 2 / 4) *
        lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * ((α₁ : ℂ) + γ / 2) / 2) =
        lFun (-((γ / 2 : ℝ) : ℂ) ^ 2) * lFun (((γ / 2 : ℝ) : ℂ) * α₁) *
          lFun (2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * α₁) := by
      rw [show -((γ : ℂ) ^ 2) / 4 = -((γ / 2 : ℝ) : ℂ) ^ 2 by push_cast; ring,
        show (γ : ℂ) * ((α₁ : ℂ) + γ / 2) / 2 - (γ : ℂ) ^ 2 / 4 = ((γ / 2 : ℝ) : ℂ) * α₁ by
          push_cast; ring,
        show (2 : ℂ) + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * ((α₁ : ℂ) + γ / 2) / 2 =
          2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * α₁ by push_cast; ring]
    have hγα₁ : γ * α₁ < γ * Q γ := mul_lt_mul_of_pos_left h2 hγ
    have hγα₁' : γ * (Q γ - γ / 16) < γ * α₁ := mul_lt_mul_of_pos_left h1 hγ
    have hγQ : γ * Q γ = 2 + γ ^ 2 / 2 := by rw [hQ]; field_simp
    have hγsq : γ ^ 2 < 4 := by linarith only [mul_self_lt_mul_self hγ.le hγ2]
    have hDne : lFun (-((γ / 2 : ℝ) : ℂ) ^ 2) * lFun (((γ / 2 : ℝ) : ℂ) * α₁) *
        lFun (2 + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * α₁) ≠ 0 := by
      rw [show (2 : ℂ) + ((γ / 2 : ℝ) : ℂ) ^ 2 - ((γ / 2 : ℝ) : ℂ) * α₁ =
          ((2 + (γ / 2) ^ 2 - γ / 2 * α₁ : ℝ) : ℂ) by push_cast; ring,
        show -((γ / 2 : ℝ) : ℂ) ^ 2 = ((-(γ / 2) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        show ((γ / 2 : ℝ) : ℂ) * α₁ = ((γ / 2 * α₁ : ℝ) : ℂ) by push_cast; ring,
        lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR]
      exact_mod_cast mul_ne_zero (mul_ne_zero
        (lR_ne_zero_of_mem_neg (by linarith only [hγsq])
          (by linarith only [pow_pos (half_pos hγ) 2]))
        (lR_ne_zero_of_mem_one_two (by linarith only [hγα₁', hγQ, sq_nonneg γ])
          (by linarith only [hγα₁, hγQ, hγsq])))
        (lR_ne_zero_of_mem_one_two (by linarith only [hγα₁, hγQ])
          (by linarith only [hγα₁', hγQ, hγsq]))
    have hRα : R (α₁ : ℂ) = (reflectionR P γ μ α₁ (B α₁) Z : ℂ) := hRval α₁ hα₁ h2
    have hC₁ : C (2 * Q γ - (α₁ : ℂ) - γ / 2) =
        (structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ : ℂ) := by
      rw [show (2 * Q γ - (α₁ : ℂ) - γ / 2) = ((2 * Q γ - α₁ - γ / 2 : ℝ) : ℂ) by push_cast; ring]
      exact hCval _ (by linarith) (by linarith)
    have hC₂ : C ((α₁ : ℂ) - γ / 2) = (structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ : ℂ) := by
      rw [show ((α₁ : ℂ) - γ / 2) = ((α₁ - γ / 2 : ℝ) : ℂ) by push_cast; ring]
      exact hCval _ (by rw [hQ] at h1; linarith) (by linarith)
    rw [add_sub_cancel_right, hD] at hshift
    have hμπ : ((μ : ℂ) * Real.pi) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ.ne') (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hcoef' : R (α₁ : ℂ) * C (2 * Q γ - (α₁ : ℂ) - γ / 2) =
        (gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
          (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) : ℂ) *
          C ((α₁ : ℂ) - γ / 2) := by
      rw [hRα, hC₁, hC₂]
      exact_mod_cast hcoef
    have key := reflected_shift_algebra hμπ hDne hshift hcoef' hP1
    rw [key, show ((γ / 2 : ℝ) : ℂ) = (γ : ℂ) / 2 by push_cast; ring]
    ring
  -- the reflected shift near every point of the strip
  set x₀ : ℝ := Q γ - γ / 32 with hx₀
  have hx₀1 : Q γ - γ / 16 < x₀ := by rw [hx₀]; linarith
  have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
  have hshiftloc := (eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hRshift)
    ((x₀ : ℂ) + γ / 2)
  have hshiftpt : ∀ᶠ t : ℝ in 𝓝[≠] x₀,
      R ((t : ℂ) + γ / 2 - γ / 2) = -(μ * Real.pi : ℂ) * R ((t : ℂ) + γ / 2) /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * ((t : ℂ) + γ / 2) / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * ((t : ℂ) + γ / 2) / 2)) :=
    (tendsto_ofReal_nhdsNE_slice x₀).eventually
      (ShiftGluing.eventually_comp_add (z := (x₀ : ℂ)) ((γ : ℂ) / 2) hshiftloc)
  set f : ℂ → ℂ := fun z => R (z + ((γ / 2 : ℝ) : ℂ)) * C (((2 * Q γ - γ / 2 : ℝ) : ℂ) - z)
    with hfdef
  set g : ℂ → ℂ := fun z => (-(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ)) *
    C (z + ((-(γ / 2) : ℝ) : ℂ)) with hgdef
  have hfg_real : ∀ᶠ t : ℝ in 𝓝[≠] x₀, f t = g t := by
    filter_upwards [hshiftpt, eventually_nhdsWithin_of_eventually_nhds
      (eventually_of_mem (Ioo_mem_nhds hx₀1 hx₀2) fun t ht => ht)] with t ht hIt
    have := hreal t hIt.1 hIt.2 ht
    simp only [hfdef, hgdef]
    rw [show (t : ℂ) + ((γ / 2 : ℝ) : ℂ) = (t : ℂ) + γ / 2 by push_cast; ring,
      show ((2 * Q γ - γ / 2 : ℝ) : ℂ) - (t : ℂ) = 2 * Q γ - (t : ℂ) - γ / 2 by push_cast; ring,
      show (t : ℂ) + ((-(γ / 2) : ℝ) : ℂ) = (t : ℂ) - γ / 2 by push_cast; ring]
    exact this
  have hfm : MeromorphicOn f (horizontalStrip h) :=
    (MeromorphicOn.comp_add_ofReal hRm' (γ / 2)).mul
      (MeromorphicOn.comp_ofReal_sub hCm' (2 * Q γ - γ / 2))
  have hgm : MeromorphicOn g (horizontalStrip h) := fun z hz =>
    ((MeromorphicAt.const _ z).mul ((meromorphic_shiftCoeffA γ _ _ _) z)).mul
      ((MeromorphicOn.comp_add_ofReal hCm' (-(γ / 2))) z hz)
  have hx₀S : (x₀ : ℂ) ∈ horizontalStrip h := by
    change |((x₀ : ℝ) : ℂ).im| < h
    simpa using hh
  have hEq : ∀ w ∈ horizontalStrip h, f =ᶠ[𝓝[≠] w] g := fun w hw =>
    ShiftGluing.meromorphicOn_eventuallyEq_of_frequently hfm hgm
      (isPreconnected_horizontalStrip h) hx₀S hw
      ((tendsto_ofReal_nhdsNE_slice x₀).frequently hfg_real.frequently)
  -- the gluing near every point of the strip
  have hglue : ∀ w ∈ horizontalStrip h, ∀ᶠ z in 𝓝[≠] w, C z = R z * C (2 * Q γ - z) := by
    intro w hw
    have hw' : w - ((γ / 2 : ℝ) : ℂ) ∈ horizontalStrip h := by
      simpa [sub_eq_add_neg] using add_ofReal_mem_horizontalStrip_glue hw (-(γ / 2))
    have h1 := ShiftGluing.eventually_comp_sub (z := w) ((γ / 2 : ℝ) : ℂ)
      ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hCshift) (w - ((γ / 2 : ℝ) : ℂ)))
    have h2 := ShiftGluing.eventually_comp_sub (z := w) ((γ / 2 : ℝ) : ℂ) (hEq _ hw')
    filter_upwards [h1, h2] with z hz1 hz2
    simp only [hfdef, hgdef] at hz2
    rw [show z - ((γ / 2 : ℝ) : ℂ) + ((γ / 2 : ℝ) : ℂ) = z by ring,
      show ((2 * Q γ - γ / 2 : ℝ) : ℂ) - (z - ((γ / 2 : ℝ) : ℂ)) = 2 * Q γ - z by push_cast; ring,
      show z - ((γ / 2 : ℝ) : ℂ) + ((-(γ / 2) : ℝ) : ℂ) = z - γ / 2 - γ / 2 by push_cast; ring,
      show z - ((γ / 2 : ℝ) : ℂ) = z - γ / 2 by push_cast; ring] at hz2
    rw [show z - ((γ / 2 : ℝ) : ℂ) + γ / 2 = z by push_cast; ring,
      show z - ((γ / 2 : ℝ) : ℂ) - γ / 2 = z - γ / 2 - γ / 2 by push_cast; ring,
      show z - ((γ / 2 : ℝ) : ℂ) = z - γ / 2 by push_cast; ring] at hz1
    rw [hz1, hz2]
  -- packaging with cut-offs
  have himsub : ∀ (z : ℂ) (t : ℝ), |((t : ℂ) - z).im| = |z.im| := fun z t => by simp [abs_neg]
  have himadd : ∀ (z : ℂ) (t : ℝ), |(z + (t : ℂ)).im| = |z.im| := fun z t => by simp
  refine ⟨B, Z, hSLP, hRD, h / 2, half_pos hh, cutoffStrip (h / 2) C, cutoffStrip (h / 2) R,
    meromorphicOn_cutoffStrip hCm' (half_le_self hh.le),
    meromorphicOn_cutoffStrip hRm' (half_le_self hh.le), fun α h1 h2 => ?_, fun α h1 h2 => ?_,
    ?_, ?_⟩
  · rw [cutoffStrip_of_lt (by simpa using half_pos hh)]
    exact hCval α h1 h2
  · rw [cutoffStrip_of_lt (by simpa using half_pos hh)]
    exact hRval α h1 h2
  · rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
    intro x
    have hzero : ∀ z : ℂ, ¬ |z.im| < h / 2 → cutoffStrip (h / 2) C z =
        cutoffStrip (h / 2) R z * cutoffStrip (h / 2) C (2 * Q γ - z) := fun z hz => by
      rw [cutoffStrip_of_not_lt hz, cutoffStrip_of_not_lt hz, zero_mul]
    by_cases hx : |x.im| < h
    · filter_upwards [hglue x hx] with z hz
      by_cases hzk : |z.im| < h / 2
      · have hz' : |(2 * (Q γ : ℂ) - z).im| < h / 2 := by
          rw [show (2 * (Q γ : ℂ) - z) = ((2 * Q γ : ℝ) : ℂ) - z by push_cast; ring, himsub]
          exact hzk
        rw [cutoffStrip_of_lt hzk, cutoffStrip_of_lt hzk, cutoffStrip_of_lt hz']
        exact hz
      · exact hzero z hzk
    · have hopen : IsOpen {w : ℂ | h / 2 < |w.im|} :=
        isOpen_lt continuous_const Complex.continuous_im.abs
      have hxo : h / 2 < |x.im| := by
        have := not_lt.mp hx
        linarith
      filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hxo)] with z hz
      exact hzero z (not_lt.mpr (le_of_lt hz))
  · rw [eventually_codiscrete_iff_forall_eventually_nhdsNE]
    intro x
    have hzero : ∀ z : ℂ, ¬ |z.im| < h / 2 →
        cutoffStrip (h / 2) R (z + γ / 2) * cutoffStrip (h / 2) C (2 * Q γ - z - γ / 2) =
          -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
            cutoffStrip (h / 2) C (z - γ / 2) := fun z hz => by
      have e1 : ¬ |(z + γ / 2).im| < h / 2 := by
        rw [show z + (γ : ℂ) / 2 = z + ((γ / 2 : ℝ) : ℂ) by push_cast; ring, himadd]
        exact hz
      have e3 : ¬ |(z - γ / 2).im| < h / 2 := by
        rw [show z - (γ : ℂ) / 2 = z + ((-(γ / 2) : ℝ) : ℂ) by push_cast; ring, himadd]
        exact hz
      rw [cutoffStrip_of_not_lt e1, cutoffStrip_of_not_lt e3, zero_mul, mul_zero]
    by_cases hx : |x.im| < h
    · filter_upwards [hEq x hx] with z hz
      by_cases hzk : |z.im| < h / 2
      · have e1 : |(z + γ / 2).im| < h / 2 := by
          rw [show z + (γ : ℂ) / 2 = z + ((γ / 2 : ℝ) : ℂ) by push_cast; ring, himadd]
          exact hzk
        have e2 : |(2 * (Q γ : ℂ) - z - γ / 2).im| < h / 2 := by
          rw [show 2 * (Q γ : ℂ) - z - γ / 2 = ((2 * Q γ - γ / 2 : ℝ) : ℂ) - z by push_cast; ring,
            himsub]
          exact hzk
        have e3 : |(z - γ / 2).im| < h / 2 := by
          rw [show z - (γ : ℂ) / 2 = z + ((-(γ / 2) : ℝ) : ℂ) by push_cast; ring, himadd]
          exact hzk
        rw [cutoffStrip_of_lt e1, cutoffStrip_of_lt e2, cutoffStrip_of_lt e3]
        simp only [hfdef, hgdef] at hz
        rw [show z + ((γ / 2 : ℝ) : ℂ) = z + γ / 2 by push_cast; ring,
          show ((2 * Q γ - γ / 2 : ℝ) : ℂ) - z = 2 * Q γ - z - γ / 2 by push_cast; ring,
          show z + ((-(γ / 2) : ℝ) : ℂ) = z - γ / 2 by push_cast; ring] at hz
        exact hz
      · exact hzero z hzk
    · have hopen : IsOpen {w : ℂ | h / 2 < |w.im|} :=
        isOpen_lt continuous_const Complex.continuous_im.abs
      have hxo : h / 2 < |x.im| := by
        have := not_lt.mp hx
        linarith
      filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hxo)] with z hz
      exact hzero z (not_lt.mpr (le_of_lt hz))

end DOZZ.Proofs

end
