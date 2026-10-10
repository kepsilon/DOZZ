/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Product
public import DOZZ.ShiftEquations.DualR.Pointwise
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.ShiftEquations.Gluing.BandNear
import DOZZ.ShiftEquations.Shift.ShiftGluing
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.ShiftEquations.Gluing.Meromorphy
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.Reflection.RtheorAnalytic

/-!
# The dual shift of `R` at generic points below `γ/2`

At `ε = γ/2 - θ` with `θ = γ/8 + u`, the product identity (`dualShift_product`) and the
inversion turn into the dual shift (`dualShift_of_product`) as soon as `R` is analytic at
`ε`, `Q ± θ`, the inversion representative agrees with `R` there, and `2(ε - Q)/γ` avoids the poles
of `Γ`. All of these hold for every small `u ≠ 0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **The dual shift at generic points below `γ/2`.** -/
theorem dualShift_eventually {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2))
    (hμ : 0 < μ) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
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
    {h₅ : ℝ} (hh₅ : 0 < h₅) {R₅ : ℂ → ℂ} (hR₅m : MeromorphicOn R₅ (horizontalStrip h₅))
    {B₅ : ℝ → Ω → BrownianPath × BrownianPath} {Z₅ : Ω → Measure ℝ}
    (hB₅ : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B₅ α) Z₅)
    (hR₅v : ∀ α : ℝ, γ / 2 < α → α < Q γ → R₅ (α : ℂ) = (reflectionR P γ μ α (B₅ α) Z₅ : ℂ))
    (hinv : ∀ᶠ z in codiscrete ℂ, R₅ z * R₅ (2 * Q γ - z) = 1) :
    ∀ᶠ u : ℝ in 𝓝[≠] 0, R ((γ / 2 - (γ / 8 + u) : ℝ) : ℂ) =
      -((γ : ℂ) ^ 2 / 4 * (μ * Real.pi : ℂ) * R γ) *
        R (((γ / 2 - (γ / 8 + u) : ℝ) : ℂ) + 2 / γ) /
          (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * ((γ / 2 - (γ / 8 + u) : ℝ) : ℂ) / γ) *
            lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * ((γ / 2 - (γ / 8 + u) : ℝ) : ℂ) / γ)) := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  have hγh : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ (by norm_num) hγ]
    nlinarith
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  -- the two representatives agree as germs on the common strip
  set h' : ℝ := min hR h₅ with hh'
  have hh'0 : 0 < h' := lt_min hhR hh₅
  have hsub₁ : horizontalStrip h' ⊆ horizontalStrip hR := fun z hz =>
    lt_of_lt_of_le (show |z.im| < h' from hz) (min_le_left _ _)
  have hsub₂ : horizontalStrip h' ⊆ horizontalStrip h₅ := fun z hz =>
    lt_of_lt_of_le (show |z.im| < h' from hz) (min_le_right _ _)
  have hgerm : ∀ w ∈ horizontalStrip h', R =ᶠ[𝓝[≠] w] R₅ := by
    intro w hw
    set x₀ : ℝ := (γ / 2 + Q γ) / 2 with hx₀
    have hx₀1 : γ / 2 < x₀ := by rw [hx₀]; linarith
    have hx₀2 : x₀ < Q γ := by rw [hx₀]; linarith
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] x₀, R t = R₅ t :=
      eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_of_mem
        (Ioo_mem_nhds hx₀1 hx₀2) fun t ht => by
          rw [hRv t ht.1 ht.2, hR₅v t ht.1 ht.2, reflectionR_eq_of_isReflectionData P P γ μ t
            (BR t) ZR (B₅ t) Z₅ (hBR t ht.1 ht.2) (hB₅ t ht.1 ht.2)])
    exact ShiftGluing.meromorphicOn_eventuallyEq_of_frequently (hRm.mono_set hsub₁)
      (hR₅m.mono_set hsub₂) (isPreconnected_horizontalStrip h')
      (ofReal_mem_horizontalStrip hh'0 x₀) hw
      ((tendsto_ofReal_nhdsNE_slice x₀).frequently hev.frequently)
  -- the generic conditions
  have e1 : ∀ᶠ u : ℝ in 𝓝[≠] 0, AnalyticAt ℂ R ((γ / 2 - γ / 8 + u * (-1) : ℝ) : ℂ) :=
    eventually_ofReal_affine (by norm_num)
      (hRm _ (ofReal_mem_horizontalStrip hhR _)).eventually_analyticAt
  have e2 : ∀ᶠ u : ℝ in 𝓝[≠] 0, AnalyticAt ℂ R ((Q γ + γ / 8 + u * 1 : ℝ) : ℂ) :=
    eventually_ofReal_affine one_ne_zero
      (hRm _ (ofReal_mem_horizontalStrip hhR _)).eventually_analyticAt
  have e3 : ∀ᶠ u : ℝ in 𝓝[≠] 0, AnalyticAt ℂ R ((Q γ - γ / 8 + u * (-1) : ℝ) : ℂ) :=
    eventually_ofReal_affine (by norm_num)
      (hRm _ (ofReal_mem_horizontalStrip hhR _)).eventually_analyticAt
  have e4 : ∀ᶠ u : ℝ in 𝓝[≠] 0, AnalyticAt ℂ R₅ ((Q γ + γ / 8 + u * 1 : ℝ) : ℂ) :=
    eventually_ofReal_affine one_ne_zero
      (hR₅m _ (ofReal_mem_horizontalStrip hh₅ _)).eventually_analyticAt
  have e5 : ∀ᶠ u : ℝ in 𝓝[≠] 0, AnalyticAt ℂ R₅ ((Q γ - γ / 8 + u * (-1) : ℝ) : ℂ) :=
    eventually_ofReal_affine (by norm_num)
      (hR₅m _ (ofReal_mem_horizontalStrip hh₅ _)).eventually_analyticAt
  have e6 : ∀ᶠ u : ℝ in 𝓝[≠] 0, R₅ ((Q γ + γ / 8 + u * 1 : ℝ) : ℂ) *
      R₅ (2 * Q γ - ((Q γ + γ / 8 + u * 1 : ℝ) : ℂ)) = 1 :=
    eventually_ofReal_affine (p := fun z => R₅ z * R₅ (2 * Q γ - z) = 1) one_ne_zero
      ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hinv) _)
  have e7 : ∀ᶠ u : ℝ in 𝓝[≠] 0,
      ∀ n : ℕ, dualArg₁ γ ((γ / 2 - γ / 8 + u * (-1) : ℝ) : ℂ) ≠ -(n : ℂ) := by
    have hc := eventually_affine_ne_neg_nat (c := 2 / (γ : ℂ)) (d := -(2 * Q γ / γ))
      (div_ne_zero two_ne_zero hγc)
    have h := eventually_ofReal_affine (x₀ := γ / 2 - γ / 8) (s := -1) (by norm_num)
      ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hc) _)
    filter_upwards [h] with u hu n
    have e : dualArg₁ γ ((γ / 2 - γ / 8 + u * (-1) : ℝ) : ℂ) =
        2 / (γ : ℂ) * ((γ / 2 - γ / 8 + u * (-1) : ℝ) : ℂ) + -(2 * Q γ / γ) := by
      unfold dualArg₁
      ring
    rw [e]
    exact hu n
  have e8 : ∀ᶠ u : ℝ in 𝓝[≠] 0, u ∈ Ioo (-(γ / 16)) (γ / 16) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [e1, e2, e3, e4, e5, e6, e7, e8] with u a1 a2 a3 a4 a5 a6 a7 a8
  set θ : ℝ := γ / 8 + u with hθ
  have hθ₁ : 0 < θ := by rw [hθ]; linarith [a8.1]
  have hθ₂ : θ < γ / 4 := by rw [hθ]; linarith [a8.2]
  have r1 : (γ / 2 - γ / 8 + u * (-1) : ℝ) = γ / 2 - θ := by rw [hθ]; ring
  have r2 : (Q γ + γ / 8 + u * 1 : ℝ) = Q γ + θ := by rw [hθ]; ring
  have r3 : (Q γ - γ / 8 + u * (-1) : ℝ) = Q γ - θ := by rw [hθ]; ring
  rw [r1] at a1 a7
  rw [r2] at a2 a4 a6
  rw [r3] at a3 a5
  -- the inversion for `R`
  have hxp : R ((Q γ + θ : ℝ) : ℂ) = R₅ ((Q γ + θ : ℝ) : ℂ) :=
    eq_of_eventuallyEq_nhdsNE_of_continuousAt
      (hgerm _ (ofReal_mem_horizontalStrip hh'0 _)) a2.continuousAt a4.continuousAt
  have hxm : R ((Q γ - θ : ℝ) : ℂ) = R₅ ((Q γ - θ : ℝ) : ℂ) :=
    eq_of_eventuallyEq_nhdsNE_of_continuousAt
      (hgerm _ (ofReal_mem_horizontalStrip hh'0 _)) a3.continuousAt a5.continuousAt
  have hinvR : R ((Q γ + θ : ℝ) : ℂ) * R ((Q γ - θ : ℝ) : ℂ) = 1 := by
    rw [hxp, hxm, show ((Q γ - θ : ℝ) : ℂ) = 2 * Q γ - ((Q γ + θ : ℝ) : ℂ) by push_cast; ring]
    exact a6
  have hprod := dualShift_product P X M hγ hγ2 hμ hX hM hSeed hShiftGluing hhR hRm hBR hRv hshift hRγ
    hθ₁ hθ₂ a1 a2 (analyticAt_Gamma_of_ne a7)
  exact dualShift_of_product hγ hγ2 hγirr hθ₁ hθ₂ hprod hinvR a7

end DOZZ.Proofs

end
