/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.Reflection
public import DOZZ.ShiftEquations.Shift.Window
public import DOZZ.ShiftEquations.TwoPole.Expansion
public import DOZZ.ShiftEquations.Rbar.Residue
public import Mathlib.Analysis.Meromorphic.Complex
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.ShiftEquations.Quotient.Divisors

/-!
# The unit-volume γ/2 shift near `Q`

With `p(z) = 2(Q - z)/γ`, the unit-volume shift multiplier is
`m(z) = p(z) π / (l(-γ²/4) l(γz/2 - γ²/4) l(2 + γ²/2 - γz/2))`, meromorphic on `ℂ`. On the two-pole
slice `α' = Q - η`, `η/(η + γ/2) T(Q - η, -2η, 2/γ + η) = m(Q - η)`, so the residue identity
`(η + γ/2) R̄(Q - η - γ/2) = η T R̄(Q - η)` reads `R̄(a - γ/2) = m(a) R̄(a)` for `a = Q - η` close
to `Q` ([KRV, §10.2], unit-volume form of [KRV, (shift1)]).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace DOZZ.Proofs

/-- The unit-volume γ/2-shift multiplier. -/
noncomputable def rbarShiftMultiplier (γ : ℝ) (z : ℂ) : ℂ :=
  2 * ((Q γ : ℂ) - z) / γ * Real.pi /
    (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))

/-- The real form of the unit-volume shift multiplier. -/
noncomputable def rbarShiftMultiplierReal (γ a : ℝ) : ℝ :=
  2 * (Q γ - a) / γ * Real.pi /
    (lR (-(γ ^ 2) / 4) * lR (γ * a / 2 - γ ^ 2 / 4) * lR (2 + γ ^ 2 / 2 - γ * a / 2))

theorem rbarShiftMultiplier_ofReal (γ a : ℝ) :
    rbarShiftMultiplier γ a = (rbarShiftMultiplierReal γ a : ℂ) := by
  unfold rbarShiftMultiplier rbarShiftMultiplierReal
  rw [show -((γ : ℂ) ^ 2) / 4 = ((-(γ ^ 2) / 4 : ℝ) : ℂ) by push_cast; ring,
    show (γ : ℂ) * a / 2 - (γ : ℂ) ^ 2 / 4 = ((γ * a / 2 - γ ^ 2 / 4 : ℝ) : ℂ) by push_cast; ring,
    show 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * a / 2 = ((2 + γ ^ 2 / 2 - γ * a / 2 : ℝ) : ℂ) by
      push_cast; ring,
    lFun_ofReal_eq_lR, lFun_ofReal_eq_lR, lFun_ofReal_eq_lR]
  push_cast
  ring

/-- **The shift multiplier is meromorphic on `ℂ`.** -/
theorem meromorphicOn_rbarShiftMultiplier (γ : ℝ) :
    MeromorphicOn (rbarShiftMultiplier γ) Set.univ := by
  intro x _
  unfold rbarShiftMultiplier
  have hn : AnalyticAt ℂ (fun z : ℂ => 2 * ((Q γ : ℂ) - z) / γ * Real.pi) x := by fun_prop
  have h1 : MeromorphicAt (fun _ : ℂ => lFun (-((γ : ℂ) ^ 2) / 4)) x := MeromorphicAt.const _ _
  have h2 := meromorphicAt_lFun_comp (f := fun z : ℂ => (γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4)
    (z := x) (by fun_prop)
  have h3 := meromorphicAt_lFun_comp (f := fun z : ℂ => 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)
    (z := x) (by fun_prop)
  exact hn.meromorphicAt.div ((h1.mul h2).mul h3)

/-- The shift multiplier in Gamma-factor form. -/
theorem rbarShiftMultiplier_eq (γ : ℝ) (z : ℂ) :
    rbarShiftMultiplier γ z = 2 * ((Q γ : ℂ) - z) / γ * Real.pi *
      (lFun (-((γ : ℂ) ^ 2) / 4))⁻¹ *
      (Complex.Gamma (1 - ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4)) *
        (Complex.Gamma ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4))⁻¹) *
      (Complex.Gamma (1 - (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) *
        (Complex.Gamma (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))⁻¹) := by
  unfold rbarShiftMultiplier
  rw [← lFun_inv, ← lFun_inv, div_eq_mul_inv, mul_inv, mul_inv]
  ring

/-- **The shift multiplier is holomorphic on `γ < Re z < Q`.** -/
theorem differentiableOn_rbarShiftMultiplier {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    DifferentiableOn ℂ (rbarShiftMultiplier γ) {z | γ < z.re ∧ z.re < Q γ} := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hfun : rbarShiftMultiplier γ = fun z => 2 * ((Q γ : ℂ) - z) / γ * Real.pi *
      (lFun (-((γ : ℂ) ^ 2) / 4))⁻¹ *
      (Complex.Gamma (1 - ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4)) *
        (Complex.Gamma ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4))⁻¹) *
      (Complex.Gamma (1 - (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) *
        (Complex.Gamma (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))⁻¹) :=
    funext (rbarShiftMultiplier_eq γ)
  rw [hfun]
  have hu : DifferentiableAt ℂ (fun w : ℂ => (γ : ℂ) * w / 2 - (γ : ℂ) ^ 2 / 4) z := by
    fun_prop
  have hv : DifferentiableAt ℂ (fun w : ℂ => 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * w / 2) z := by
    fun_prop
  have hre1 : 0 < (1 - ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4)).re := by
    simp [Complex.mul_re, pow_two]
    have : γ * z.re < γ * Q γ := mul_lt_mul_of_pos_left hz.2 hγ
    have hγQ : γ * Q γ = 2 + γ ^ 2 / 2 := by rw [hQ]; field_simp
    nlinarith
  have hre2a : -1 < (1 - (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)).re := by
    simp [Complex.mul_re, pow_two]
    have : γ * γ < γ * z.re := mul_lt_mul_of_pos_left hz.1 hγ
    nlinarith
  have hre2b : (1 - (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)).re < 0 := by
    simp [Complex.mul_re, pow_two]
    have : γ * z.re < γ * Q γ := mul_lt_mul_of_pos_left hz.2 hγ
    have hγQ : γ * Q γ = 2 + γ ^ 2 / 2 := by rw [hQ]; field_simp
    nlinarith
  exact ((((differentiableAt_const _).sub differentiableAt_id).const_mul _ |>.div_const _
    |>.mul_const _).mul (differentiableAt_const _)).mul
      ((differentiableAt_Gamma_comp ((differentiableAt_const _).sub hu) hre1).mul
        (differentiableAt_inv_Gamma_comp hu)) |>.mul
      (((Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_mem_neg hre2a hre2b)).comp z
        ((differentiableAt_const _).sub hv)).mul (differentiableAt_inv_Gamma_comp hv))

/-- **On the two-pole slice the crossing multiplier gives the shift multiplier**:
`η/(η + γ/2) T(Q - η, -2η, 2/γ + η) = m(Q - η)`. -/
theorem slice_multiplier_eq {γ η : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hη : 0 < η)
    (hηγ : η < 2 / γ - γ / 2) (hη4 : η < γ / 4) :
    η / (η + γ / 2) * crossingMultiplier3Real γ (Q γ - η) (-(2 * η)) (2 / γ + η) =
      rbarShiftMultiplierReal γ (Q γ - η) := by
  obtain ⟨hQ, hQ2, hγh, h42, h2⟩ := slice_facts hγ hγ2
  have hγη : γ * η < 2 - γ ^ 2 / 2 := by
    have := mul_lt_mul_of_pos_left hηγ hγ
    have h' : γ * (2 / γ - γ / 2) = 2 - γ ^ 2 / 2 := by field_simp
    linarith
  have hγη4 : γ * η < γ ^ 2 / 4 := by
    have := mul_lt_mul_of_pos_left hη4 hγ
    nlinarith
  have hγsq : γ ^ 2 < 4 := by nlinarith
  have hγηpos : 0 < γ * η := mul_pos hγ hη
  unfold crossingMultiplier3Real rbarShiftMultiplierReal
  rw [show γ ^ 2 / 4 * ((2 / γ + η + (Q γ - η) + -(2 * η) - γ / 2 - 2 * Q γ) / γ) =
      -(γ * η / 2) - γ ^ 2 / 4 by rw [hQ]; field_simp; ring,
    show γ / 4 * (Q γ - η + -(2 * η) - (2 / γ + η) - Q γ) + 1 / 2 = -(γ * η) by
      field_simp; ring,
    show 1 - γ / 2 * (Q γ - (Q γ - η)) = 1 - γ * η / 2 by ring,
    show γ * -(2 * η) / 2 = -(γ * η) by ring,
    show γ * (Q γ - η) / 2 - γ ^ 2 / 4 = 1 - γ * η / 2 by rw [hQ]; field_simp; ring,
    show 2 + γ ^ 2 / 2 - γ * (Q γ - η) / 2 = 1 - (-(γ * η / 2) - γ ^ 2 / 4) by
      rw [hQ]; field_simp; ring,
    show 2 * (Q γ - (Q γ - η)) / γ = 2 * η / γ by ring]
  have hA0 : -(γ * η / 2) - γ ^ 2 / 4 ≠ 0 := by
    have : 0 < γ * η / 2 + γ ^ 2 / 4 := by positivity
    linarith
  have hG0 : Real.Gamma (-(γ * η / 2) - γ ^ 2 / 4) ≠ 0 :=
    Real.Gamma_ne_zero (real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith)
      (by push_cast; linarith))
  have hG1 : Real.Gamma (1 - (-(γ * η / 2) - γ ^ 2 / 4)) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hLB : lR (-(γ * η)) ≠ 0 := lR_ne_zero_of_mem_neg (by linarith) (by linarith)
  have hLC : lR (1 - γ * η / 2) ≠ 0 := lR_ne_zero_of_mem_unit (by linarith) (by linarith)
  have hLm : lR (-(γ ^ 2) / 4) ≠ 0 := lR_ne_zero_of_mem_neg (by linarith) (by linarith)
  rw [Real.Gamma_add_one hA0,
    show lR (1 - (-(γ * η / 2) - γ ^ 2 / 4)) = Real.Gamma (1 - (-(γ * η / 2) - γ ^ 2 / 4)) /
      Real.Gamma (-(γ * η / 2) - γ ^ 2 / 4) by unfold lR; rw [sub_sub_cancel]]
  generalize Real.Gamma (-(γ * η / 2) - γ ^ 2 / 4) = G0 at hG0 ⊢
  generalize Real.Gamma (1 - (-(γ * η / 2) - γ ^ 2 / 4)) = G1 at hG1 ⊢
  generalize lR (-(γ * η)) = LB at hLB ⊢
  generalize lR (1 - γ * η / 2) = LC at hLC ⊢
  generalize lR (-(γ ^ 2) / 4) = Lm at hLm ⊢
  have hηγ2 : η + γ / 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The unit-volume γ/2 shift on the two-pole slice**: `R̄(Q - η - γ/2) = m(Q - η) R̄(Q - η)` for
every admissible window, from the γ/2 crossing (`gammaHalf_crossing`), the residue bridge, the
holomorphic extension `unitVolumeStructureConstant_holomorphic_near_extended_domain` and the tail
estimate `twoInsertion_tail_sum_uniform` (through the two-pole expansion). -/
theorem reflectionBarR_shift_of_window {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hCross : ∀ μ α' ε α : ℝ, 0 < μ → γ / 2 < ε → ε < 2 / γ → α < Q γ → α' < Q γ →
      2 * Q γ < α + α' + ε - γ / 2 →
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α)
    (hBridge : ∀ α2 α3 : ℝ, 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ →
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
        Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
            (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
          (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
            reflectionBarR P γ α3 (B α3) Z)))
    (hTail : ∀ (K2 K3 : Set ℂ) (_ : IsCompact K2) (_ : IsCompact K3)
      (_ : ∀ z ∈ K2, 2 ≤ ‖z‖) (_ : ∀ z ∈ K3, 2 ≤ ‖z‖)
      (_ : ∀ z2 ∈ K2, ∀ z3 ∈ K3, 3 ≤ ‖z2 - z3‖)
      (A2 A3 : Set ℝ) (_ : IsCompact A2) (_ : IsCompact A3)
      (_ : ∀ α ∈ A2, γ / 2 < α ∧ α < Q γ)
      (_ : ∀ α ∈ A3, γ / 2 < α ∧ α < Q γ)
      (F2s F3s : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
      (_ : UniformPositiveC1Family K2 F2s radius supBound derivBound lowerBound)
      (_ : UniformPositiveC1Family K3 F3s radius supBound derivBound lowerBound),
      ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, (α ∈ A2 ∨ α ∈ A3) → IsReflectionData P γ α (B α) Z) ∧
          ∀ θ : ℝ, 0 < θ → ∃ C : ℝ, 0 ≤ C ∧
            ∀ z2 ∈ K2, ∀ z3 ∈ K3, ∀ α2 ∈ A2, ∀ α3 ∈ A3,
              ∀ F2 ∈ F2s z2, ∀ F3 ∈ F3s z3, ∀ x : ℝ, 1 ≤ x →
                |(P {ω | ENNReal.ofReal x <
                    localSingularMass M F2 z2 γ α2 ω + localSingularMass M F3 z3 γ α3 ω}).toReal -
                  (oneInsertionTailCoefficient γ α2 z2 (F2 z2) (reflectionBarR P γ α2 (B α2) Z) *
                      Real.rpow x (-reflectionExponent γ α2) +
                    oneInsertionTailCoefficient γ α3 z3 (F3 z3) (reflectionBarR P γ α3 (B α3) Z) *
                      Real.rpow x (-reflectionExponent γ α3))| ≤
                  C * Real.rpow x (-(twoInsertionTailCeiling γ α2 α3 - θ)))
    {V₃ : Set (Fin 3 → ℂ)} (hV₃ : IsOpen V₃)
    (hV₃mem : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      complexifyNCharges α ∈ V₃)
    {f₃ : (Fin 3 → ℂ) → ℂ} (hf₃ : DifferentiableOn ℂ f₃ V₃)
    (hf₃eq : ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
      f₃ (complexifyNCharges α) = (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ))
    {η δ : ℝ} (hW : TwoPoleWindow γ η δ)
    (B₁ : Ω → BrownianPath × BrownianPath) (Z₁ : Ω → Measure ℝ)
    (h₁ : IsReflectionData P γ (Q γ - η - γ / 2) B₁ Z₁)
    (B₂ : Ω → BrownianPath × BrownianPath) (Z₂ : Ω → Measure ℝ)
    (h₂ : IsReflectionData P γ (Q γ - η) B₂ Z₂) :
    reflectionBarR P γ (Q γ - η - γ / 2) B₁ Z₁ =
      rbarShiftMultiplierReal γ (Q γ - η) * reflectionBarR P γ (Q γ - η) B₂ Z₂ := by
  obtain ⟨hη, hη1, hδ, hδ1, hδ2, -⟩ := id hW
  have hηγ : η < 2 / γ - γ / 2 := lt_of_lt_of_le hη1 (min_le_left _ _)
  have hη4 : η < γ / 4 := lt_of_lt_of_le hη1 ((min_le_right _ _).trans (min_le_left _ _))
  have hη2γ : η < 1 / (2 * γ) := lt_of_lt_of_le hη1 ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨B₄, Z₄, -, -, hRD₄, V, hV, hVx, F, r, -, hr, hFx, hFexp⟩ :=
    structureConstant_two_pole_expansion_of_tail P X M γ η δ hγ hγ2 hX hM hW hTail
  have hres := secondResidue_eq_of_bridge P X M hγ hγ2 hX hM hCross hBridge hV₃ hV₃mem hf₃
    hf₃eq hη hη4 hηγ hη2γ hδ hδ1 hδ2 hV hVx hr hFx hFexp B₂ Z₂ h₂
  have hres' : twoPoleSecondResidue P γ B₄ Z₄ η = 4 * η / γ *
      crossingMultiplier3Real γ (Q γ - η) (-(2 * η)) (2 / γ + η) *
        reflectionBarR P γ (Q γ - η) B₂ Z₂ := by exact_mod_cast hres
  unfold twoPoleSecondResidue at hres'
  rw [reflectionBarR_eq_of_isReflectionData P P γ (Q γ - η - γ / 2) (B₄ (Q γ - η - γ / 2)) Z₄
    B₁ Z₁ hRD₄ h₁, show Q γ - (Q γ - η) + γ / 2 = η + γ / 2 by ring] at hres'
  rw [← slice_multiplier_eq hγ hγ2 hη hηγ hη4]
  have hne : (4 / γ * (η + γ / 2)) ≠ 0 := by positivity
  apply mul_left_cancel₀ hne
  rw [hres']
  have hηγ2 : η + γ / 2 ≠ 0 := by positivity
  field_simp

end DOZZ.Proofs

end
