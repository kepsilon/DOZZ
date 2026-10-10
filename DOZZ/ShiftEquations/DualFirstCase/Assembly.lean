/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.ShiftEquations.DualFirstCase.Geometry
public import DOZZ.ShiftEquations.DualFirstCase.CoefficientIdentity
public import DOZZ.ShiftEquations.DualFirstCase.Continuation
public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.Brownian.Reflection.RtheorIdentification
import DOZZ.DOZZAlgebra.ReflectionShifts
/-! # The first-case dual structure shift, independent of the DOZZ roots

The four explicit external inputs are the two dual crossing seeds (`DOZZ.dual_crossing_seed_one`,
`DOZZ.dual_crossing_seed_two`), the common reflected/glued representative of
`DOZZ.structureConstant_reflected_shift_and_gluing`, and the identification of the reflection
coefficient off its Gamma poles. Their complete statements are reproduced as conditional inputs.
-/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
universe u
namespace DOZZ.Proofs
theorem structureConstant_dual_shift_strip_first_case_joint
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hsmall : η ≤ γ / 4)
    (hseedOne : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        structureConstant P M γ μ (α - 2 / γ) ε α' =
          dualCrossingMultiplier γ α' α ε *
            reflectionR P γ μ ε Bε Z *
              structureConstant P M γ μ α (2 * Q γ - ε - 2 / γ) α')
    (hseedTwo : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (hG8 : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hμ : 0 < μ)
    (_hη : 0 < η ∧ Q γ - 2 * η > γ)
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (_hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (_hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ),
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
                    C (z - γ / 2)))
    (hOff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hμ : 0 < μ)
    (_hα : γ / 2 < α ∧ α < Q γ) (_hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (_hData : IsReflectionData P γ α B Z),
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, R z = reflectionDOZZ γ μ z) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              (∀ᶠ z in codiscrete ℂ,
                C (z + 2 / γ) =
                  -(1 / (Real.pi * dualMu γ μ)) *
                    shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
                      C (z - 2 / γ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                C (z + γ / 2) =
                  -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) *
                    C (z - γ / 2) := by
  obtain ⟨e, he, heη, hesmall, hewindow, he₂, he₃⟩ :=
    dualFirstCase_shrink γ η α₂ α₃ hη hsmall hα₂ hα₃
  obtain ⟨B, Z, hZ, hB, H, hH, F, R, hF, hR, hFreal, hRreal, hglue, _hreflected⟩ :=
    hG8 P X M γ μ e hγ hγ2 hμ ⟨he, hewindow⟩ hX hM α₂ α₃ he₂ he₃
  have hχ : 0 < 2 / γ := div_pos (by norm_num) hγ
  have hχb : γ / 2 < 2 / γ := by
    apply (div_lt_div_iff₀ (by norm_num) hγ).mpr
    nlinarith only [hγ, hγ2]
  have hq : Q γ = 2 / γ + γ / 2 := rfl
  have hRD : R =ᶠ[codiscreteWithin (horizontalStrip H)] reflectionDOZZ γ μ := by
    apply dualFirstCase_continue_interval hH (lo := max (γ / 2) (2 / γ)) (hi := Q γ)
    · apply max_lt <;> rw [hq] <;> linarith only [hγ, hχ]
    · exact hR
    · exact (meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set (subset_univ _)
    · intro x hx hxQ
      have hxb : γ / 2 < x := lt_of_le_of_lt (le_max_left _ _) hx
      have hxc : Q γ - γ / 2 < x := by rw [hq]; linarith only [lt_of_le_of_lt (le_max_right _ _) hx]
      rw [hRreal x hxb hxQ]
      exact hOff P γ μ x hγ hγ2 hμ ⟨hxb, hxQ⟩ (dualFirstCase_poleFree hγ hxc) (B x) Z (hB x hxb hxQ)
  obtain ⟨lo, hloQ, hwindow⟩ := dualFirstCase_seed_interval γ e α₂ α₃ hγ hesmall he₂.1 he₃.1
  let a := max lo (2 / γ)
  have haQ : a < Q γ := max_lt hloQ (by rw [hq]; linarith only [hγ])
  have ha₂ : Q γ - γ / 2 < α₂ := by linarith only [he₂.1, hesmall, hγ]
  have ha₂b : γ / 2 < α₂ := by
    rw [hq] at he₂
    linarith only [he₂.1, hχb, hesmall, hγ]
  have hseed : (fun z : ℂ => F (z + ((-(2 / γ) : ℝ) : ℂ))) =ᶠ[codiscreteWithin (horizontalStrip H)]
      (fun z => dualFirstCase_crossingProduct γ α₂ α₃ z * reflectionDOZZ γ μ z *
        F (((2 * Q γ - 2 / γ : ℝ) : ℂ) - z)) := by
    apply dualFirstCase_continue_interval hH haQ (dualFirstCase_meromorphic_translate hF (-(2 / γ)))
    · exact (((dualFirstCase_crossingProduct_meromorphic γ α₂ α₃).mono_set (subset_univ _)).mul
        ((meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set (subset_univ _))).mul
          (dualFirstCase_meromorphic_reflect hF (2 * Q γ - 2 / γ))
    · intro x hx hxQ
      have hxlo : lo < x := lt_of_le_of_lt (le_max_left _ _) hx
      obtain ⟨hs, hminus, href⟩ := hwindow x hxlo hxQ
      have hxc : Q γ - γ / 2 < x := by
        rw [hq]; linarith only [lt_of_le_of_lt (le_max_right _ _) hx]
      have hxb : γ / 2 < x := by linarith only [hminus.1, he, hχb]
      obtain ⟨B₁, Z₁, _hZ₁, hB₁, hc₁⟩ :=
        hseedOne P M X γ μ x α₂ α₃ hγ hγ2 hμ hxQ he₂.2 he₃.2 hs hX hM
      obtain ⟨B₂, Bx, Z₂, _hZ₂, hB₂, hBx, hc₂⟩ :=
        hseedTwo P M X γ μ x α₂ α₃ hγ hγ2 hμ hxQ he₂.2 he₃.2 hs hX hM
      have hc₁c := congrArg (fun r : ℝ => (r : ℂ)) hc₁
      have hc₂c := congrArg (fun r : ℝ => (r : ℂ)) hc₂
      push_cast at hc₁c hc₂c
      rw [hOff P γ μ α₂ hγ hγ2 hμ ⟨ha₂b, he₂.2⟩ (dualFirstCase_poleFree hγ ha₂) B₁ Z₁ hB₁] at hc₁c
      rw [hOff P γ μ α₂ hγ hγ2 hμ ⟨ha₂b, he₂.2⟩ (dualFirstCase_poleFree hγ ha₂) B₂ Z₂ hB₂,
        hOff P γ μ x hγ hγ2 hμ ⟨hxb, hxQ⟩ (dualFirstCase_poleFree hγ hxc) Bx Z₂ hBx,
        dualFirstCase_structure_swap12 P X M γ μ (2 * Q γ - α₂ - 2 / γ) x α₃ hγ hγ2 hX hM,
        dualFirstCase_structure_swap12 P X M γ μ α₂ (2 * Q γ - x - 2 / γ) α₃ hγ hγ2 hX hM] at hc₂c
      rw [show (x : ℂ) + ((-(2 / γ) : ℝ) : ℂ) = ((x - 2 / γ : ℝ) : ℂ) by push_cast; ring,
        show ((2 * Q γ - 2 / γ : ℝ) : ℂ) - (x : ℂ) = ((2 * Q γ - x - 2 / γ : ℝ) : ℂ) by push_cast; ring,
        hFreal (x - 2 / γ) hminus.1 hminus.2,
        hFreal (2 * Q γ - x - 2 / γ) href.1 href.2,
        dualFirstCase_crossingProduct_ofReal γ x α₂ α₃ hγ.ne']
      calc
        (structureConstant P M γ μ (x - 2 / γ) α₂ α₃ : ℂ) = _ := hc₁c
        _ = (dualCrossingMultiplier γ α₃ x α₂ : ℂ) *
          (reflectionDOZZ γ μ α₂ * (structureConstant P M γ μ x (2 * Q γ - α₂ - 2 / γ) α₃ : ℂ)) := by ring
        _ = _ := by rw [hc₂c]; push_cast; ring
  have hk : ∀ n : ℤ, 4 / γ ^ 2 ≠ n := four_div_sq_ne_int_of_irrational hγirr
  have hK : (Real.pi : ℂ) * dualMu γ μ ≠ 0 := by
    have heq : (Real.pi : ℂ) * dualMu γ μ = reflectionDOZZDualConst γ μ := by
      unfold dualMu reflectionDOZZDualConst
      field_simp
    rw [heq]
    exact reflectionDOZZDualConst_ne_zero hγ hγ2 hμ hk
  have hcoeff := dualFirstCase_coefficient_product_codiscrete γ (α₂ : ℂ) (α₃ : ℂ) hγ.ne'
    (dualFirstCase_fixed_factor_ne_zero hγ ha₂ he₂.2)
  have hden := reflectionDualShiftDenom_ne_zero hγ hk
  have hshiftR := reflectionDOZZ_shift_binv hγ hγ2 (fun n => by exact_mod_cast hk n) hμ
  have hglueW : ∀ᶠ z in codiscreteWithin (horizontalStrip H), F z = R z * F (2 * Q γ - z) :=
    hglue.filter_mono (codiscreteWithin_le_codiscrete_inf_principal _ |>.trans inf_le_left)
  have hplus := dualFirstCase_codiscreteWithin_translate hglueW (2 / γ)
  have hRDplus := dualFirstCase_codiscreteWithin_translate hRD (2 / γ)
  have hshiftF : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      F (z + (2 / γ : ℝ)) =
        (-(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z α₂ α₃) * F (z - (2 / γ : ℝ)) := by
    have hfilter : codiscreteWithin (horizontalStrip H) ≤ codiscrete ℂ :=
      codiscreteWithin_le_codiscrete_inf_principal _ |>.trans inf_le_left
    filter_upwards [hseed, hplus, hRDplus, hcoeff.filter_mono hfilter,
      hden.filter_mono hfilter, hshiftR.filter_mono hfilter] with z hs hg hrd hc hd hr
    rw [hr] at hs
    rw [hrd] at hg
    have hreflect : ((2 * Q γ - 2 / γ : ℝ) : ℂ) - z = 2 * Q γ - (z + (2 / γ : ℝ)) := by push_cast; ring
    rw [hreflect] at hs
    have hconst : (((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) /
      lFun ((4 / γ ^ 2 : ℝ) : ℂ)) = (Real.pi : ℂ) * dualMu γ μ := by
      unfold dualMu
      field_simp
    rw [hconst] at hs
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat] at hs hg ⊢
    rw [← sub_eq_add_neg] at hs
    change dualFirstCase_crossingProduct γ α₂ α₃ z * shiftCoeffA γ (2 / γ) z α₂ α₃ = reflectionDualShiftDenom γ z at hc
    exact dualFirstCase_scalar_shift
      (dualFirstCase_crossingProduct γ α₂ α₃ z) (shiftCoeffA γ (2 / γ) z α₂ α₃)
      ((Real.pi : ℂ) * dualMu γ μ) (reflectionDualShiftDenom γ z)
      (reflectionDOZZ γ μ (z + 2 / γ)) (F (2 * Q γ - (z + 2 / γ)))
      (F (z - 2 / γ)) (F (z + 2 / γ)) hd hK hc
      (by simpa only [reflectionDualShiftDenom, Complex.ofReal_div, Complex.ofReal_ofNat] using hs) hg
  have hfirstF : ∀ᶠ z in codiscrete ℂ,
      F (z + γ / 2) = -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃ * F (z - γ / 2) := by
    filter_upwards [eventually_codiscrete_comp_add hglue ((γ / 2 : ℝ) : ℂ), _hreflected] with z hg hr
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hg
    rw [hg, show 2 * (Q γ : ℂ) - (z + γ / 2) = 2 * Q γ - z - γ / 2 by ring]
    exact hr
  obtain ⟨C, S, hC, hS, hCF, hCzero, hSR, hSD, hCg, hCs⟩ :=
    dualFirstCase_common_representative F R (reflectionDOZZ γ μ)
      (fun z => -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z α₂ α₃)
      H (2 / γ) (2 * Q γ) hH hF hR hRD
      (by simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hglueW) hshiftF
  refine ⟨B, Z, hZ, hB, H / 2, half_pos hH, C, S, hC, hS, ?_, ?_, hSD, ?_, ?_, ?_⟩
  · intro x hx hxQ
    have hxstrip : (x : ℂ) ∈ horizontalStrip (H / 2) := by
      simpa only [horizontalStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using half_pos hH
    rw [hCF hxstrip]
    exact hFreal x (by linarith only [heη, hx]) hxQ
  · intro x hx hxQ
    have hxstrip : (x : ℂ) ∈ horizontalStrip (H / 2) := by
      simpa only [horizontalStrip, mem_ofPred_eq, Complex.ofReal_im, abs_zero] using half_pos hH
    rw [hSR hxstrip]
    exact hRreal x hx hxQ
  · simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hCg
  · simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hCs
  · have hfirstF' : ∀ᶠ z in codiscrete ℂ,
        F (z + ((γ / 2 : ℝ) : ℂ)) =
          (-(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃) * F (z - ((γ / 2 : ℝ) : ℂ)) := by
      simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hfirstF
    have ht := dualFirstCase_transfer_global_shift F C
      (fun z => -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z α₂ α₃)
      (H / 2) (γ / 2) hCF hCzero hfirstF'
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using ht

/-- The dual structure shift on the first-case box, with the full physical and common-reflection
clauses. Only the four inputs displayed below remain conditional. -/
theorem structureConstant_dual_shift_strip_first_case
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hsmall : η ≤ γ / 4)
    (hseedOne : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        structureConstant P M γ μ (α - 2 / γ) ε α' =
          dualCrossingMultiplier γ α' α ε *
            reflectionR P γ μ ε Bε Z *
              structureConstant P M γ μ α (2 * Q γ - ε - 2 / γ) α')
    (hseedTwo : ∀ {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (_hγ : 0 < γ) (_hγ₂ : γ < 2) (_hμ : 0 < μ)
    (_hα : α < Q γ) (_hε : ε < Q γ) (_hα' : α' < Q γ)
    (_hs : 2 * Q γ + 2 / γ < α + ε + α')
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M),
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α')
    (hG8 : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ)
    (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hμ : 0 < μ)
    (_hη : 0 < η ∧ Q γ - 2 * η > γ)
    (_hX : IsEquatorGFF P X) (_hM : IsGMCOf P X γ M)
    (α₂ α₃ : ℝ)
    (_hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ)
    (_hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ),
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
                    C (z - γ / 2)))
    (hOff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (_hγ : 0 < γ) (_hγ2 : γ < 2) (_hμ : 0 < μ)
    (_hα : γ / 2 < α ∧ α < Q γ) (_hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (_hData : IsReflectionData P γ α B Z),
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ)) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ C R : ℂ → ℂ,
              MeromorphicOn C {z | |z.im| < h} ∧
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, 2 * η < α → α < Q γ →
                C (α : ℂ) = (structureConstant P M γ μ α α₂ α₃ : ℂ)) ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              (∀ᶠ z in codiscrete ℂ, R z = reflectionDOZZ γ μ z) ∧
              (∀ᶠ z in codiscrete ℂ,
                C z = R z * C (2 * Q γ - z)) ∧
              ∀ᶠ z in codiscrete ℂ,
                C (z + 2 / γ) =
                  -(1 / (Real.pi * dualMu γ μ)) *
                    shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) *
                      C (z - 2 / γ) := by
  obtain ⟨B, Z, hZ, hB, h, hh, C, R, hC, hR, hCp, hRp, hRD, hg, hs, _hfirst⟩ :=
    structureConstant_dual_shift_strip_first_case_joint P X M γ μ η hγ hγ2 hγirr hμ hη hX hM
      α₂ α₃ hα₂ hα₃ hsmall hseedOne hseedTwo hG8 hOff
  exact ⟨B, Z, hZ, hB, h, hh, C, R, hC, hR, hCp, hRp, hRD, hg, hs⟩
end DOZZ.Proofs
