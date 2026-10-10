/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
public import DOZZ.ShiftEquations.Inversion.Gluing
import DOZZ.ShiftEquations.Inversion.Nonzero

/-! The inversion `DOZZ.reflectionR_inversion_meromorphic` from the literal conclusion of
`DOZZ.structureConstant_reflected_shift_and_gluing`. Double gluing gives inversion in the
meromorphic strip; the representative construction with exterior value one
(`exists_physical_inversion_representative`) gives the whole-plane representative with every
supplied-space physical value. -/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- The conclusion of `DOZZ.structureConstant_reflected_shift_and_gluing` alone implies
`DOZZ.reflectionR_inversion_meromorphic`: its gluing equation and physical three-point values supply
a nonzero germ, while its reflection germ supplies the physical values on the given probability
space. No dual crossing is assumed. -/
theorem reflectionR_inversion_meromorphic_of_reflected_shift_and_gluing
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hShiftGluing : ∀ η : ℝ, 0 < η ∧ Q γ - 2 * η > γ →
      ∀ α₂ α₃ : ℝ, Q γ - η < α₂ ∧ α₂ < Q γ →
        Q γ - η < α₃ ∧ α₃ < Q γ →
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
                    C (z - γ / 2))) :
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
              ∀ᶠ z in codiscrete ℂ, R z * R (2 * Q γ - z) = 1 := by
  have hhalf : γ / 2 < 2 / γ := (lt_div_iff₀ hγ).mpr (by nlinarith)
  have hγQ : γ < Q γ := by unfold Q; linarith
  obtain ⟨η, hηpos, hηlt⟩ := exists_between
    (div_pos (sub_pos.mpr hγQ) (show (0 : ℝ) < 4 by norm_num))
  have hη : 0 < η ∧ Q γ - 2 * η > γ := ⟨hηpos, by linarith⟩
  let a : ℝ := Q γ - η / 2
  have ha : Q γ - η < a ∧ a < Q γ := by dsimp [a]; constructor <;> linarith
  obtain ⟨B, Z, hSLP, hRD, H, hH, C, F, hC, hF, hCr, hFr, hglue, -⟩ :=
    hShiftGluing η hη a a ha ha
  have hCne : ∀ y : ℝ, 2 * η < y → y < Q γ → C (y : ℂ) ≠ 0 := by
    intro y hylo hyhi
    rw [hCr y hylo hyhi, Complex.ofReal_ne_zero]
    apply (structureConstant_pos P X M γ μ y a a hγ hγ2 hμ hX hM
      hyhi ha.2 ha.2 ?_).ne'
    unfold sExp
    apply div_pos _ hγ
    dsimp [a]
    linarith
  have hglue' : ∀ᶠ z in codiscrete ℂ, C z = F z * C (((2 * Q γ : ℝ) : ℂ) - z) := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hglue
  have hinv := inversion_of_gluing C F (2 * Q γ) H (2 * η) (Q γ)
    hH (by linarith [hη.2]) hC hCne hglue'
  have hphysical : ∀ᶠ z in codiscreteWithin (horizontalStrip H),
      z.im = 0 → γ / 2 < z.re → z.re < Q γ →
        F z = (reflectionR P γ μ z.re (B z.re) Z : ℂ) := by
    apply Eventually.of_forall
    intro z hzim hlo hhi
    have hzreal : z = (z.re : ℂ) := by
      apply Complex.ext
      · exact (Complex.ofReal_re _).symm
      · exact hzim.trans (Complex.ofReal_im _).symm
    rw [hzreal]
    exact hFr z.re hlo hhi
  obtain ⟨R, hRm, hRr, hRi⟩ := exists_physical_inversion_representative F
    (fun α => (reflectionR P γ μ α (B α) Z : ℂ)) (2 * Q γ) H (H / 2)
    (γ / 2) (Q γ) (half_pos hH) (half_lt_self hH) hF hinv hphysical
  refine ⟨B, Z, hSLP, hRD, H / 2, half_pos hH, R, hRm, hRr, ?_⟩
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using hRi

end DOZZ.Proofs
