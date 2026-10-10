/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.UnitVolumeStructureConstantHolomorphicNearExtendedDomain
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! The physical first-strip slice has a holomorphic structure-constant germ. This is the
holomorphic extension of the unit-volume structure constant
(`DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`) with the positive zero
mode restored. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- Every physical charge on the first-strip slice has positive zero mode and extended Seiberg
bounds. The positivity is needed for the Gamma factor when restoring the zero mode. -/
theorem firstStrip_extended (γ η a α₂ α₃ : ℝ) (hγ : 0 < γ)
    (h₂ : Q γ - η < α₂ ∧ α₂ < Q γ) (h₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (ha : 2 * η < a ∧ a < Q γ) :
    0 < sExp γ a α₂ α₃ ∧ ExtendedSeiberg3 γ a α₂ α₃ := by
  have hs : 0 < sExp γ a α₂ α₃ := div_pos (by linarith [h₂.1, h₃.1, ha.1]) hγ
  refine ⟨hs, ha.2, h₂.2, h₃.2, ?_⟩
  have hbulk : 0 < 4 / γ ^ 2 := by positivity
  have h1 : 0 < 2 / γ * (Q γ - a) := mul_pos (by positivity) (sub_pos.mpr ha.2)
  have h2 : 0 < 2 / γ * (Q γ - α₂) := mul_pos (by positivity) (sub_pos.mpr h₂.2)
  have h3 : 0 < 2 / γ * (Q γ - α₃) := mul_pos (by positivity) (sub_pos.mpr h₃.2)
  exact (neg_lt_zero.mpr hs).trans (lt_min hbulk (lt_min h1 (lt_min h2 h3)))

/-- The unreflected fusion seed interval is nonempty on the entire first-strip regime. -/
theorem firstStrip_fusion_interval (γ η α₂ α₃ : ℝ)
    (hη : 0 < η ∧ γ < Q γ - 2 * η)
    (h₂ : Q γ - η < α₂) (h₃ : Q γ - η < α₃) :
    γ / 2 + 2 * η < 2 / γ ∧
      ∀ a : ℝ, γ / 2 + 2 * η < a → 2 * Q γ + γ / 2 < a + α₂ + α₃ := by
  constructor
  · unfold Q at hη
    linarith [hη.2]
  · intro a ha
    linarith

/-- Restoring the zero mode gives a holomorphic germ for the physical structure constant on
an open neighborhood of the entire interval `(2η,Q)`, on the supplied space. -/
theorem firstStrip_holomorphic_physical
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (h₂ : Q γ - η < α₂ ∧ α₂ < Q γ) (h₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ V : Set ℂ, IsOpen V ∧ (∀ a : ℝ, 2 * η < a → a < Q γ → (a : ℂ) ∈ V) ∧
      ∃ F : ℂ → ℂ, DifferentiableOn ℂ F V ∧
        ∀ a : ℝ, 2 * η < a → a < Q γ →
          F (a : ℂ) = (structureConstant P M γ μ a α₂ α₃ : ℂ) := by
  obtain ⟨W, hW, hWreal, f, hf, hfreal⟩ :=
    DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  let T : ℂ → Fin 3 → ℂ := fun z => ![z, (α₂ : ℂ), (α₃ : ℂ)]
  let s : ℂ → ℂ := fun z => (z + α₂ + α₃ - 2 * Q γ) / γ
  let V : Set ℂ := T ⁻¹' W ∩ {z | 0 < (s z).re}
  have hT : Differentiable ℂ T := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i
    · exact differentiable_id
    · exact differentiable_const _
    · exact differentiable_const _
  have hs : Differentiable ℂ s := by dsimp [s]; fun_prop
  have hV : IsOpen V := (hW.preimage hT.continuous).inter
    (isOpen_lt continuous_const (Complex.continuous_re.comp hs.continuous))
  have hsreal (a : ℝ) : s (a : ℂ) = (sExp γ a α₂ α₃ : ℂ) := by
    simp only [s, sExp, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_add,
      Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hTreal (a : ℝ) : T (a : ℂ) = complexifyNCharges (![a, α₂, α₃] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> rfl
  have hmem (a : ℝ) (ha : 2 * η < a) (haQ : a < Q γ) : (a : ℂ) ∈ V := by
    obtain ⟨hsp, hext⟩ := firstStrip_extended γ η a α₂ α₃ hγ h₂ h₃ ⟨ha, haQ⟩
    refine ⟨?_, ?_⟩
    · change T (a : ℂ) ∈ W
      rw [hTreal]
      exact hWreal ![a, α₂, α₃] hext
    · change 0 < (s (a : ℂ)).re
      rw [hsreal, Complex.ofReal_re]
      exact hsp
  let F : ℂ → ℂ := fun z => Complex.exp (-s z * (Real.log μ : ℂ)) * Complex.Gamma (s z) * f (T z)
  refine ⟨V, hV, hmem, F, ?_, ?_⟩
  · intro z hz
    have hG : DifferentiableAt ℂ Complex.Gamma (s z) := by
      apply Complex.differentiableAt_Gamma
      intro n hn
      have hpos : 0 < (s z).re := hz.2
      rw [hn] at hpos
      simp only [Complex.neg_re, Complex.natCast_re] at hpos
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hfc := (hf.differentiableAt (hW.mem_nhds hz.1)).comp z hT.differentiableAt
    exact ((((hs.differentiableAt.neg.mul_const _).cexp).mul
      (hG.comp z hs.differentiableAt)).mul hfc).differentiableWithinAt
  · intro a ha haQ
    obtain ⟨-, hext⟩ := firstStrip_extended γ η a α₂ α₃ hγ h₂ h₃ ⟨ha, haQ⟩
    dsimp only [F]
    rw [hsreal, hTreal, hfreal ![a, α₂, α₃] hext, Complex.Gamma_ofReal]
    change Complex.exp (-(sExp γ a α₂ α₃ : ℂ) * (Real.log μ : ℂ)) *
      (Real.Gamma (sExp γ a α₂ α₃) : ℂ) * (unitVolumeStructureConstant P M γ a α₂ α₃ : ℂ) = _
    rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      mul_comm (-sExp γ a α₂ α₃) (Real.log μ), ← Real.rpow_def_of_pos hμ]
    unfold structureConstant unitVolumeStructureConstant
    push_cast
    ring

end DOZZ.Proofs
