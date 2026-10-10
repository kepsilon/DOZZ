/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Correlations.Residue.FullFromUnit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
/-! # Pole-free normalization of the two DOZZ roots -/
@[expose] public section
open MeasureTheory
namespace DOZZ.Proofs
/-- On the pole-free locus the complex normalization removes the real Gamma factor exactly. -/
theorem roots_unitVolume_normalization {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ a b c : ℝ) (hμ : 0 < μ)
    (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    ((μ : ℂ) ^ (sExp γ a b c : ℂ) / Complex.Gamma (sExp γ a b c)) *
      (structureConstant P M γ μ a b c : ℂ) =
        (unitVolumeStructureConstant P M γ a b c : ℂ) := by
  let s := sExp γ a b c
  have hGamma : Complex.Gamma (s : ℂ) ≠ 0 := Complex.Gamma_ne_zero (fun n hn =>
    hs n (Complex.ofReal_inj.mp (by simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using hn)))
  rw [residue_structureConstant_eq_unitVolume, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.Gamma_ofReal, ← Complex.ofReal_cpow hμ.le]
  have hprod : μ ^ s * μ ^ (-s) = (1 : ℝ) := by
    rw [← Real.rpow_add hμ, add_neg_cancel, Real.rpow_zero]
  have hGammaR : (Real.Gamma (sExp γ a b c) : ℂ) ≠ 0 := by
    simpa only [Complex.Gamma_ofReal] using hGamma
  field_simp [hGammaR]
  have he : ((μ ^ (sExp γ a b c) : ℝ) : ℂ) * ((μ ^ (-sExp γ a b c) : ℝ) : ℂ) = 1 := by
    exact_mod_cast hprod
  rw [he, one_mul]
/-- A normalized value equality determines the full structure constant on the pole-free locus. -/
theorem roots_structureConstant_of_unitVolume_value {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ a b c : ℝ) (hμ : 0 < μ)
    (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) (D : ℂ)
    (hD : (unitVolumeStructureConstant P M γ a b c : ℂ) =
      ((μ : ℂ) ^ (sExp γ a b c : ℂ) / Complex.Gamma (sExp γ a b c)) * D) :
    (structureConstant P M γ μ a b c : ℂ) = D := by
  have hGamma : Complex.Gamma (sExp γ a b c : ℂ) ≠ 0 := Complex.Gamma_ne_zero (fun n hn =>
    hs n (Complex.ofReal_inj.mp (by simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using hn)))
  have hpow : (μ : ℂ) ^ (sExp γ a b c : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hμ.ne'))
  apply mul_left_cancel₀ (div_ne_zero hpow hGamma)
  exact (roots_unitVolume_normalization P M γ μ a b c hμ hs).trans hD
end DOZZ.Proofs
