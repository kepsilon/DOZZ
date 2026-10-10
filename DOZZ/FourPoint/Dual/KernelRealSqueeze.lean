/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.CopiedInnerPolar
public import DOZZ.FourPoint.Dual.RelativeIncrement
import Mathlib.Tactic
/-! The literal extended-valued copied kernel squeeze gives a real signed increment bound. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A finite polar comparison proves finiteness of the squeezed kernel mass and controls
its signed increment without a first moment of either inner mass. -/
theorem dual_ennreal_kernel_increment_error (I V : ℝ≥0∞) (p A β θlo θhi : ℝ)
    (hp : 0 < p) (hA : 0 < A) (hβ : 0 ≤ β) (hlo : 0 ≤ θlo) (hhi : 0 ≤ θhi)
    (hV : V ≠ ⊤) (hs : ENNReal.ofReal (θlo*β)*V ≤ I ∧
      I ≤ ENNReal.ofReal (θhi*β)*V) :
    I ≠ ⊤ ∧
    |((A+I.toReal)^(-p)-A^(-p))-((A+β*V.toReal)^(-p)-A^(-p))| ≤
      max |θlo-1| |θhi-1| * (A^(-p)-(A+β*V.toReal)^(-p)) := by
  have hI : I ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hs.2
  have hl : θlo*(β*V.toReal) ≤ I.toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hlo hβ), mul_assoc] using
      ENNReal.toReal_mono hI hs.1
  have hh : I.toReal ≤ θhi*(β*V.toReal) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hhi hβ), mul_assoc] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hV) hs.2
  exact ⟨hI, dual_negative_increment_kernel_squeeze p A (β*V.toReal) I.toReal θlo θhi
    hp hA (mul_nonneg hβ ENNReal.toReal_nonneg) hlo hhi hl hh⟩

end DOZZ.Proofs
