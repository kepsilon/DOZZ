/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-! The ordinary Gauss series coefficient recurrence, needed to seed the Gauss system at zero. -/

@[expose] public section

open Polynomial

namespace DOZZ.Proofs

theorem ordinaryHypergeometric_pochhammer_denominator_ne_zero {c : ℂ} (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    Polynomial.eval c (ascPochhammer ℂ n) ≠ 0 := by
  intro h
  obtain ⟨k, hkn, hkc⟩ := (ascPochhammer_eval_eq_zero_iff n c).mp h
  exact hc k (by linear_combination hkc)

/-- Multiplying successive ordinary-series coefficients by their denominator factors gives the
three-term recurrence for the Gauss equation. -/
theorem ordinaryHypergeometricCoefficient_gauss_recurrence (a b c : ℂ) (n : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    ((n + 1 : ℂ) * ((n : ℂ) + c)) * ordinaryHypergeometricCoefficient a b c (n + 1) =
      ((n : ℂ) + a) * ((n : ℂ) + b) * ordinaryHypergeometricCoefficient a b c n := by
  have hcn : c + (n : ℂ) ≠ 0 := by
    intro h
    have h' : c = -(n : ℂ) := by linear_combination h
    exact hc n h'
  have hcpn : Polynomial.eval c (ascPochhammer ℂ n) ≠ 0 :=
    ordinaryHypergeometric_pochhammer_denominator_ne_zero n hc
  have hfact : ((n + 1).factorial : ℂ) = (n + 1 : ℂ) * (n.factorial : ℂ) := by
    exact_mod_cast Nat.factorial_succ n
  have hfact0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [ordinaryHypergeometricCoefficient, ascPochhammer_succ_eval]
  rw [hfact]
  field_simp [hcpn, hcn, hfact0]
  ring

end DOZZ.Proofs
