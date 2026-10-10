/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesDerivativeBounds
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Topology of the nonresonant parameter domain for Gauss connection coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

private def gaussIntegerRange : Set ℂ := Set.range fun n : ℤ => (n : ℂ)

/-- Parameter triples for which both local exponents in the connection problem are
nonresonant. -/
def gaussConnectionParameterDomain : Set (ℂ × ℂ × ℂ) :=
  {p | (∀ n : ℤ, p.2.2 ≠ (n : ℂ)) ∧
    ∀ n : ℤ, p.2.2 - p.1 - p.2.1 ≠ (n : ℂ)}

private def gaussConnectionParameterEquiv :
    (ℂ × ℂ × ℂ) ≃ (ℂ × ℂ × ℂ) where
  toFun p := (p.2.2, p.2.2 - p.1 - p.2.1, p.1)
  invFun q := (q.2.2, q.1 - q.2.1 - q.2.2, q.1)
  left_inv := by
    rintro ⟨a, b, c⟩
    simp
    ring
  right_inv := by
    rintro ⟨c, δ, a⟩
    simp

/-- The integer lattice is closed in the complex plane. -/
private theorem gaussIntegerRange_isClosed : IsClosed gaussIntegerRange := by
  have hIso : Isometry (fun n : ℤ => (n : ℂ)) := Complex.isometry_intCast
  exact hIso.isClosedEmbedding.isClosed_range

/-- The nonresonant parameter domain is open. -/
theorem gaussConnectionParameterDomain_isOpen :
    IsOpen gaussConnectionParameterDomain := by
  have hc : IsOpen {p : ℂ × ℂ × ℂ | p.2.2 ∉ gaussIntegerRange} := by
    exact gaussIntegerRange_isClosed.isOpen_compl.preimage
      (continuous_snd.comp continuous_snd)
  have hδ : IsOpen {p : ℂ × ℂ × ℂ |
      p.2.2 - p.1 - p.2.1 ∉ gaussIntegerRange} := by
    have hcont : Continuous (fun p : ℂ × ℂ × ℂ => p.2.2 - p.1 - p.2.1) := by
      fun_prop
    exact gaussIntegerRange_isClosed.isOpen_compl.preimage hcont
  have hEq : gaussConnectionParameterDomain =
      {p | p.2.2 ∉ gaussIntegerRange} ∩
        {p | p.2.2 - p.1 - p.2.1 ∉ gaussIntegerRange} := by
    ext p
    simp [gaussConnectionParameterDomain, gaussIntegerRange, eq_comm]
  rw [hEq]
  exact hc.inter hδ


end DOZZ.Proofs
