/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ParameterDomain
public import DOZZ.Correlations.Analytic.NormalizedVertexHolomorphy

/-! The all-finite insertion frame is the zero infinity-charge slice of the mixed frame. -/

@[expose] public section
namespace DOZZ.Proofs

/-- Append the zero infinity charge to a complex finite-charge vector. -/
def appendZeroCharges {N : ℕ} (β : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.snoc β 0

/-- Appending the zero infinity charge is a holomorphic linear operation. -/
theorem append_zero_differentiable {N : ℕ} :
    Differentiable ℂ (appendZeroCharges (N := N)) := by
  apply differentiable_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [appendZeroCharges, Fin.snoc_last]
    exact differentiable_const _
  · simp only [appendZeroCharges, Fin.snoc_castSucc]
    exact differentiable_apply _

/-- The exact all-finite extended domain satisfies every mixed-frame moment inequality after
appending a zero infinity charge. -/
theorem append_zero_extended_domain {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (α : Fin N → ℝ) (ha : ExtendedSeibergN γ α) :
    (∀ i, (Fin.snoc α (0 : ℝ) : Fin (N + 1) → ℝ) i < Q γ) ∧
      (2 * Q γ - ∑ i, (Fin.snoc α (0 : ℝ) : Fin (N + 1) → ℝ) i) / γ < 4 / γ ^ 2 ∧
      ∀ i, (2 * Q γ - ∑ j, (Fin.snoc α (0 : ℝ) : Fin (N + 1) → ℝ) j) / γ < 2 / γ * (Q γ - (Fin.snoc α (0 : ℝ) : Fin (N + 1) → ℝ) i) := by
  have hfull := finite_frame_admissible γ hγ α ha
  have hsum : (∑ i, (Fin.snoc α (0 : ℝ) : Fin (N + 1) → ℝ) i) = (∑ i, α i) + 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hfull.2.1
    · simpa only [Fin.snoc_castSucc] using hfull.1 j
  · simpa only [hsum] using hfull.2.2.1
  · intro i
    rw [hsum]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last] using hfull.2.2.2.2
    · simpa only [Fin.snoc_castSucc] using hfull.2.2.2.1 j

end DOZZ.Proofs
