/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.NPointCoulombPrefactor
public import DOZZ.Complex.Charge

/-! Entire continuation of the finite-position Coulomb prefactor. -/

@[expose] public section
namespace DOZZ.Proofs

/-- Fixed distinct positions give a polynomial-exponential continuation of the Coulomb
prefactor, with no logarithm branch depending on the charges. -/
noncomputable def complexCoulombPrefactor {N : ℕ} (β : Fin N → ℂ) (z : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j, if i < j then Complex.exp (-(β i * β j) * (Real.log ‖z i - z j‖ : ℂ)) else 1

/-- The fixed-position complex Coulomb prefactor is entire in all charges. -/
theorem complex_coulomb_prefactor_differentiable {N : ℕ} (z : Fin N → ℂ) :
    Differentiable ℂ (fun β => complexCoulombPrefactor β z) := by
  classical
  have hpair (i j : Fin N) : Differentiable ℂ (fun β : Fin N → ℂ =>
      if i < j then Complex.exp (-(β i * β j) * (Real.log ‖z i - z j‖ : ℂ)) else 1) := by
    by_cases h : i < j
    · simp only [ite_eq_left h]
      fun_prop
    · simp only [ite_eq_right h]
      exact differentiable_const _
  intro β
  unfold complexCoulombPrefactor
  exact (HasFDerivAt.finsetProd (fun i _ =>
    HasFDerivAt.finsetProd (fun j _ => (hpair i j β).hasFDerivAt))).differentiableAt

/-- The entire prefactor is exactly the real prefactor `DOZZ.nPointCoulombPrefactor` on real
charges. -/
theorem complex_coulomb_prefactor_ofReal {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ)
    (hz : Function.Injective z) :
    complexCoulombPrefactor (fun i => (α i : ℂ)) z = (nPointCoulombPrefactor α z : ℂ) := by
  unfold complexCoulombPrefactor nPointCoulombPrefactor
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  apply Finset.prod_congr rfl
  intro j _
  split_ifs with h
  · have hn : 0 < ‖z i - z j‖ := norm_pos_iff.mpr
      (sub_ne_zero.mpr (fun he => (ne_of_lt h) (hz he)))
    rw [Real.rpow_eq_pow, Real.rpow_def_of_pos hn]
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  · rfl

end DOZZ.Proofs
