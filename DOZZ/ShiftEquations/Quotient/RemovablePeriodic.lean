/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Quotient.Divisors
import DOZZ.ShiftEquations.Quotient.StripFactor
import DOZZ.DOZZAlgebra.FormulaShiftB
import DOZZ.DOZZAlgebra.FormulaShiftBinv
import DOZZ.DOZZAlgebra.GenericLocus
import DOZZ.Brownian.Reflection.RtheorAnalytic
import DOZZ.Brownian.Reflection.RtheorIdentification

/-!
# The DOZZ quotient is a removable doubly periodic factor

This is the final quotient argument of [KRV, §11]. A total function `C`, meromorphic on a strip and
obeying the two structure-constant shift laws off a codiscrete subset of the plane, is a constant
multiple of the DOZZ formula on the strip, off a codiscrete subset of the plane. The factor is that
constant on the strip and the total quotient off it; it is differentiable on the strip and has the
periods `γ` and `4/γ` there.

The DOZZ formula obeys the same two shifts (`dozzFormula_shift_b`, `dozzFormula_shift_binv`) and is
meromorphic and nonzero off a codiscrete set; both multipliers are nonzero off a codiscrete set. The
abstract factorization `exists_eventually_eq_const_mul_of_shifts` (dense periods inside the strip,
bounded walks at its boundary) does the rest.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- On the regime of the final quotient argument [KRV, §11] (`γ² ∉ ℚ` and fixed real charges `α₂`,
`α₃` on the near-`Q` slice), the quotient extends holomorphically through all divisor points and has
periods `γ` and `4/γ`. -/
theorem structureConstant_DOZZ_quotient_removable_periodic
    (γ μ η : ℝ) (U : ℂ → ℂ) (α₂ α₃ : ℝ) (h : ℝ) (hh : 0 < h)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ)
    (hα₂ : Q γ - η < α₂ ∧ α₂ < Q γ) (hα₃ : Q γ - η < α₃ ∧ α₃ < Q γ)
    (hU : IsUpsilon γ U)
    (C : ℂ → ℂ) (hC : MeromorphicOn C (horizontalStrip h))
    (hfirst : ∀ᶠ z in codiscrete ℂ,
      C (z + γ / 2) =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ) * C (z - γ / 2))
    (hdual : ∀ᶠ z in codiscrete ℂ,
      C (z + 2 / γ) =
        -(1 / (Real.pi * dualMu γ μ)) *
          shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ) * C (z - 2 / γ)) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (horizontalStrip h) ∧
      (∀ᶠ z in codiscrete ℂ, Ψ z * dozzFormula γ μ U z (α₂ : ℂ) (α₃ : ℂ) = C z) ∧
      ∀ z ∈ horizontalStrip h, Ψ (z + γ) = Ψ z ∧ Ψ (z + 4 / γ) = Ψ z := by
  set b : ℝ := γ / 2 with hbdef
  set b' : ℝ := 2 / γ with hb'def
  have hb : 0 < b := by positivity
  have hb' : 0 < b' := by positivity
  have hγ0 : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hbc : ((b : ℝ) : ℂ) = (γ : ℂ) / 2 := by rw [hbdef]; push_cast; ring
  have hb'c : ((b' : ℝ) : ℂ) = 2 / (γ : ℂ) := by rw [hb'def]; push_cast; ring
  have hirr : Irrational (b / b') := by
    have e : b / b' = γ ^ 2 / (4 : ℕ) := by
      rw [hbdef, hb'def]; push_cast; field_simp; ring
    rw [e]
    exact hγirr.div_natCast (by norm_num)
  have hγk : ∀ n : ℤ, 4 / γ ^ 2 ≠ n := four_div_sq_ne_int_of_irrational hγirr
  have hγk' : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ) := fun k hk => hγk k (by exact_mod_cast hk)
  have hQη : 0 < Q γ - η := by linarith [hη.1, hη.2]
  -- the DOZZ formula and its divisor
  have hU₂ : U (α₂ : ℂ) ≠ 0 := IsUpsilon.ne_zero_of_re hU (by simp; linarith [hα₂.1])
    (by simpa using hα₂.2)
  have hU₃ : U (α₃ : ℂ) ≠ 0 := IsUpsilon.ne_zero_of_re hU (by simp; linarith [hα₃.1])
    (by simpa using hα₃.2)
  have hD := (meromorphicOn_dozzFormula hγ hγ2 hμ hU (α₂ : ℂ) (α₃ : ℂ)).mono_set
    (Set.subset_univ (horizontalStrip h))
  have hD0 := eventually_dozzFormula_ne_zero hγ hγ2 hμ hU hU₂ hU₃
  -- nonzero multipliers
  have hπμ : (-(1 / (Real.pi * μ)) : ℂ) ≠ 0 := by
    have : ((Real.pi : ℂ) * μ) ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast hμ.ne')
    exact neg_ne_zero.mpr (one_div_ne_zero this)
  have hdual0 : (-(1 / (Real.pi * dualMu γ μ)) : ℂ) ≠ 0 := by
    have hl : lFun ((4 / γ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      lFun_ne_zero_of_forall_ne_int fun n hn => hγk n (by exact_mod_cast hn)
    have hbase : ((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (dozzBase_pos hγ hγ2 hμ).ne'))
    have hμ' : dualMu γ μ ≠ 0 := by
      unfold dualMu
      exact div_ne_zero hbase (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hl)
    exact neg_ne_zero.mpr (one_div_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) hμ'))
  have hA₁ := eventually_shiftCoeffA_ne_zero γ (α₂ : ℂ) (α₃ : ℂ)
    (χ := (γ : ℂ) / 2) (div_ne_zero hγ0 two_ne_zero)
    (lFun_ne_zero_of_forall_ne_int fun n hn => by
      have hq : 0 < γ ^ 2 / 4 := by positivity
      have hq1 : γ ^ 2 / 4 < 1 := by nlinarith
      have e : -((γ : ℂ) / 2) ^ 2 = ((-(γ ^ 2 / 4) : ℝ) : ℂ) := by push_cast; ring
      rw [e] at hn
      have hn' : -(γ ^ 2 / 4) = (n : ℝ) := by exact_mod_cast hn
      rcases lt_trichotomy n 0 with hlt | heq | hgt
      · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
        linarith
      · rw [heq, Int.cast_zero] at hn'
        linarith
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hgt
        linarith)
  have hA₂ := eventually_shiftCoeffA_ne_zero γ (α₂ : ℂ) (α₃ : ℂ)
    (χ := 2 / (γ : ℂ)) (div_ne_zero two_ne_zero hγ0)
    (lFun_ne_zero_of_forall_ne_int fun n hn => hγk (-n) (by
      have e : -(2 / (γ : ℂ)) ^ 2 = ((-(4 / γ ^ 2)) : ℝ) := by push_cast; ring
      rw [e] at hn
      have hn' : -(4 / γ ^ 2) = (n : ℝ) := by exact_mod_cast hn
      push_cast
      linarith))
  -- both shift laws for `C` and the DOZZ formula, with nonzero multipliers
  have hgood : ∀ᶠ z in codiscrete ℂ,
      (C (z + b) = (-(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ)) *
          C (z - b) ∧
        dozzFormula γ μ U (z + b) (α₂ : ℂ) (α₃ : ℂ) =
          (-(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ)) *
            dozzFormula γ μ U (z - b) (α₂ : ℂ) (α₃ : ℂ) ∧
        (-(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) z (α₂ : ℂ) (α₃ : ℂ)) ≠ 0) ∧
      (C (z + b') = (-(1 / (Real.pi * dualMu γ μ)) *
          shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ)) * C (z - b') ∧
        dozzFormula γ μ U (z + b') (α₂ : ℂ) (α₃ : ℂ) =
          (-(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ)) *
            dozzFormula γ μ U (z - b') (α₂ : ℂ) (α₃ : ℂ) ∧
        (-(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) z (α₂ : ℂ) (α₃ : ℂ)) ≠ 0) := by
    filter_upwards [hfirst, hdual, dozzFormula_shift_b hγ hγ2 hμ hU (α₂ : ℂ) (α₃ : ℂ),
      dozzFormula_shift_binv hγ hγ2 hγk' hμ hU (α₂ : ℂ) (α₃ : ℂ), hA₁, hA₂]
      with z h1 h2 h3 h4 h5 h6
    rw [hbc, hb'c]
    exact ⟨⟨h1, h3, mul_ne_zero hπμ h5⟩, ⟨h2, h4, mul_ne_zero hdual0 h6⟩⟩
  obtain ⟨c, hc⟩ := exists_eventually_eq_const_mul_of_shifts hh hb hb' hirr hC hD hD0 hgood
  classical
  -- the factor: the constant on the strip, the quotient off it
  refine ⟨fun z => if z ∈ horizontalStrip h then c
    else C z / dozzFormula γ μ U z (α₂ : ℂ) (α₃ : ℂ), ?_, ?_, ?_⟩
  · exact (differentiableOn_const c).congr fun z hz => ite_eq_left hz
  · filter_upwards [hc, hD0] with z hz hDz
    by_cases hzS : z ∈ horizontalStrip h
    · rw [ite_eq_left hzS, hz hzS]
    · rw [ite_eq_right hzS, div_mul_cancel₀ _ hDz]
  · intro z hz
    have hz' : |z.im| < h := hz
    have h1 : z + (γ : ℂ) ∈ horizontalStrip h := by
      change |(z + (γ : ℂ)).im| < h
      simpa using hz'
    have h2 : z + 4 / (γ : ℂ) ∈ horizontalStrip h := by
      change |(z + 4 / (γ : ℂ)).im| < h
      rw [show (4 / (γ : ℂ)) = ((4 / γ : ℝ) : ℂ) by push_cast; ring, Complex.add_im,
        Complex.ofReal_im, add_zero]
      exact hz'
    exact ⟨(ite_eq_left h1).trans (ite_eq_left hz).symm,
      (ite_eq_left h2).trans (ite_eq_left hz).symm⟩

end DOZZ.Proofs

end
