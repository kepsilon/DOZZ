/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.AffineMoment
public import DOZZ.ShiftEquations.Mobius.Algebra
import DOZZ.ShiftEquations.Mobius.InversionMoment

/-!
# Coulomb moments under Möbius charts

Every finite Möbius chart is affine (`c = 0`) or an affine map of the inversion of an affine map
(`c ≠ 0`). Composing the affine moment identity with the inversion moment identity gives, for
roots with finite images,
`E[I_{ψz}^{-s}] = ∏ᵢ |ψ'(zᵢ)|^{γ αᵢ s / 2} E[I_z^{-s}]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- The power of a positive real, in exponential form. -/
theorem rpow_eq_exp_mul_log {x : ℝ} (hx : 0 < x) (p : ℝ) : x ^ p = Real.exp (p * Real.log x) := by
  rw [Real.rpow_def_of_pos hx, mul_comm]

/-- **Coulomb moments under a Möbius chart.** -/
theorem coulombMass_mobius_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {N : ℕ} (α : Fin N → ℝ) (z : Fin N → ℂ)
    (ψ : MobiusChart) (hfinite : ∀ i, ψ.c * z i + ψ.d ≠ 0) :
    ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α (fun i => mobiusMap ψ (z i)) 0)
        (-nPointSExp γ α) ∂P =
      ENNReal.ofReal (∏ i, ‖deriv (mobiusMap ψ) (z i)‖ ^ (γ * α i * nPointSExp γ α / 2)) *
        ∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z 0) (-nPointSExp γ α) ∂P := by
  set s := nPointSExp γ α with hs
  set S := ∑ i, α i with hS
  have hsum : ∀ x : ℝ, ∑ i, x * α i = x * S := fun x => by rw [hS, Finset.mul_sum]
  have hder : ∀ i, ‖deriv (mobiusMap ψ) (z i)‖ =
      ‖ψ.a * ψ.d - ψ.b * ψ.c‖ / ‖ψ.c * z i + ψ.d‖ ^ 2 :=
    fun i => norm_deriv_mobiusMap ψ (hfinite i)
  have hdet : 0 < ‖ψ.a * ψ.d - ψ.b * ψ.c‖ := norm_pos_iff.mpr ψ.determinant_ne
  have hw : ∀ i, 0 < ‖ψ.c * z i + ψ.d‖ := fun i => norm_pos_iff.mpr (hfinite i)
  -- the target constant, in exponential form
  have htarget : ∏ i, ‖deriv (mobiusMap ψ) (z i)‖ ^ (γ * α i * s / 2) =
      Real.exp (γ * S * s / 2 * Real.log ‖ψ.a * ψ.d - ψ.b * ψ.c‖ -
        ∑ i, γ * α i * s * Real.log ‖ψ.c * z i + ψ.d‖) := by
    have hfac : ∀ i, ‖deriv (mobiusMap ψ) (z i)‖ ^ (γ * α i * s / 2) =
        Real.exp (γ * α i * s / 2 * (Real.log ‖ψ.a * ψ.d - ψ.b * ψ.c‖ -
          2 * Real.log ‖ψ.c * z i + ψ.d‖)) := fun i => by
      rw [hder i, rpow_eq_exp_mul_log (div_pos hdet (pow_pos (hw i) 2)),
        Real.log_div hdet.ne' (pow_pos (hw i) 2).ne', Real.log_pow]
      push_cast
      ring_nf
    rw [Finset.prod_congr rfl fun i _ => hfac i, ← Real.exp_sum]
    congr 1
    rw [show (∑ i, γ * α i * s / 2 * (Real.log ‖ψ.a * ψ.d - ψ.b * ψ.c‖ -
        2 * Real.log ‖ψ.c * z i + ψ.d‖)) =
        (∑ i, (γ * s / 2 * Real.log ‖ψ.a * ψ.d - ψ.b * ψ.c‖) * α i) -
          ∑ i, γ * α i * s * Real.log ‖ψ.c * z i + ψ.d‖ by
      rw [← Finset.sum_sub_distrib]
      congr 1
      funext i
      ring, hsum]
    ring
  by_cases hc : ψ.c = 0
  · -- an affine chart
    have hd := mobiusChart_d_ne_zero_of_c_eq_zero ψ hc
    have ha := mobiusChart_a_ne_zero_of_c_eq_zero ψ hc
    have hA : ψ.a / ψ.d ≠ 0 := div_ne_zero ha hd
    have hfun : (fun i => mobiusMap ψ (z i)) = fun i => ψ.a / ψ.d * z i + ψ.b / ψ.d :=
      funext fun i => mobiusMap_of_c_eq_zero ψ hc (z i)
    rw [hfun, coulombMass_affine_moment P X hX γ hγ hγ2 M hM α z _ _ hA, htarget]
    congr 2
    have hAn : 0 < ‖ψ.a / ψ.d‖ := norm_pos_iff.mpr hA
    rw [rpow_eq_exp_mul_log hAn]
    congr 1
    have hlog : ∀ i, Real.log ‖ψ.c * z i + ψ.d‖ = Real.log ‖ψ.d‖ := fun i => by
      rw [hc, zero_mul, zero_add]
    simp_rw [hlog]
    rw [hc, mul_zero, sub_zero, norm_div, norm_mul, Real.log_div (norm_pos_iff.mpr ha).ne'
      (norm_pos_iff.mpr hd).ne', Real.log_mul (norm_pos_iff.mpr ha).ne'
      (norm_pos_iff.mpr hd).ne', ← Finset.sum_mul, show ∑ i, γ * α i * s = γ * S * s by
        rw [hS, Finset.mul_sum, Finset.sum_mul]]
    ring
  · -- an affine map of the inversion of an affine map
    have hA2 : -((ψ.a * ψ.d - ψ.b * ψ.c) / ψ.c) ≠ 0 :=
      neg_ne_zero.mpr (div_ne_zero ψ.determinant_ne hc)
    have hfun : (fun i => mobiusMap ψ (z i)) =
        fun i => -((ψ.a * ψ.d - ψ.b * ψ.c) / ψ.c) * (ψ.c * z i + ψ.d)⁻¹ + ψ.a / ψ.c :=
      funext fun i => mobiusMap_of_c_ne_zero ψ hc (hfinite i)
    rw [hfun, coulombMass_affine_moment P X hX γ hγ hγ2 M hM α
        (fun i => (ψ.c * z i + ψ.d)⁻¹) _ _ hA2,
      coulombMass_inv_moment P X hX γ hγ hγ2 M hM α (fun i => ψ.c * z i + ψ.d) hfinite (-s),
      coulombMass_affine_moment P X hX γ hγ hγ2 M hM α z ψ.c ψ.d hc, htarget,
      ← mul_assoc, ← mul_assoc]
    congr 1
    have hcn : 0 < ‖ψ.c‖ := norm_pos_iff.mpr hc
    have hA2n : 0 < ‖-((ψ.a * ψ.d - ψ.b * ψ.c) / ψ.c)‖ := norm_pos_iff.mpr hA2
    have hprod : ENNReal.rpow (∏ k, ENNReal.rpow (ENNReal.ofReal ‖ψ.c * z k + ψ.d‖) (γ * α k))
        (-s) = ENNReal.ofReal (Real.exp (-s * ∑ k, γ * α k * Real.log ‖ψ.c * z k + ψ.d‖)) := by
      simp only [ENNReal.rpow_eq_pow]
      rw [Finset.prod_congr rfl fun k _ => ENNReal.ofReal_rpow_of_pos (hw k),
        ← ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.rpow_pos_of_pos (hw k) _).le,
        ENNReal.ofReal_rpow_of_pos (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (hw k) _)]
      congr 1
      rw [Finset.prod_congr rfl fun k _ => rpow_eq_exp_mul_log (hw k) (γ * α k), ← Real.exp_sum,
        ← Real.exp_mul, Finset.sum_mul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hprod, rpow_eq_exp_mul_log hA2n, rpow_eq_exp_mul_log hcn,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← Real.exp_add, ← Real.exp_add]
    congr 2
    have hlogA : Real.log ‖-((ψ.a * ψ.d - ψ.b * ψ.c) / ψ.c)‖ =
        Real.log ‖ψ.a * ψ.d - ψ.b * ψ.c‖ - Real.log ‖ψ.c‖ := by
      rw [norm_neg, norm_div, Real.log_div hdet.ne' hcn.ne']
    have hsum3 : ∑ i, γ * α i * s * Real.log ‖ψ.c * z i + ψ.d‖ =
        s * ∑ i, γ * α i * Real.log ‖ψ.c * z i + ψ.d‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hlogA, ← hS, ← hs, hsum3]
    ring

end DOZZ.Proofs

end
