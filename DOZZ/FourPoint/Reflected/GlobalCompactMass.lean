/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalMassIterated
public import DOZZ.FourPoint.Reflected.SpatialCutoffs
/-! Compact real tests equal the actual nonnegative global lateral masses. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_global_reinsertionWeight_nonneg (γ : ℝ) (a : TwoSidedPath) (x : ℂ) :
    0 ≤ reflected_global_reinsertionWeight γ a x := by
  unfold reflected_global_reinsertionWeight
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

theorem reflected_global_reinsertionWeight_continuousOn (γ : ℝ) (a : TwoSidedPath) :
    ContinuousOn (reflected_global_reinsertionWeight γ a) ({0} : Set ℂ)ᶜ := by
  intro x hx
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hx)
  have hl : ContinuousAt (fun x : ℂ => Real.log ‖x‖) x :=
    continuous_norm.continuousAt.log hx0
  have hc : ContinuousAt (fun x : ℂ => Real.exp
      (γ*a (-Real.log ‖x‖)-γ*Q γ*|Real.log ‖x‖|)) x :=
    ((continuousAt_const.mul (a.continuous.continuousAt.comp hl.neg)).sub
      (continuousAt_const.mul hl.abs)).rexp
  apply hc.continuousWithinAt.congr
  · intro y hy
    have hy0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr (by simpa using hy)
    simp only [reflected_global_reinsertionWeight, ite_eq_right hy0]
  · simp only [reflected_global_reinsertionWeight, ite_eq_right hx0]

/-- A nonnegative compact real radial test is exactly the extended-real lateral mass. -/
theorem reflected_global_compact_test_ofReal (γ : ℝ) (a : TwoSidedPath)
    (μ : Measure ℂ) (K : Set ℂ) (hK : IsCompact K) (hK0 : K ⊆ ({0} : Set ℂ)ᶜ)
    (hμ : μ K < ⊤) (f : BoundedContinuousFunction ℂ ℝ) (hf : ∀ x, 0 ≤ f x)
    (hfK : tsupport (f : ℂ → ℝ) ⊆ K) :
    ENNReal.ofReal (∫ x, f x*reflected_global_reinsertionWeight γ a x ∂μ) =
      ∫⁻ x in K, ENNReal.ofReal (f x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ := by
  obtain ⟨g, hg, hgs⟩ := reflected_compact_weighted_test ({0} : Set ℂ)ᶜ
    (isClosed_singleton (x := (0 : ℂ))).isOpen_compl f
    (hK.of_isClosed_subset (isClosed_tsupport _) hfK) (hfK.trans hK0)
    (reflected_global_reinsertionWeight γ a)
    (reflected_global_reinsertionWeight_continuousOn γ a)
  have hgn : ∀ x, 0 ≤ g x := fun x => by
    rw [hg x]
    exact mul_nonneg (hf x) (reflected_global_reinsertionWeight_nonneg γ a x)
  have he := reflected_compact_test_integral_ofReal μ K hK hμ g hgn (hgs.trans hfK)
  simp_rw [hg] at he
  exact he.trans (lintegral_congr fun x => ENNReal.ofReal_mul (hf x))

end DOZZ.Proofs
