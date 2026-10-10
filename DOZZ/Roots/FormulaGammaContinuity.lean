/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Roots.FormulaRegularity
public import DOZZ.Upsilon.JointContinuity
import DOZZ.Correlations.Analytic.ParameterDomain
import DOZZ.ShiftEquations.Reflection.RbarContinuity
import DOZZ.ShiftEquations.Rbar.Multiplier
/-! # Gamma continuity of the explicit finite DOZZ expression -/
@[expose] public section
open Complex Set Filter Topology
namespace DOZZ.Proofs
/-- The entire characterized Upsilon family is continuous at every subcritical parameter and argument. -/
theorem roots_upsilon_family_continuousAt (U : ℝ → ℂ → ℂ)
    (hU : ∀ g ∈ Ioo (0 : ℝ) 2, IsUpsilon g (U g)) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) :
    ContinuousAt (Function.uncurry U) (γ, z) :=
  (IsUpsilon.continuousOn_uncurry hU).continuousAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨⟨hγ, hγ2⟩, mem_univ z⟩)
/-- The positive real prefactor in the DOZZ expression varies continuously in gamma. -/
theorem roots_continuousAt_dozzBase (γ μ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ContinuousAt (fun g => dozzBase g μ) γ := by
  have hr : 0 < γ ^ 2 / 4 ∧ γ ^ 2 / 4 < 1 := ⟨by positivity, by nlinarith only [hγ, hγ2]⟩
  have hx : (((γ : ℂ) ^ 2 / 4)).re = γ ^ 2 / 4 := by
    have he : ((γ : ℂ) ^ 2 / 4) = ((γ ^ 2 / 4 : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.ofReal_re]
  have h1 : 0 < (((γ : ℂ) ^ 2 / 4)).re := by rw [hx]; exact hr.1
  have h2 : 0 < (1 - (γ : ℂ) ^ 2 / 4).re := by rw [Complex.sub_re, Complex.one_re, hx]; linarith only [hr.2]
  have hm : ContinuousAt (fun g : ℝ => (g : ℂ) ^ 2 / 4) γ := by fun_prop
  have hc : ContinuousAt (fun g : ℝ => lFun ((g : ℂ) ^ 2 / 4)) γ := by
    simpa only [Function.comp_def] using
      (continuousAt_lFun (ne_neg_nat_of_re_pos h1) (ne_neg_nat_of_re_pos h2)).comp (f := fun g : ℝ => (g : ℂ) ^ 2 / 4) hm
  exact (continuousAt_const.mul continuousAt_const).mul (Complex.continuous_re.continuousAt.comp hc)
/-- The finite DOZZ formula is continuous in gamma for every characterized Upsilon family. -/
theorem roots_dozzFormula_gamma_continuousAt (U : ℝ → ℂ → ℂ)
    (hU : ∀ g ∈ Ioo (0 : ℝ) 2, IsUpsilon g (U g))
    (γ μ a b c : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : ExtendedSeiberg3 γ a b c) (hs : ∀ n : ℕ, sExp γ a b c ≠ -(n : ℝ)) :
    ContinuousAt (fun g => dozzFormula g μ (U g) a b c) γ := by
  have hUg := hU γ ⟨hγ, hγ2⟩
  have hUc (w : ℝ → ℂ) (hw : ContinuousAt w γ) : ContinuousAt (fun g => U g (w g)) γ := by
    have hm : ContinuousAt (fun g : ℝ => (g, w g)) γ := continuousAt_id.prodMk hw
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using
      (roots_upsilon_family_continuousAt U hU γ hγ hγ2 (w γ)).comp (f := fun g : ℝ => (g, w g)) hm
  have hder : ContinuousAt (fun g => deriv (U g) 0) γ := by
    have hval := hUc (fun g => ((g / 2 : ℝ) : ℂ)) (by fun_prop)
    apply hval.congr_of_eventuallyEq
    have hn : ∀ᶠ g : ℝ in nhds γ, g ∈ Ioo (0 : ℝ) 2 := isOpen_Ioo.mem_nhds ⟨hγ, hγ2⟩
    filter_upwards [hn] with g hg
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using IsUpsilon.deriv_zero hg.1 hg.2 (hU g hg)
  have hQ := continuousAt_Q hγ.ne'
  have hQc := Complex.continuous_ofReal.continuousAt.comp hQ
  have hExp : ContinuousAt (fun g : ℝ => (2 * Q g - ((a : ℂ) + b + c)) / g) γ :=
    (continuousAt_const.mul hQc |>.sub continuousAt_const).div
      Complex.continuous_ofReal.continuousAt (Complex.ofReal_ne_zero.mpr hγ.ne')
  have hrealpow : ContinuousAt (fun g : ℝ => (g / 2) ^ (2 - g ^ 2 / 2)) γ :=
    (continuousAt_id.div_const 2).rpow (by fun_prop) (Or.inl (by positivity : γ / 2 ≠ 0))
  have hbase : ContinuousAt (fun g : ℝ => ((dozzBase g μ * (g / 2) ^ (2 - g ^ 2 / 2) : ℝ) : ℂ)) γ :=
    Complex.continuous_ofReal.continuousAt.comp ((roots_continuousAt_dozzBase γ μ hγ hγ2).mul hrealpow)
  have hp := hbase.cpow hExp (Complex.ofReal_mem_slitPlane.mpr (dozzFormula_base_pos hγ hγ2 hμ))
  have hn : ContinuousAt (fun g => deriv (U g) 0 * U g a * U g b * U g c) γ :=
    ((hder.mul (hUc _ continuousAt_const)).mul (hUc _ continuousAt_const)).mul (hUc _ continuousAt_const)
  have hd : ContinuousAt (fun g : ℝ =>
      U g (((a : ℂ) + b + c - 2 * Q g) / 2) * U g (((a : ℂ) + b + c) / 2 - a) *
        U g (((a : ℂ) + b + c) / 2 - b) * U g (((a : ℂ) + b + c) / 2 - c)) γ :=
    (((hUc _ ((continuousAt_const.sub (continuousAt_const.mul hQc)).div_const _)).mul
      (hUc _ continuousAt_const)).mul (hUc _ continuousAt_const)).mul (hUc _ continuousAt_const)
  exact (hp.mul hn).div hd (roots_dozz_denominator_ne_zero hγ hγ2 hUg hα hs)
end DOZZ.Proofs
