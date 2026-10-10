/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.KernelIncrementScale
public import DOZZ.FourPoint.Reflected.InverseMassExpectation
/-! Kernel coefficient bounds remain valid for infinite added masses. -/
@[expose] public section
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_ennreal_inverse_increment_scaled (p c : ℝ) (A J : ℝ≥0∞)
    (hp : 0 < p) (hc : 0 < c) (hA : 0 < A) (hAf : A ≠ ⊤) :
    max 1 c*(((A+J)^(-p)).toReal-(A^(-p)).toReal) ≤
      ((A+ENNReal.ofReal c*J)^(-p)).toReal-(A^(-p)).toReal ∧
    ((A+ENNReal.ofReal c*J)^(-p)).toReal-(A^(-p)).toReal ≤
      min 1 c*(((A+J)^(-p)).toReal-(A^(-p)).toReal) := by
  by_cases hJ : J = ⊤
  · have hcN : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
    simp only [hJ,ENNReal.mul_top hcN,add_top,ENNReal.top_rpow_of_neg (neg_neg_of_pos hp),
      ENNReal.toReal_zero,zero_sub]
    have hmax : 1 ≤ max 1 c := le_max_left _ _
    have hmin : min 1 c ≤ 1 := min_le_left _ _
    have hn := ENNReal.toReal_nonneg (a := A^(-p))
    constructor <;> nlinarith only [hmax,hmin,hn]
  · have hcf : ENNReal.ofReal c*J ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJ
    simp only [← ENNReal.toReal_rpow,ENNReal.toReal_add hAf hJ,
      ENNReal.toReal_add hAf hcf,ENNReal.toReal_mul,ENNReal.toReal_ofReal hc.le]
    exact reflected_inverse_increment_scaled p A.toReal J.toReal c hp.le
      (ENNReal.toReal_pos hA.ne' hAf) ENNReal.toReal_nonneg hc

theorem reflected_ennreal_kernel_increment_squeeze (p cLo cHi : ℝ) (A J I : ℝ≥0∞)
    (hp : 0 < p) (hcLo : 0 < cLo) (hcHi : 0 < cHi) (hA : 0 < A) (hAf : A ≠ ⊤)
    (hlo : ENNReal.ofReal cLo*J ≤ I) (hhi : I ≤ ENNReal.ofReal cHi*J) :
    max 1 cHi*(((A+J)^(-p)).toReal-(A^(-p)).toReal) ≤
      ((A+I)^(-p)).toReal-(A^(-p)).toReal ∧
    ((A+I)^(-p)).toReal-(A^(-p)).toReal ≤
      min 1 cLo*(((A+J)^(-p)).toReal-(A^(-p)).toReal) := by
  have hl := reflected_ennreal_inverse_increment_scaled p cLo A J hp hcLo hA hAf
  have hh := reflected_ennreal_inverse_increment_scaled p cHi A J hp hcHi hA hAf
  have hfin : A^(-p) ≠ ⊤ := by
    simp only [ne_eq,ENNReal.rpow_eq_top_iff,hA.ne',hAf,false_and,false_or,not_false_eq_true]
  have hbound (K : ℝ≥0∞) : (A+K)^(-p) ≠ ⊤ := ne_top_of_le_ne_top hfin
    (ennreal_rpow_antitone_of_nonpos (le_add_of_nonneg_right (show 0 ≤ K from bot_le))
      (neg_nonpos.mpr hp.le))
  refine ⟨hh.1.trans (sub_le_sub_right (ENNReal.toReal_mono (hbound I)
    (ennreal_rpow_antitone_of_nonpos (add_le_add_right hhi A) (neg_nonpos.mpr hp.le))) _),?_⟩
  exact (sub_le_sub_right (ENNReal.toReal_mono (hbound (ENNReal.ofReal cLo*J))
    (ennreal_rpow_antitone_of_nonpos (add_le_add_right hlo A) (neg_nonpos.mpr hp.le))) _).trans hl.2

end DOZZ.Proofs
