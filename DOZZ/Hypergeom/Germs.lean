/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Series
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.NhdsWithin

/-! Endpoint values, derivatives, and principal-power germs for the local bases. -/

@[expose] public section

open Filter Set Topology

namespace DOZZ.Proofs

/-- Endpoint germs used in the crossing and fusion comparisons of [KRV, §4.2] and [KRV, §4.3]. The
unpowered factors tend to one at their regular singular points; the two powered bases have the
displayed leading powers. -/
theorem gauss_local_basis_germs {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    gaussFMinus H a b c 0 = 1 ∧
    HasDerivAt (gaussFMinus H a b c) (a * b / c) 0 ∧
    Tendsto (fun z : ℂ => gaussFPlus H a b c z / z ^ (1 - c))
      (nhdsWithin 0 gaussCutPlane) (nhds 1) ∧
    gaussGMinus H a b c 1 = 1 ∧
    HasDerivAt (gaussGMinus H a b c) (-(a * b / (1 + a + b - c))) 1 ∧
    Tendsto (fun z : ℂ => gaussGPlus H a b c z / (1 - z) ^ (c - a - b))
      (nhdsWithin 1 gaussCutPlane) (nhds 1) := by
  have hcN : ∀ n : ℕ, c ≠ -(n : ℂ) := by
    intro n heq
    apply hc (-(n : ℤ))
    exact heq.trans (by simp)
  have htwoC : ∀ n : ℕ, 2 - c ≠ -(n : ℂ) := by
    intro n heq
    apply hc (n + 2)
    have hcast : c = ((n : ℂ) + 2) := by
      calc
        c = 2 - (2 - c) := by ring
        _ = 2 - (-(n : ℂ)) := by rw [heq]
        _ = (n : ℂ) + 2 := by ring
    exact_mod_cast hcast
  have hdeltaMinus : ∀ n : ℕ, 1 + a + b - c ≠ -(n : ℂ) := by
    intro n heq
    apply hδ (n + 1)
    have hcast : c - a - b = (n : ℂ) + 1 := by
      calc
        c - a - b = 1 - (1 + a + b - c) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [heq]
        _ = (n : ℂ) + 1 := by ring
    exact_mod_cast hcast
  have hdeltaPlus : ∀ n : ℕ, 1 + c - a - b ≠ -(n : ℂ) := by
    intro n heq
    apply hδ (-(n + 1))
    have hcast : c - a - b = -((n : ℂ) + 1) := by
      calc
        c - a - b = (1 + c - a - b) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [heq]
        _ = -((n : ℂ) + 1) := by ring
    exact_mod_cast hcast
  have hminusChar : IsGaussHypergeometric a b c (H a b c) := hH a b c hcN
  have hminusAtZero : H a b c 0 = 1 := by
    have h := hminusChar.2 0 (by norm_num)
    simpa using h
  have hminusDeriv : HasDerivAt (H a b c) (a * b / c) 0 :=
    gauss_family_hasDerivAt_zero hH a b c hcN
  have hplusDeriv : HasDerivAt
      (H (a - c + 1) (b - c + 1) (2 - c))
      ((a - c + 1) * (b - c + 1) / (2 - c)) 0 :=
    gauss_family_hasDerivAt_zero hH (a - c + 1) (b - c + 1) (2 - c) htwoC
  have hplusCont : ContinuousAt
      (H (a - c + 1) (b - c + 1) (2 - c)) 0 := hplusDeriv.continuousAt
  have hplusAtOne : H (a - c + 1) (b - c + 1) (2 - c) 0 = 1 := by
    have hchar := hH (a - c + 1) (b - c + 1) (2 - c) htwoC
    simpa using hchar.2 0 (by norm_num)
  have hminusOneChar : IsGaussHypergeometric a b (1 + a + b - c)
      (H a b (1 + a + b - c)) := hH a b (1 + a + b - c) hdeltaMinus
  have hminusOneAtZero : H a b (1 + a + b - c) 0 = 1 := by
    simpa using hminusOneChar.2 0 (by norm_num)
  have hminusOneDeriv : HasDerivAt (H a b (1 + a + b - c))
      (a * b / (1 + a + b - c)) 0 :=
    gauss_family_hasDerivAt_zero hH a b (1 + a + b - c) hdeltaMinus
  have hplusOneDeriv : HasDerivAt
      (H (c - b) (c - a) (1 + c - a - b))
      ((c - b) * (c - a) / (1 + c - a - b)) 0 :=
    gauss_family_hasDerivAt_zero hH (c - b) (c - a) (1 + c - a - b) hdeltaPlus
  have hplusOneCont : ContinuousAt
      (H (c - b) (c - a) (1 + c - a - b)) 0 := hplusOneDeriv.continuousAt
  have hplusOneAtZero : H (c - b) (c - a) (1 + c - a - b) 0 = 1 := by
    have hchar := hH (c - b) (c - a) (1 + c - a - b) hdeltaPlus
    simpa using hchar.2 0 (by norm_num)
  have hcutZero : ∀ z ∈ gaussCutPlane, z ≠ 0 := by
    intro z hz
    change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
    rcases hz with him | ⟨hpos, _⟩
    · intro hzero
      apply him
      simp [hzero]
    · intro hzero
      have hzre : z.re = 0 := by simp [hzero]
      linarith
  have hcutOne : ∀ z ∈ gaussCutPlane, 1 - z ≠ 0 := by
    intro z hz hzero
    have hzone : z = 1 := (sub_eq_zero.mp hzero).symm
    change z.im ≠ 0 ∨ (0 < z.re ∧ z.re < 1) at hz
    rw [hzone] at hz
    simp at hz
  have hFplusRatio : EqOn
      (fun z : ℂ => gaussFPlus H a b c z / z ^ (1 - c))
      (fun z => H (a - c + 1) (b - c + 1) (2 - c) z) gaussCutPlane := by
    intro z hz
    simp only [gaussFPlus]
    exact mul_div_cancel_left₀ _ (Complex.cpow_ne_zero_iff.mpr (Or.inl (hcutZero z hz)))
  have hGplusRatio : EqOn
      (fun z : ℂ => gaussGPlus H a b c z / (1 - z) ^ (c - a - b))
      (fun z => H (c - b) (c - a) (1 + c - a - b) (1 - z)) gaussCutPlane := by
    intro z hz
    simp only [gaussGPlus]
    exact mul_div_cancel_left₀ _
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (hcutOne z hz)))
  have hid : Tendsto (fun z : ℂ => z) (nhdsWithin 0 gaussCutPlane) (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hFplusLimit : Tendsto
      (fun z : ℂ => H (a - c + 1) (b - c + 1) (2 - c) z)
      (nhdsWithin 0 gaussCutPlane) (nhds 1) := by
    simpa [Function.comp_def, hplusAtOne] using hplusCont.tendsto.comp hid
  have hmapOne : Tendsto (fun z : ℂ => 1 - z)
      (nhdsWithin 1 gaussCutPlane) (nhds 0) := by
    have hcont : ContinuousAt (fun z : ℂ => 1 - z) 1 := by fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hGplusLimit : Tendsto
      (fun z : ℂ => H (c - b) (c - a) (1 + c - a - b) (1 - z))
      (nhdsWithin 1 gaussCutPlane) (nhds 1) := by
    simpa [Function.comp_def, hplusOneAtZero] using hplusOneCont.tendsto.comp hmapOne
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hminusAtZero
  · have hfun : gaussFMinus H a b c = H a b c := by
      funext z
      rfl
    rw [hfun]
    exact hminusDeriv
  · exact (tendsto_congr' hFplusRatio.eventuallyEq_nhdsWithin).2 hFplusLimit
  · simpa only [gaussGMinus, sub_self] using hminusOneAtZero
  · have hminusOneDeriv' : HasDerivAt (H a b (1 + a + b - c))
        (a * b / (1 + a + b - c)) (1 - 1 : ℂ) := by
      simpa using hminusOneDeriv
    have hcomp := hminusOneDeriv'.comp_const_sub (1 : ℂ) (1 : ℂ)
    have hfun : gaussGMinus H a b c =
        (fun z : ℂ => H a b (1 + a + b - c) (1 - z)) := by
      funext z
      rfl
    rw [hfun]
    exact hcomp
  · exact (tendsto_congr' hGplusRatio.eventuallyEq_nhdsWithin).2 hGplusLimit

end DOZZ.Proofs
