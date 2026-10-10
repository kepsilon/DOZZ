/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisWronskians
public import DOZZ.Hypergeom.ODE.CutPlaneTopology

/-! A nonvanishing Wronskian gives a global basis of Gauss solutions. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The Wronskian of two holomorphic Gauss solutions satisfies Abel's identity. -/
theorem gauss_pair_wronskian_abel
    (a b c : ℂ) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f gaussCutPlane)
    (hg : AnalyticOnNhd ℂ g gaussCutPlane)
    (hfeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c f z = 0)
    (hgeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c g z = 0) :
    ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv (fun w => f w * deriv g w - deriv f w * g w) z +
        (c - (a + b + 1) * z) *
          (f z * deriv g z - deriv f z * g z) = 0 := by
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  have hf₁ : AnalyticOnNhd ℂ (deriv f) gaussCutPlane := hf.deriv
  have hg₁ : AnalyticOnNhd ℂ (deriv g) gaussCutPlane := hg.deriv
  have hWanalytic : AnalyticOnNhd ℂ W gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => f z * deriv g z - deriv f z * g z)
      gaussCutPlane
    exact (hf.mul hg₁).sub (hf₁.mul hg)
  have hWderiv : ∀ z ∈ gaussCutPlane,
      deriv W z = f z * deriv (deriv g) z - deriv (deriv f) z * g z := by
    intro z hz
    have hleft := (hf z hz).differentiableAt.hasDerivAt.mul
      (hg₁ z hz).differentiableAt.hasDerivAt
    have hright := (hf₁ z hz).differentiableAt.hasDerivAt.mul
      (hg z hz).differentiableAt.hasDerivAt
    have hsub := hleft.sub hright
    change deriv (fun w => f w * deriv g w - deriv f w * g w) z = _
    have hfun : (fun w => f w * deriv g w - deriv f w * g w) =
        f * deriv g - deriv f * g := by
      funext w
      rfl
    rw [hfun, hsub.deriv]
    ring
  intro z hz
  rw [hWderiv z hz]
  have hfeq := hfeq z hz
  have hgeq := hgeq z hz
  dsimp [gaussHolomorphicOperator] at hfeq hgeq
  linear_combination (f z) * hgeq - (g z) * hfeq

/-- On the principal cut plane, any solution is the unique constant linear combination of two
holomorphic solutions whose Wronskian never vanishes. -/
theorem gauss_two_solution_span_unique
    (a b c : ℂ) (f g : ℂ → ℂ)
    (hfDiff : DifferentiableOn ℂ f gaussCutPlane)
    (hgDiff : DifferentiableOn ℂ g gaussCutPlane)
    (hfeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c f z = 0)
    (hgeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c g z = 0)
    (hWne : ∀ z ∈ gaussCutPlane,
      f z * deriv g z - deriv f z * g z ≠ 0)
    (y : ℂ → ℂ) (hyDiff : DifferentiableOn ℂ y gaussCutPlane)
    (hyeq : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c y z = 0) :
    ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
      y z = v.1 * f z + v.2 * g z := by
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  let A : ℂ → ℂ := fun z => y z * deriv g z - deriv y z * g z
  let B : ℂ → ℂ := fun z => f z * deriv y z - deriv f z * y z
  let α : ℂ → ℂ := fun z => A z / W z
  let β : ℂ → ℂ := fun z => B z / W z
  have hfAnalytic : AnalyticOnNhd ℂ f gaussCutPlane :=
    hfDiff.analyticOnNhd gaussCutPlane_isOpen
  have hgAnalytic : AnalyticOnNhd ℂ g gaussCutPlane :=
    hgDiff.analyticOnNhd gaussCutPlane_isOpen
  have hyAnalytic : AnalyticOnNhd ℂ y gaussCutPlane :=
    hyDiff.analyticOnNhd gaussCutPlane_isOpen
  have hf₁ : AnalyticOnNhd ℂ (deriv f) gaussCutPlane := hfAnalytic.deriv
  have hg₁ : AnalyticOnNhd ℂ (deriv g) gaussCutPlane := hgAnalytic.deriv
  have hy₁ : AnalyticOnNhd ℂ (deriv y) gaussCutPlane := hyAnalytic.deriv
  have hWanalytic : AnalyticOnNhd ℂ W gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => f z * deriv g z - deriv f z * g z)
      gaussCutPlane
    exact (hfAnalytic.mul hg₁).sub (hf₁.mul hgAnalytic)
  have hAanalytic : AnalyticOnNhd ℂ A gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => y z * deriv g z - deriv y z * g z)
      gaussCutPlane
    exact (hyAnalytic.mul hg₁).sub (hy₁.mul hgAnalytic)
  have hBanalytic : AnalyticOnNhd ℂ B gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => f z * deriv y z - deriv f z * y z)
      gaussCutPlane
    exact (hfAnalytic.mul hy₁).sub (hf₁.mul hyAnalytic)
  have hWabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv W z +
        (c - (a + b + 1) * z) * W z = 0 := by
    intro z hz
    simpa [W] using gauss_pair_wronskian_abel a b c f g
      hfAnalytic hgAnalytic hfeq hgeq z hz
  have hAabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv A z +
        (c - (a + b + 1) * z) * A z = 0 := by
    intro z hz
    simpa [A] using gauss_pair_wronskian_abel a b c y g
      hyAnalytic hgAnalytic hyeq hgeq z hz
  have hBabel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv B z +
        (c - (a + b + 1) * z) * B z = 0 := by
    intro z hz
    simpa [B] using gauss_pair_wronskian_abel a b c f y
      hfAnalytic hyAnalytic hfeq hyeq z hz
  have hWdiff : DifferentiableOn ℂ W gaussCutPlane := hWanalytic.differentiableOn
  have hAdiff : DifferentiableOn ℂ A gaussCutPlane := hAanalytic.differentiableOn
  have hBdiff : DifferentiableOn ℂ B gaussCutPlane := hBanalytic.differentiableOn
  have hαdiff : DifferentiableOn ℂ α gaussCutPlane := by
    exact hAdiff.div hWdiff hWne
  have hβdiff : DifferentiableOn ℂ β gaussCutPlane := by
    exact hBdiff.div hWdiff hWne
  have hαderivZero : gaussCutPlane.EqOn (deriv α) (fun _ => 0) := by
    intro z hz
    have hAAt := (hAanalytic z hz).differentiableAt
    have hWAt := (hWanalytic z hz).differentiableAt
    have hquot := (hAAt.hasDerivAt.div hWAt.hasDerivAt (hWne z hz)).deriv
    have hreg := gaussCutPlane_subset_regularPlane hz
    have hden : z * (1 - z) ≠ 0 :=
      mul_ne_zero hreg.1 (sub_ne_zero.mpr (Ne.symm hreg.2))
    have hnum : deriv A z * W z - A z * deriv W z = 0 := by
      have hmul : z * (1 - z) *
          (deriv A z * W z - A z * deriv W z) = 0 := by
        linear_combination (W z) * hAabel z hz - (A z) * hWabel z hz
      exact (mul_eq_zero.mp hmul).resolve_left hden
    change deriv (A / W) z = 0
    rw [hquot, hnum]
    simp
  have hβderivZero : gaussCutPlane.EqOn (deriv β) (fun _ => 0) := by
    intro z hz
    have hBAt := (hBanalytic z hz).differentiableAt
    have hWAt := (hWanalytic z hz).differentiableAt
    have hquot := (hBAt.hasDerivAt.div hWAt.hasDerivAt (hWne z hz)).deriv
    have hreg := gaussCutPlane_subset_regularPlane hz
    have hden : z * (1 - z) ≠ 0 :=
      mul_ne_zero hreg.1 (sub_ne_zero.mpr (Ne.symm hreg.2))
    have hnum : deriv B z * W z - B z * deriv W z = 0 := by
      have hmul : z * (1 - z) *
          (deriv B z * W z - B z * deriv W z) = 0 := by
        linear_combination (W z) * hBabel z hz - (B z) * hWabel z hz
      exact (mul_eq_zero.mp hmul).resolve_left hden
    change deriv (B / W) z = 0
    rw [hquot, hnum]
    simp
  have hcutPre : IsPreconnected gaussCutPlane := by
    rw [isPreconnected_iff_preconnectedSpace]
    infer_instance
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hαconst : ∀ z ∈ gaussCutPlane, α z = α (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hαdiff hαderivZero hz hmid
  have hβconst : ∀ z ∈ gaussCutPlane, β z = β (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hβdiff hβderivZero hz hmid
  have hdecompose : ∀ z ∈ gaussCutPlane,
      y z = α z * f z + β z * g z := by
    intro z hz
    have hden := hWne z hz
    have hnum : A z * f z + B z * g z = y z * W z := by
      dsimp [A, B, W]
      ring
    calc
      y z = y z * (W z / W z) := by rw [div_self hden, mul_one]
      _ = y z * W z / W z := by ring
      _ = (A z * f z + B z * g z) / W z := by rw [hnum]
      _ = A z / W z * f z + B z / W z * g z := by
        field_simp [hden]
  let v : ℂ × ℂ := (α (1 / 2), β (1 / 2))
  have hv : ∀ z ∈ gaussCutPlane, y z = v.1 * f z + v.2 * g z := by
    intro z hz
    calc
      y z = α z * f z + β z * g z := hdecompose z hz
      _ = v.1 * f z + v.2 * g z := by
        dsimp [v]
        rw [hαconst z hz, hβconst z hz]
  refine ⟨v, hv, ?_⟩
  intro v' hv'
  have hmidValue : y (1 / 2) =
      v'.1 * f (1 / 2) + v'.2 * g (1 / 2) := hv' (1 / 2) hmid
  have hchosenValue : y (1 / 2) =
      v.1 * f (1 / 2) + v.2 * g (1 / 2) := hv (1 / 2) hmid
  have hFAt : DifferentiableAt ℂ f (1 / 2) := (hfAnalytic (1 / 2) hmid).differentiableAt
  have hGAt : DifferentiableAt ℂ g (1 / 2) := (hgAnalytic (1 / 2) hmid).differentiableAt
  have hlinearDeriv (r s : ℂ) :
      deriv (fun z => r * f z + s * g z) (1 / 2) =
        r * deriv f (1 / 2) + s * deriv g (1 / 2) := by
    have hsum := (hFAt.hasDerivAt.const_mul r).add (hGAt.hasDerivAt.const_mul s)
    exact hsum.deriv
  have hmidDeriv (r s : ℂ)
      (hvalues : ∀ z ∈ gaussCutPlane, y z = r * f z + s * g z) :
      deriv y (1 / 2) = r * deriv f (1 / 2) + s * deriv g (1 / 2) := by
    have hEqOn : gaussCutPlane.EqOn y (fun z => r * f z + s * g z) := hvalues
    have hderiv := hEqOn.deriv gaussCutPlane_isOpen hmid
    calc
      deriv y (1 / 2) = deriv (fun z => r * f z + s * g z) (1 / 2) := hderiv
      _ = r * deriv f (1 / 2) + s * deriv g (1 / 2) := hlinearDeriv r s
  have hE0 : (v'.1 - v.1) * f (1 / 2) + (v'.2 - v.2) * g (1 / 2) = 0 := by
    calc
      _ = (v'.1 * f (1 / 2) + v'.2 * g (1 / 2)) -
          (v.1 * f (1 / 2) + v.2 * g (1 / 2)) := by ring
      _ = y (1 / 2) - y (1 / 2) := by rw [← hmidValue, ← hchosenValue]
      _ = 0 := by ring
  have hE1 : (v'.1 - v.1) * deriv f (1 / 2) +
      (v'.2 - v.2) * deriv g (1 / 2) = 0 := by
    calc
      _ = (v'.1 * deriv f (1 / 2) + v'.2 * deriv g (1 / 2)) -
          (v.1 * deriv f (1 / 2) + v.2 * deriv g (1 / 2)) := by ring
      _ = deriv y (1 / 2) - deriv y (1 / 2) := by
        rw [← hmidDeriv v'.1 v'.2 hv', ← hmidDeriv v.1 v.2 hv]
      _ = 0 := by ring
  have hWmid : W (1 / 2) ≠ 0 := by
    simpa [W] using hWne (1 / 2) hmid
  apply Prod.ext
  · have hprod : (v'.1 - v.1) * W (1 / 2) = 0 := by
      dsimp [W]
      linear_combination (deriv g (1 / 2)) * hE0 - g (1 / 2) * hE1
    have hdiff : v'.1 - v.1 = 0 := (mul_eq_zero.mp hprod).resolve_right hWmid
    exact sub_eq_zero.mp hdiff
  · have hprod : (v'.2 - v.2) * W (1 / 2) = 0 := by
      dsimp [W]
      linear_combination f (1 / 2) * hE1 - deriv f (1 / 2) * hE0
    have hdiff : v'.2 - v.2 = 0 := (mul_eq_zero.mp hprod).resolve_right hWmid
    exact sub_eq_zero.mp hdiff

/-- The zero-end local basis, including its Wronskian and global spanning property. -/
theorem gauss_local_basis_zero {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussFMinus H a b c) gaussCutPlane ∧
    DifferentiableOn ℂ (gaussFPlus H a b c) gaussCutPlane ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c (gaussFMinus H a b c) z = 0 ∧
      gaussHolomorphicOperator a b c (gaussFPlus H a b c) z = 0 ∧
      gaussFMinus H a b c z * deriv (gaussFPlus H a b c) z -
        deriv (gaussFMinus H a b c) z * gaussFPlus H a b c z =
          (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) ∧
    (∀ y : ℂ → ℂ, DifferentiableOn ℂ y gaussCutPlane →
      (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c y z = 0) →
      ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
        y z = v.1 * gaussFMinus H a b c z + v.2 * gaussFPlus H a b c z) := by
  have hFminusDiff := gaussFMinus_differentiableOn_cutPlane hH a b c hc
  have hFplusDiff := gaussFPlus_differentiableOn_cutPlane hH a b c hc
  have hFminusEq := gaussFMinus_holomorphicOperator_eq_zero hH a b c hc
  have hFplusEq := gaussFPlus_holomorphicOperator_eq_zero hH a b c hc
  have hW := gaussFPlus_wronskian_identity hH a b c hc
  refine ⟨hFminusDiff, hFplusDiff, ?_, ?_⟩
  · intro z hz
    exact ⟨hFminusEq z hz, hFplusEq z hz, hW z hz⟩
  · intro y hyDiff hyEq
    refine gauss_two_solution_span_unique a b c
      (gaussFMinus H a b c) (gaussFPlus H a b c)
      hFminusDiff hFplusDiff hFminusEq hFplusEq ?_ y hyDiff hyEq
    intro z hz
    have hzreg := gaussCutPlane_subset_regularPlane hz
    have hw0 : 1 - z ≠ 0 := by
      intro he
      apply hzreg.2
      exact (sub_eq_zero.mp he).symm
    have hpowz : z ^ (-c) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hzreg.1)
    have hpoww : (1 - z) ^ (c - a - b - 1) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
    have hcoeff : (1 - c) ≠ 0 := by
      intro he
      apply hc 1
      exact_mod_cast (sub_eq_zero.mp he).symm
    rw [hW z hz]
    exact mul_ne_zero (mul_ne_zero hcoeff hpowz) hpoww

/-- The one-end local basis, including its Wronskian and global spanning property. -/
theorem gauss_local_basis_one {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussGMinus H a b c) gaussCutPlane ∧
    DifferentiableOn ℂ (gaussGPlus H a b c) gaussCutPlane ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 ∧
      gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 ∧
      gaussGMinus H a b c z * deriv (gaussGPlus H a b c) z -
        deriv (gaussGMinus H a b c) z * gaussGPlus H a b c z =
          -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) ∧
    (∀ y : ℂ → ℂ, DifferentiableOn ℂ y gaussCutPlane →
      (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c y z = 0) →
      ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
        y z = v.1 * gaussGMinus H a b c z + v.2 * gaussGPlus H a b c z) := by
  have hGminusDiff := gaussGMinus_differentiableOn_cutPlane hH a b c hδ
  have hGplusDiff := gaussGPlus_differentiableOn_cutPlane hH a b c hδ
  have hGminusEq := gaussGMinus_holomorphicOperator_eq_zero hH a b c hδ
  have hGplusEq := gaussGPlus_holomorphicOperator_eq_zero hH a b c hδ
  have hW := gaussGPlus_wronskian_identity hH a b c hδ
  refine ⟨hGminusDiff, hGplusDiff, ?_, ?_⟩
  · intro z hz
    exact ⟨hGminusEq z hz, hGplusEq z hz, hW z hz⟩
  · intro y hyDiff hyEq
    refine gauss_two_solution_span_unique a b c
      (gaussGMinus H a b c) (gaussGPlus H a b c)
      hGminusDiff hGplusDiff hGminusEq hGplusEq ?_ y hyDiff hyEq
    intro z hz
    have hzreg := gaussCutPlane_subset_regularPlane hz
    have hw0 : 1 - z ≠ 0 := by
      intro he
      apply hzreg.2
      exact (sub_eq_zero.mp he).symm
    have hpowz : z ^ (-c) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hzreg.1)
    have hpoww : (1 - z) ^ (c - a - b - 1) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl hw0)
    have hcoeff : -(c - a - b) ≠ 0 := by
      intro he
      apply hδ 0
      exact_mod_cast (neg_eq_zero.mp he)
    rw [hW z hz]
    exact mul_ne_zero (mul_ne_zero hcoeff hpowz) hpoww

end DOZZ.Proofs
