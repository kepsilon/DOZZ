/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.BasisEquationTransforms
public import DOZZ.Hypergeom.Germs

/-! Abel's identity and the endpoint normalization of the zero-basis Wronskian. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter

private theorem gaussSlitPlane_isOpen_for_wronskians : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

private theorem gaussCutPlane_isOpen_for_wronskians : IsOpen gaussCutPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z | 0 < z.re ∧ z.re < 1})
  exact (isOpen_compl_singleton.preimage Complex.continuous_im).union
    (isOpen_Ioo.preimage Complex.continuous_re)

/-- The zero-basis Wronskian has its explicit value on the principal cut plane. -/
theorem gaussFPlus_wronskian_identity
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℤ, c ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H a b c z * deriv (gaussFPlus H a b c) z -
        deriv (gaussFMinus H a b c) z * gaussFPlus H a b c z =
          (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  let A : ℂ := a - c + 1
  let B : ℂ := b - c + 1
  let C : ℂ := 2 - c
  let e : ℂ := a + b - c + 1
  let f : ℂ → ℂ := H a b c
  let v : ℂ → ℂ := H A B C
  let p : ℂ → ℂ := fun z => z ^ (1 - c)
  let q : ℂ → ℂ := fun z => (1 - z) ^ e
  let g : ℂ → ℂ := gaussFPlus H a b c
  let W : ℂ → ℂ := fun z => f z * deriv g z - deriv f z * g z
  let T : ℂ → ℂ := fun z => z ^ c * q z
  let S : ℂ → ℂ := fun z => T z * W z
  have hcNat : ∀ n : ℕ, c ≠ -(n : ℂ) := by
    intro n heq
    apply hc (-(n : ℤ))
    exact heq.trans (by simp)
  have hCfree : ∀ n : ℕ, C ≠ -(n : ℂ) := by
    simpa [C] using two_sub_parameter_ne_nat_neg hc
  have hfchar := hH a b c hcNat
  have hvchar := hH A B C hCfree
  have hFanalyticSlit : AnalyticOnNhd ℂ f gaussSlitPlane :=
    hfchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_wronskians
  have hVanalyticSlit : AnalyticOnNhd ℂ v gaussSlitPlane :=
    hvchar.1.analyticOnNhd gaussSlitPlane_isOpen_for_wronskians
  have hFanalytic : AnalyticOnNhd ℂ f gaussCutPlane := by
    exact hFanalyticSlit.mono gaussCutPlane_subset_gaussSlitPlane
  have hVanalytic : AnalyticOnNhd ℂ v gaussCutPlane := by
    exact hVanalyticSlit.mono gaussCutPlane_subset_gaussSlitPlane
  have hPanalytic : AnalyticOnNhd ℂ p gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z : ℂ => z ^ (1 - c)) gaussCutPlane
    exact analyticOnNhd_id.cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have hGanalytic : AnalyticOnNhd ℂ g gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => p z * v z) gaussCutPlane
    exact hPanalytic.mul hVanalytic
  have hQanalytic : AnalyticOnNhd ℂ q gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => (1 - z) ^ e) gaussCutPlane
    exact (analyticOnNhd_const.sub analyticOnNhd_id).cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane
        (one_sub_gaussCutPlane_subset_gaussCutPlane hz))
  have hZanalytic : AnalyticOnNhd ℂ (fun z : ℂ => z ^ c) gaussCutPlane := by
    exact analyticOnNhd_id.cpow analyticOnNhd_const
      (fun z hz => gaussCutPlane_subset_Complex_slitPlane hz)
  have hTanalytic : AnalyticOnNhd ℂ T gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => z ^ c * q z) gaussCutPlane
    exact hZanalytic.mul hQanalytic
  have hFanalytic₁ : AnalyticOnNhd ℂ (deriv f) gaussCutPlane := hFanalytic.deriv
  have hVanalytic₁ : AnalyticOnNhd ℂ (deriv v) gaussCutPlane := hVanalytic.deriv
  have hGanalytic₁ : AnalyticOnNhd ℂ (deriv g) gaussCutPlane := hGanalytic.deriv
  have hWanalytic : AnalyticOnNhd ℂ W gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => f z * deriv g z - deriv f z * g z) gaussCutPlane
    exact (hFanalytic.mul hGanalytic₁).sub (hFanalytic₁.mul hGanalytic)
  have hSanalytic : AnalyticOnNhd ℂ S gaussCutPlane := by
    change AnalyticOnNhd ℂ (fun z => T z * W z) gaussCutPlane
    exact hTanalytic.mul hWanalytic
  have hPderiv : gaussCutPlane.EqOn (deriv p)
      (fun z => (1 - c) * z ^ (-c)) := by
    intro z hz
    simpa [p] using (Complex.deriv_cpow_const (c := 1 - c)
      (gaussCutPlane_subset_Complex_slitPlane hz))
  have hQderiv : gaussCutPlane.EqOn (deriv q)
      (fun z => -e * (1 - z) ^ (e - 1)) := by
    intro z hz
    have hw : 1 - z ∈ gaussCutPlane := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hws := gaussCutPlane_subset_Complex_slitPlane hw
    have hmap : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
    have hpow := Complex.deriv_cpow_const (c := e) hws
    have hcomp := (differentiableAt_id.cpow_const (c := e) hws).hasDerivAt.comp z hmap
    change deriv (fun w => (1 - w) ^ e) z = -e * (1 - z) ^ (e - 1)
    simpa [Function.comp_def, hpow, mul_comm] using hcomp.deriv
  have hGderiv : gaussCutPlane.EqOn (deriv g)
      (fun z => (1 - c) * z ^ (-c) * v z + p z * deriv v z) := by
    intro z hz
    have hPAt := (hPanalytic z hz).differentiableAt
    have hVAt := (hVanalytic z hz).differentiableAt
    have hmul := hPAt.hasDerivAt.mul hVAt.hasDerivAt
    change deriv (p * v) z = (1 - c) * z ^ (-c) * v z + p z * deriv v z
    rw [hmul.deriv, hPderiv hz]
  have hWderiv : ∀ z ∈ gaussCutPlane,
      deriv W z = f z * deriv (deriv g) z - deriv (deriv f) z * g z := by
    intro z hz
    have hleft := (hFanalytic z hz).differentiableAt.hasDerivAt.mul
      (hGanalytic₁ z hz).differentiableAt.hasDerivAt
    have hright := (hFanalytic₁ z hz).differentiableAt.hasDerivAt.mul
      (hGanalytic z hz).differentiableAt.hasDerivAt
    have hsub := hleft.sub hright
    change deriv (fun w => f w * deriv g w - deriv f w * g w) z = _
    have hfun : (fun w => f w * deriv g w - deriv f w * g w) =
        f * deriv g - deriv f * g := by
      funext w
      rfl
    rw [hfun]
    rw [hsub.deriv]
    ring
  have hTderiv : ∀ z ∈ gaussCutPlane,
      deriv T z = c * z ^ (c - 1) * q z - e * z ^ c * (1 - z) ^ (e - 1) := by
    intro z hz
    have hZAt := (hZanalytic z hz).differentiableAt
    have hQAt := (hQanalytic z hz).differentiableAt
    have hmul := hZAt.hasDerivAt.mul hQAt.hasDerivAt
    have hZderiv : deriv (fun w : ℂ => w ^ c) z = c * z ^ (c - 1) :=
      Complex.deriv_cpow_const (gaussCutPlane_subset_Complex_slitPlane hz)
    change deriv (fun w => w ^ c * q w) z = _
    have hfun : (fun w => w ^ c * q w) = (fun w => w ^ c) * q := by
      funext w
      rfl
    rw [hfun]
    rw [hmul.deriv, hZderiv, hQderiv hz]
    ring
  have hFop : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c f z = 0 := by
    simpa [f] using gauss_family_holomorphicOperator_eq_zero hH a b c hcNat
  have hGop : ∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c g z = 0 := by
    simpa [g] using gaussFPlus_holomorphicOperator_eq_zero hH a b c hc
  have hAbel : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv W z + (c - (a + b + 1) * z) * W z = 0 := by
    intro z hz
    rw [hWderiv z hz]
    dsimp [W]
    have hFeq := hFop z hz
    have hGeq := hGop z hz
    dsimp [gaussHolomorphicOperator] at hFeq hGeq
    linear_combination (f z) * hGeq - (g z) * hFeq
  have hTscaled : ∀ z ∈ gaussCutPlane,
      z * (1 - z) * deriv T z = (c - (a + b + 1) * z) * T z := by
    intro z hz
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hz1 := (gaussCutPlane_subset_regularPlane hz).2
    have hw0 : 1 - z ≠ 0 := by
      intro h
      apply hz1
      exact (sub_eq_zero.mp h).symm
    have hpowz : z ^ (c - 1) = z ^ c / z := by
      simpa using Complex.cpow_sub c 1 hz0
    have hpoww : (1 - z) ^ (e - 1) = (1 - z) ^ e / (1 - z) := by
      simpa using Complex.cpow_sub e 1 hw0
    rw [hTderiv z hz, hpowz, hpoww]
    field_simp [hz0, hw0]
    dsimp [T, q, e]
    ring
  have hSderivZero : gaussCutPlane.EqOn (deriv S) (fun _ => 0) := by
    intro z hz
    have hTAt := (hTanalytic z hz).differentiableAt
    have hWAt := (hWanalytic z hz).differentiableAt
    have hmul := hTAt.hasDerivAt.mul hWAt.hasDerivAt
    have hSderiv : deriv S z = deriv T z * W z + T z * deriv W z := by
      change deriv (T * W) z = _
      exact hmul.deriv
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hz1 := (gaussCutPlane_subset_regularPlane hz).2
    have hw0 : 1 - z ≠ 0 := by
      intro h
      apply hz1
      exact (sub_eq_zero.mp h).symm
    have hden : z * (1 - z) ≠ 0 := mul_ne_zero hz0 hw0
    have hWscaled : z * (1 - z) * deriv W z =
        -(c - (a + b + 1) * z) * W z := by
      calc
        z * (1 - z) * deriv W z =
            -((c - (a + b + 1) * z) * W z) := eq_neg_of_add_eq_zero_left (hAbel z hz)
        _ = -(c - (a + b + 1) * z) * W z := by ring
    have hmulzero : z * (1 - z) * deriv S z = 0 := by
      rw [hSderiv]
      calc
        z * (1 - z) * (deriv T z * W z + T z * deriv W z) =
            (z * (1 - z) * deriv T z) * W z +
              T z * (z * (1 - z) * deriv W z) := by ring
        _ = (c - (a + b + 1) * z) * T z * W z -
              T z * ((c - (a + b + 1) * z) * W z) := by
            rw [hTscaled z hz, hWscaled]
            ring
        _ = 0 := by ring
    exact (mul_eq_zero.mp hmulzero).resolve_left hden
  have hSdiff : DifferentiableOn ℂ S gaussCutPlane := hSanalytic.differentiableOn
  have hcutPre : IsPreconnected gaussCutPlane := by
    rw [isPreconnected_iff_preconnectedSpace]
    infer_instance
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hconst : ∀ z ∈ gaussCutPlane, S z = S (1 / 2) := by
    intro z hz
    exact gaussCutPlane_isOpen.is_const_of_deriv_eq_zero
      hcutPre hSdiff hSderivZero hz hmid
  have hfzero : f 0 = 1 := by
    simpa [f] using (hfchar.2 0 (by norm_num : ‖(0 : ℂ)‖ < 1))
  have hvzero : v 0 = 1 := by
    simpa [v] using (hvchar.2 0 (by norm_num : ‖(0 : ℂ)‖ < 1))
  have h0slit : (0 : ℂ) ∈ gaussSlitPlane := by
    change (0 : ℂ).im ≠ 0 ∨ (0 : ℂ).re < 1
    simp
  have hfcont : ContinuousAt f 0 := (hFanalyticSlit 0 h0slit).continuousAt
  have hvcont : ContinuousAt v 0 := (hVanalyticSlit 0 h0slit).continuousAt
  have hf'cont : ContinuousAt (deriv f) 0 :=
    (hFanalyticSlit.deriv 0 h0slit).continuousAt
  have hv'cont : ContinuousAt (deriv v) 0 :=
    (hVanalyticSlit.deriv 0 h0slit).continuousAt
  have hqcont : ContinuousAt q 0 := by
    change ContinuousAt (fun z : ℂ => (1 - z) ^ e) 0
    exact (by fun_prop : ContinuousAt (fun z : ℂ => 1 - z) 0).cpow
      continuousAt_const (by simp [Complex.mem_slitPlane_iff])
  have hRcont : ContinuousAt
      (fun z => q z * ((1 - c) * f z * v z +
        z * (f z * deriv v z - deriv f z * v z))) 0 := by
    fun_prop
  have hRzero : (fun z => q z * ((1 - c) * f z * v z +
      z * (f z * deriv v z - deriv f z * v z))) 0 = 1 - c := by
    simp [q, hfzero, hvzero]
  have hRlim : Tendsto
      (fun z => q z * ((1 - c) * f z * v z +
        z * (f z * deriv v z - deriv f z * v z)))
      (nhdsWithin 0 gaussCutPlane) (nhds (1 - c)) := by
    have h := hRcont.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin 0 gaussCutPlane ≤ nhds 0)
    have hRval : q 0 * ((1 - c) * f 0 * v 0 +
        0 * (f 0 * deriv v 0 - deriv f 0 * v 0)) = 1 - c := by
      simpa using hRzero
    rw [hRval] at h
    exact h
  have hscaled : ∀ z ∈ gaussCutPlane,
      S z = q z * ((1 - c) * f z * v z +
        z * (f z * deriv v z - deriv f z * v z)) := by
    intro z hz
    have hz0 := (gaussCutPlane_subset_regularPlane hz).1
    have hGderivAt : deriv g z =
        (1 - c) * z ^ (-c) * v z + p z * deriv v z := by
      simpa using hGderiv hz
    have hpow₀ : z ^ c * z ^ (-c) = 1 := by
      rw [← Complex.cpow_add c (-c) hz0]
      simp
    have hpow₁ : z ^ c * z ^ (1 - c) = z := by
      rw [← Complex.cpow_add c (1 - c) hz0]
      have hexp : c + (1 - c) = 1 := by ring
      rw [hexp]
      simp
    have hgval : g z = z ^ (1 - c) * v z := by
      rfl
    have hpval : p z = z ^ (1 - c) := by
      rfl
    change z ^ c * q z * (f z * deriv g z - deriv f z * g z) = _
    rw [hGderivAt, hgval, hpval]
    calc
      _ = q z * ((1 - c) * (z ^ c * z ^ (-c)) * f z * v z +
          (z ^ c * z ^ (1 - c)) *
            (f z * deriv v z - deriv f z * v z)) := by ring
      _ = q z * ((1 - c) * f z * v z +
          z * (f z * deriv v z - deriv f z * v z)) := by
        rw [hpow₀, hpow₁]
        ring
  have hlimS : Tendsto S (nhdsWithin 0 gaussCutPlane) (nhds (1 - c)) := by
    have hEq : S =ᶠ[nhdsWithin 0 gaussCutPlane]
        (fun z => q z * ((1 - c) * f z * v z +
          z * (f z * deriv v z - deriv f z * v z))) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hscaled z hz
    exact hRlim.congr' hEq.symm
  have hSvalue : S (1 / 2) = 1 - c := by
    have hzeroClosure : (0 : ℂ) ∈ closure gaussCutPlane := by
      apply Metric.mem_closure_iff.2
      intro ε hε
      let r : ℝ := min ε 1 / 2
      have hrpos : 0 < r := by
        dsimp [r]
        positivity
      have hrε : r < ε := by
        dsimp [r]
        have hmin : min ε 1 ≤ ε := min_le_left _ _
        linarith
      have hrone : r < 1 := by
        dsimp [r]
        have hmin : min ε 1 ≤ 1 := min_le_right _ _
        linarith
      refine ⟨(r : ℂ), ?_, ?_⟩
      · change (r : ℂ).im ≠ 0 ∨ (0 < (r : ℂ).re ∧ (r : ℂ).re < 1)
        simp [hrpos, hrone]
      · simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_pos hrpos] using hrε
    have hconstlim : Tendsto (fun _ : ℂ => S (1 / 2))
        (nhdsWithin 0 gaussCutPlane) (nhds (1 - c)) := by
      have hEq : S =ᶠ[nhdsWithin 0 gaussCutPlane] (fun _ => S (1 / 2)) := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact hconst z hz
      exact hlimS.congr' hEq
    have hconstant : Tendsto (fun _ : ℂ => S (1 / 2))
        (nhdsWithin 0 gaussCutPlane) (nhds (S (1 / 2))) := tendsto_const_nhds
    exact (tendsto_nhds_unique'
      (mem_closure_iff_nhdsWithin_neBot.mp hzeroClosure) hconstlim hconstant).symm
  intro z hz
  have hz0 := (gaussCutPlane_subset_regularPlane hz).1
  have hz1 := (gaussCutPlane_subset_regularPlane hz).2
  have hw0 : 1 - z ≠ 0 := by
    intro h
    apply hz1
    exact (sub_eq_zero.mp h).symm
  have hSval := hconst z hz
  rw [hSvalue] at hSval
  have hpowe : -(e) = c - a - b - 1 := by dsimp [e]; ring
  have hcpowz : (z ^ c)⁻¹ = z ^ (-c) := by rw [Complex.cpow_neg]
  have hcpoww : (q z)⁻¹ = (1 - z) ^ (c - a - b - 1) := by
    dsimp [q]
    rw [← hpowe, Complex.cpow_neg]
  dsimp [S, T, W, q, f, g] at hSval ⊢
  have hzPowNe : z ^ c ≠ 0 :=
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hz0))
  have hwPowNe : (1 - z) ^ e ≠ 0 :=
    (Complex.cpow_ne_zero_iff.mpr (Or.inl hw0))
  have hprod : z ^ c * (1 - z) ^ e ≠ 0 := mul_ne_zero hzPowNe hwPowNe
  have hratio : W z = (1 - c) / (z ^ c * (1 - z) ^ e) := by
    apply (eq_div_iff hprod).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hSval
  calc
    W z = (1 - c) / (z ^ c * (1 - z) ^ e) := hratio
    _ = (1 - c) * (z ^ c)⁻¹ * ((1 - z) ^ e)⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]
      ring
    _ = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
      rw [hcpowz, hcpoww]

/-- The one-basis Wronskian follows from the zero-basis identity by reflection. -/
theorem gaussGPlus_wronskian_identity
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussGMinus H a b c z * deriv (gaussGPlus H a b c) z -
        deriv (gaussGMinus H a b c) z * gaussGPlus H a b c z =
          -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  let c₀ : ℂ := 1 + a + b - c
  let F : ℂ → ℂ := gaussFMinus H a b c₀
  let G : ℂ → ℂ := gaussFPlus H a b c₀
  let f : ℂ → ℂ := gaussGMinus H a b c
  let g : ℂ → ℂ := gaussGPlus H a b c
  have hc₀ : ∀ n : ℤ, c₀ ≠ (n : ℂ) := by
    intro n heq
    apply hδ (1 - n)
    have hshift : c - a - b = (1 - n : ℤ) := by
      calc
        c - a - b = 1 - c₀ := by dsimp [c₀]; ring
        _ = 1 - (n : ℂ) := by rw [heq]
        _ = ((1 - n : ℤ) : ℂ) := by push_cast; ring
    exact hshift
  have hFdiff : DifferentiableOn ℂ F gaussCutPlane := by
    simpa [F] using gaussFMinus_differentiableOn_cutPlane hH a b c₀ hc₀
  have hGdiff : DifferentiableOn ℂ G gaussCutPlane := by
    simpa [G] using gaussFPlus_differentiableOn_cutPlane hH a b c₀ hc₀
  have hFident : f = (fun z => F (1 - z)) := by
    funext z
    rfl
  have hGident : g = (fun z => G (1 - z)) := by
    funext z
    change (1 - z) ^ (c - a - b) *
        H (c - b) (c - a) (1 + c - a - b) (1 - z) =
      (1 - z) ^ (1 - c₀) *
        H (a - c₀ + 1) (b - c₀ + 1) (2 - c₀) (1 - z)
    have hexp : c - a - b = 1 - c₀ := by dsimp [c₀]; ring
    have ha : c - b = a - c₀ + 1 := by dsimp [c₀]; ring
    have hb : c - a = b - c₀ + 1 := by dsimp [c₀]; ring
    have hc' : 1 + c - a - b = 2 - c₀ := by dsimp [c₀]; ring
    rw [hexp, ha, hb, hc']
  have hmap (z : ℂ) : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hFderiv : gaussCutPlane.EqOn (deriv f)
      (fun z => -deriv F (1 - z)) := by
    intro z hz
    have hw : 1 - z ∈ gaussCutPlane := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hAt := (hFdiff (1 - z) hw).differentiableAt
      (gaussCutPlane_isOpen_for_wronskians.mem_nhds hw)
    have hcomp := hAt.hasDerivAt.comp z (hmap z)
    calc
      deriv f z = deriv (fun w => F (1 - w)) z := by rw [hFident]
      _ = -deriv F (1 - z) := by
        simpa [Function.comp_def, mul_comm] using hcomp.deriv
  have hGderiv : gaussCutPlane.EqOn (deriv g)
      (fun z => -deriv G (1 - z)) := by
    intro z hz
    have hw : 1 - z ∈ gaussCutPlane := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hAt := (hGdiff (1 - z) hw).differentiableAt
      (gaussCutPlane_isOpen_for_wronskians.mem_nhds hw)
    have hcomp := hAt.hasDerivAt.comp z (hmap z)
    calc
      deriv g z = deriv (fun w => G (1 - w)) z := by rw [hGident]
      _ = -deriv G (1 - z) := by
        simpa [Function.comp_def, mul_comm] using hcomp.deriv
  intro z hz
  let w : ℂ := 1 - z
  have hw : w ∈ gaussCutPlane := by
    simpa [w] using one_sub_gaussCutPlane_subset_gaussCutPlane hz
  have hW := gaussFPlus_wronskian_identity hH a b c₀ hc₀ w hw
  have hW' : F w * deriv G w - deriv F w * G w =
      (1 - c₀) * w ^ (-c₀) * (1 - w) ^ (c₀ - a - b - 1) := by
    simpa [F, G] using hW
  have hfval : f z = F w := by simp [f, F, w, c₀, gaussGMinus, gaussFMinus]
  have hgval : g z = G w := by
    rw [hGident]
  have hcoeff : 1 - c₀ = c - a - b := by dsimp [c₀]; ring
  have hexpz : c₀ - a - b - 1 = -c := by dsimp [c₀]; ring
  have hexpw : -c₀ = c - a - b - 1 := by dsimp [c₀]; ring
  calc
    f z * deriv g z - deriv f z * g z =
        F w * (-deriv G w) - (-deriv F w) * G w := by
          rw [hfval, hgval, hGderiv hz, hFderiv hz]
    _ = -(F w * deriv G w - deriv F w * G w) := by ring
    _ = -(1 - c₀) * w ^ (-c₀) * (1 - w) ^ (c₀ - a - b - 1) := by
      rw [hW']
      ring
    _ = -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
      rw [hcoeff, hexpw, hexpz]
      dsimp [w]
      have hbase : 1 - (1 - z : ℂ) = z := by ring
      rw [hbase]
      ring

end DOZZ.Proofs
