/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionFormulaFromBox
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Real endpoint limits identify the connection Cramer coefficients. -/

@[expose] public section

open Filter Set
open scoped Topology

namespace DOZZ.Proofs

private theorem gaussSlitPlane_isOpen_for_endpointLimits : IsOpen gaussSlitPlane := by
  change IsOpen ({z : ℂ | z.im ≠ 0} ∪ {z : ℂ | z.re < 1})
  exact (isOpen_ne.preimage Complex.continuous_im).union
    (isOpen_Iio.preimage Complex.continuous_re)

/-- Every characterized family member tends to its normalized value `1` at the regular origin. -/
theorem gaussFamily_tendsto_one_at_zero
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℂ) (hc : ∀ n : ℕ, c ≠ -(n : ℂ)) :
    Tendsto (H a b c) (𝓝 0) (𝓝 1) := by
  have hchar := hH a b c hc
  have hzero : H a b c 0 = 1 := by
    simpa using hchar.2 0 (by norm_num)
  have hmem : (0 : ℂ) ∈ gaussSlitPlane := by simp [gaussSlitPlane]
  have hAt : DifferentiableAt ℂ (H a b c) 0 :=
    (hchar.1 0 hmem).differentiableAt
      (gaussSlitPlane_isOpen_for_endpointLimits.mem_nhds hmem)
  simpa [hzero] using hAt.continuousAt.tendsto

private theorem tendsto_one_sub_ofReal_cpow_zero (δ : ℂ) (hδ : 0 < δ.re) :
    Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ δ) (𝓝[Iio 1] 1) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hsub : Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) := by
    have hid : Tendsto (fun x : ℝ => x) F (𝓝 1) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1) := tendsto_const_nhds
    simpa using hconst.sub hid
  have hrpow : Tendsto (fun x : ℝ => (1 - x) ^ δ.re) F (𝓝 0) := by
    have hcont : ContinuousAt (fun p : ℝ × ℝ => p.1 ^ p.2) (0, δ.re) :=
      Real.continuousAt_rpow (0, δ.re) (Or.inr hδ)
    have hconst : Tendsto (fun _ : ℝ => δ.re) F (𝓝 δ.re) := tendsto_const_nhds
    have h := hcont.tendsto.comp (hsub.prodMk_nhds hconst)
    simpa [Function.comp_def, Real.zero_rpow hδ.ne'] using h
  have hnorm :
      (fun x : ℝ => ‖(1 - (x : ℂ)) ^ δ‖) =ᶠ[F]
        (fun x : ℝ => (1 - x) ^ δ.re) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < 1 - x := sub_pos.mpr hx
    have hbase : 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  rw [tendsto_congr' hnorm]
  exact hrpow

/-- If the zero-basis solution has a finite real-axis endpoint limit and `Re(c-a-b)>0`,
the first midpoint Cramer coefficient is exactly that limit. The basis limits are `G₋→1` and
`G₊→0`; the separate Euler integral supplies the endpoint value in applications. -/
theorem connectionMinusFirstCramer_eq_of_endpoint_limit
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L : ℂ} (hδ : 0 < (p.2.2 - p.1 - p.2.1).re)
    (hF : Tendsto (fun x : ℝ => gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionMinusFirstCramerCoefficient H p = L := by
  let δ : ℂ := p.2.2 - p.1 - p.2.1
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [hn]
        _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    exact hp.2 (n + 1) (by simpa [δ] using hδn)
  have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [hn]
        _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have hInt := hp.2 (-(n + 1 : ℤ))
    apply hInt
    simpa [δ] using hδn
  have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x) F (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1) := tendsto_const_nhds
      simpa using hconst.sub hid
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hsub
  have hGminus : Tendsto
      (fun x : ℝ => gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have hzero := gaussFamily_tendsto_one_at_zero hH p.1 p.2.1
      (1 + p.1 + p.2.1 - p.2.2) hcMinus
    simpa [gaussGMinus, F, Function.comp_def] using hzero.comp harg
  have hshift : Tendsto
      (fun x : ℝ => H (p.2.2 - p.2.1) (p.2.2 - p.1)
        (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) F (𝓝 1) := by
    exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg
  have hpower : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ δ) F (𝓝 0) :=
    tendsto_one_sub_ofReal_cpow_zero δ hδ
  have hGplus : Tendsto
      (fun x : ℝ => gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) := by
    simpa [gaussGPlus, δ, F] using hpower.mul hshift
  let C₁ := connectionMinusFirstCramerCoefficient H p
  let C₂ := connectionMinusSecondCramerCoefficient H p
  have hRHS : Tendsto
      (fun x : ℝ => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 C₁) := by
    simpa [C₁, C₂] using
      (tendsto_const_nhds.mul hGminus).add (tendsto_const_nhds.mul hGplus)
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    have hlt : ∀ᶠ x : ℝ in F, x < 1 := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1
      simpa only [mem_Iio] using
        (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
    have hpos : ∀ᶠ x : ℝ in F, 0 < x := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num))
    filter_upwards [hlt, hpos] with x hxlt hxpos
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hxpos, hxlt⟩
  have hEq : (fun x : ℝ => gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ)) =ᶠ[F]
      (fun x => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) := by
    filter_upwards [hcut] with x hx
    exact gaussFMinus_eq_connectionMidpointCramer hH hp (x : ℂ) hx
  have hRightLimit : Tendsto
      (fun x : ℝ => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 L) := by
    exact hF.congr' hEq
  have hFne : NeBot F := by
    dsimp [F]
    exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩
  exact tendsto_nhds_unique' hFne hRHS hRightLimit

/-- If the singularly rescaled zero-basis solution has a finite real-axis endpoint limit and
`Re(c-a-b)<0`, the second midpoint Cramer coefficient is that limit. The first one-basis term
vanishes after rescaling, while the powered second one-basis term tends to `1`. -/
theorem connectionMinusSecondCramer_eq_of_scaled_endpoint_limit
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L : ℂ} (hδ : 0 < (p.1 + p.2.1 - p.2.2).re)
    (hF : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-(p.2.2 - p.1 - p.2.1)) *
        gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionMinusSecondCramerCoefficient H p = L := by
  let δ : ℂ := p.2.2 - p.1 - p.2.1
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [hn]
        _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    exact hp.2 (n + 1) (by simpa [δ] using hδn)
  have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n hn
    have hcast : -((n + 1 : ℕ) : ℂ) = (-(n + 1 : ℤ) : ℂ) := by norm_cast
    have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
      dsimp [δ]
      calc
        p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [hn]
        _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have hInt := hp.2 (-(n + 1 : ℤ))
    apply hInt
    simpa [δ] using hδn
  have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x) F (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1) := tendsto_const_nhds
      simpa using hconst.sub hid
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hsub
  have hGminus : Tendsto
      (fun x : ℝ => gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have hzero := gaussFamily_tendsto_one_at_zero hH p.1 p.2.1
      (1 + p.1 + p.2.1 - p.2.2) hcMinus
    simpa [gaussGMinus, F, Function.comp_def] using hzero.comp harg
  have hshift : Tendsto
      (fun x : ℝ => H (p.2.2 - p.2.1) (p.2.2 - p.1)
        (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) F (𝓝 1) := by
    exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg
  have hpower : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ)) F (𝓝 0) := by
    apply tendsto_one_sub_ofReal_cpow_zero (-δ)
    have hreal : (-δ).re = p.1.re + p.2.1.re - p.2.2.re := by
      simp [δ]
      ring
    have hδ' : 0 < p.1.re + p.2.1.re - p.2.2.re := by
      simpa only [Complex.sub_re, Complex.add_re] using hδ
    rw [hreal]
    exact hδ'
  have hscaledMinus : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) := by
    simpa using hpower.mul hGminus
  have hscaledPlus : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have heq : (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) =ᶠ[F]
        (fun x => H (p.2.2 - p.2.1) (p.2.2 - p.1)
          (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) := by
      filter_upwards [eventually_mem_nhdsWithin] with x hx
      have hxlt : x < 1 := by simpa only [mem_Iio] using hx
      have hxbase : (1 : ℂ) - (x : ℂ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (ne_of_lt hxlt).symm
      change (1 - (x : ℂ)) ^ (-δ) *
        ((1 - (x : ℂ)) ^ δ * H (p.2.2 - p.2.1) (p.2.2 - p.1)
          (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) = _
      rw [← mul_assoc, ← Complex.cpow_add _ _ hxbase, neg_add_cancel,
        Complex.cpow_zero, one_mul]
    exact (hshift.congr' heq.symm)
  let C₁ := connectionMinusFirstCramerCoefficient H p
  let C₂ := connectionMinusSecondCramerCoefficient H p
  have hRHS : Tendsto
      (fun x : ℝ => C₁ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) +
        C₂ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) F (𝓝 C₂) := by
    simpa [C₁, C₂] using
      (tendsto_const_nhds.mul hscaledMinus).add
        (tendsto_const_nhds.mul hscaledPlus)
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    have hlt : ∀ᶠ x : ℝ in F, x < 1 := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1
      simpa only [mem_Iio] using
        (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
    have hpos : ∀ᶠ x : ℝ in F, 0 < x := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num))
    filter_upwards [hlt, hpos] with x hxlt hxpos
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hxpos, hxlt⟩
  have hEq : (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
      gaussFMinus H p.1 p.2.1 p.2.2 (x : ℂ)) =ᶠ[F]
      (fun x => C₁ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) +
        C₂ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) := by
    filter_upwards [hcut] with x hx
    have hexp := gaussFMinus_eq_connectionMidpointCramer hH hp (x : ℂ) hx
    rw [hexp]
    ring
  have hRightLimit : Tendsto
    (fun x : ℝ => C₁ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) +
        C₂ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) F (𝓝 L) := by
    simpa [C₁, C₂, δ] using hF.congr' hEq
  have hFne : NeBot F := by
    dsimp [F]
    exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩
  exact tendsto_nhds_unique' hFne hRHS hRightLimit

/-- Generic first-coefficient extraction from any cut-plane expansion in the one-end basis. -/
private theorem firstCramer_eq_of_endpoint_expansion
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L C₁ C₂ : ℂ} (δ : ℂ) (hδeq : δ = p.2.2 - p.1 - p.2.1)
    (hδ : 0 < δ.re) (f : ℂ → ℂ)
    (hF : Tendsto (fun x : ℝ => f (x : ℂ)) (𝓝[Iio 1] 1) (𝓝 L))
    (hExpansion : ∀ z ∈ gaussCutPlane,
      f z = C₁ * gaussGMinus H p.1 p.2.1 p.2.2 z +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 z) :
    C₁ = L := by
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
      rw [hδeq]
      calc
        p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [hn]
        _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    apply hp.2 (n + 1)
    calc
      p.2.2 - p.1 - p.2.1 = δ := hδeq.symm
      _ = ((n + 1 : ℕ) : ℂ) := hδn
  have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
      rw [hδeq]
      calc
        p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [hn]
        _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have hInt := hp.2 (-(n + 1 : ℤ))
    apply hInt
    simpa [hδeq] using hδn
  have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x) F (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1) := tendsto_const_nhds
      simpa using hconst.sub hid
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hsub
  have hGminus : Tendsto
      (fun x : ℝ => gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have hzero := gaussFamily_tendsto_one_at_zero hH p.1 p.2.1
      (1 + p.1 + p.2.1 - p.2.2) hcMinus
    simpa [gaussGMinus, F, Function.comp_def] using hzero.comp harg
  have hshift : Tendsto
      (fun x : ℝ => H (p.2.2 - p.2.1) (p.2.2 - p.1)
        (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) F (𝓝 1) := by
    exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg
  have hpower : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ δ) F (𝓝 0) :=
    tendsto_one_sub_ofReal_cpow_zero δ hδ
  have hGplus : Tendsto
      (fun x : ℝ => gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) := by
    simpa [gaussGPlus, hδeq, F] using hpower.mul hshift
  have hRHS : Tendsto
      (fun x : ℝ => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 C₁) := by
    simpa using (tendsto_const_nhds.mul hGminus).add
      (tendsto_const_nhds.mul hGplus)
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    have hlt : ∀ᶠ x : ℝ in F, x < 1 := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1
      simpa only [mem_Iio] using
        (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
    have hpos : ∀ᶠ x : ℝ in F, 0 < x := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num))
    filter_upwards [hlt, hpos] with x hxlt hxpos
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hxpos, hxlt⟩
  have hEq : (fun x : ℝ => f (x : ℂ)) =ᶠ[F]
      (fun x => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) := by
    filter_upwards [hcut] with x hx
    exact hExpansion (x : ℂ) hx
  have hRight : Tendsto
      (fun x : ℝ => C₁ * gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ) +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 L) := hF.congr' hEq
  have hFne : NeBot F := by
    dsimp [F]
    exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩
  exact tendsto_nhds_unique' hFne hRHS hRight

/-- Generic second-coefficient extraction from a rescaled cut-plane expansion in the one-end
basis. -/
private theorem secondCramer_eq_of_scaled_endpoint_expansion
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L C₁ C₂ : ℂ} (δ : ℂ) (hδeq : δ = p.2.2 - p.1 - p.2.1)
    (hδ : 0 < (-δ).re) (f : ℂ → ℂ)
    (hF : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) * f (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L))
    (hExpansion : ∀ z ∈ gaussCutPlane,
      f z = C₁ * gaussGMinus H p.1 p.2.1 p.2.2 z +
        C₂ * gaussGPlus H p.1 p.2.1 p.2.2 z) :
    C₂ = L := by
  let F : Filter ℝ := 𝓝[Iio 1] 1
  have hcMinus : ∀ n : ℕ, (1 + p.1 + p.2.1 - p.2.2) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = ((n + 1 : ℕ) : ℂ) := by
      rw [hδeq]
      calc
        p.2.2 - p.1 - p.2.1 = 1 - (1 + p.1 + p.2.1 - p.2.2) := by ring
        _ = 1 - (-(n : ℂ)) := by rw [hn]
        _ = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    apply hp.2 (n + 1)
    calc
      p.2.2 - p.1 - p.2.1 = δ := hδeq.symm
      _ = ((n + 1 : ℕ) : ℂ) := hδn
  have hcPlus : ∀ n : ℕ, (1 + p.2.2 - p.1 - p.2.1) ≠ -(n : ℂ) := by
    intro n hn
    have hδn : δ = -((n + 1 : ℕ) : ℂ) := by
      rw [hδeq]
      calc
        p.2.2 - p.1 - p.2.1 = (1 + p.2.2 - p.1 - p.2.1) - 1 := by ring
        _ = -(n : ℂ) - 1 := by rw [hn]
        _ = -((n + 1 : ℕ) : ℂ) := by push_cast; ring
    have hInt := hp.2 (-(n + 1 : ℤ))
    apply hInt
    simpa [hδeq] using hδn
  have harg : Tendsto (fun x : ℝ => (1 - (x : ℂ))) F (𝓝 0) := by
    have hsub : Tendsto (fun x : ℝ => 1 - x) F (𝓝 0) := by
      have hid : Tendsto (fun x : ℝ => x) F (𝓝 1) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) F (𝓝 1) := tendsto_const_nhds
      simpa using hconst.sub hid
    simpa [Function.comp_def] using Complex.continuous_ofReal.continuousAt.tendsto.comp hsub
  have hGminus : Tendsto
      (fun x : ℝ => gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have hzero := gaussFamily_tendsto_one_at_zero hH p.1 p.2.1
      (1 + p.1 + p.2.1 - p.2.2) hcMinus
    simpa [gaussGMinus, F, Function.comp_def] using hzero.comp harg
  have hshift : Tendsto
      (fun x : ℝ => H (p.2.2 - p.2.1) (p.2.2 - p.1)
        (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) F (𝓝 1) := by
    exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcPlus).comp harg
  have hpower : Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ)) F (𝓝 0) := by
    exact tendsto_one_sub_ofReal_cpow_zero (-δ) hδ
  have hscaledMinus : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 0) := by
    simpa using hpower.mul hGminus
  have hscaledPlus : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) F (𝓝 1) := by
    have heq : (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) *
        gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ)) =ᶠ[F]
        (fun x => H (p.2.2 - p.2.1) (p.2.2 - p.1)
          (1 + p.2.2 - p.1 - p.2.1) (1 - (x : ℂ))) := by
      filter_upwards [eventually_mem_nhdsWithin] with x hx
      have hxlt : x < 1 := by simpa only [mem_Iio] using hx
      have hxbase : (1 : ℂ) - (x : ℂ) ≠ 0 := by
        apply sub_ne_zero.mpr
        exact_mod_cast (ne_of_lt hxlt).symm
      simp only [gaussGPlus]
      rw [← hδeq]
      rw [← mul_assoc, ← Complex.cpow_add _ _ hxbase, neg_add_cancel,
        Complex.cpow_zero, one_mul]
    exact hshift.congr' heq.symm
  have hRHS : Tendsto
      (fun x : ℝ => C₁ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) +
        C₂ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) F (𝓝 C₂) := by
    simpa using (tendsto_const_nhds.mul hscaledMinus).add
      (tendsto_const_nhds.mul hscaledPlus)
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    have hlt : ∀ᶠ x : ℝ in F, x < 1 := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x < 1
      simpa only [mem_Iio] using
        (eventually_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, x ∈ Iio 1)
    have hpos : ∀ᶠ x : ℝ in F, 0 < x := by
      change ∀ᶠ x : ℝ in 𝓝[Iio (1 : ℝ)] 1, 0 < x
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_gt_nhds (show (0 : ℝ) < 1 from by norm_num))
    filter_upwards [hlt, hpos] with x hxlt hxpos
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hxpos, hxlt⟩
  have hEq : (fun x : ℝ => (1 - (x : ℂ)) ^ (-δ) * f (x : ℂ)) =ᶠ[F]
      (fun x => C₁ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) +
        C₂ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) := by
    filter_upwards [hcut] with x hx
    rw [hExpansion (x : ℂ) hx]
    ring
  have hRight : Tendsto
      (fun x : ℝ => C₁ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGMinus H p.1 p.2.1 p.2.2 (x : ℂ)) +
        C₂ * ((1 - (x : ℂ)) ^ (-δ) *
          gaussGPlus H p.1 p.2.1 p.2.2 (x : ℂ))) F (𝓝 L) := hF.congr' hEq
  have hFne : NeBot F := by
    dsimp [F]
    exact (isLUB_Iio : IsLUB (Iio (1 : ℝ)) 1).nhdsWithin_neBot ⟨0, by norm_num⟩
  exact tendsto_nhds_unique' hFne hRHS hRight

/-- The same endpoint extraction applies to the second zero-basis solution `F₊`; its midpoint
Cramer coefficients are thus identified by the corresponding (possibly rescaled) Euler limits. -/
theorem connectionPlusFirstCramer_eq_of_endpoint_limit
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L : ℂ} (hδ : 0 < (p.2.2 - p.1 - p.2.1).re)
    (hF : Tendsto (fun x : ℝ => gaussFPlus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionPlusFirstCramerCoefficient H p = L := by
  have hExpansion := gaussFPlus_eq_connectionMidpointCramer hH hp
  exact firstCramer_eq_of_endpoint_expansion hH hp
    (δ := p.2.2 - p.1 - p.2.1) rfl hδ (gaussFPlus H p.1 p.2.1 p.2.2)
    hF hExpansion

/-- The rescaled endpoint extraction also identifies the second Cramer coefficient of `F₊`. -/
theorem connectionPlusSecondCramer_eq_of_scaled_endpoint_limit
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    {p : ℂ × ℂ × ℂ} (hp : p ∈ gaussConnectionParameterDomain)
    {L : ℂ} (hδ : 0 < (p.1 + p.2.1 - p.2.2).re)
    (hF : Tendsto
      (fun x : ℝ => (1 - (x : ℂ)) ^ (-(p.2.2 - p.1 - p.2.1)) *
        gaussFPlus H p.1 p.2.1 p.2.2 (x : ℂ))
      (𝓝[Iio 1] 1) (𝓝 L)) :
    connectionPlusSecondCramerCoefficient H p = L := by
  have hExpansion := gaussFPlus_eq_connectionMidpointCramer hH hp
  have hδ' : 0 < (-(p.2.2 - p.1 - p.2.1)).re := by
    have hreal : (-(p.2.2 - p.1 - p.2.1)).re =
        (p.1 + p.2.1 - p.2.2).re := by simp [Complex.sub_re]; ring
    rw [hreal]
    exact hδ
  exact secondCramer_eq_of_scaled_endpoint_expansion hH hp
    (δ := p.2.2 - p.1 - p.2.1) rfl hδ' (gaussFPlus H p.1 p.2.1 p.2.2)
    hF hExpansion

end DOZZ.Proofs
