/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.UnreflectedB
public import DOZZ.FourPoint.BPZ.BPZAssemblyA
public import DOZZ.FourPoint.BPZ.ExplicitProfile
public import DOZZ.FourPoint.BPZ.TaylorSingular
public import DOZZ.FourPoint.BPZ.RootedHessian
public import DOZZ.FourPoint.BPZ.RootedRemainder
public import DOZZ.FourPoint.Fusion.OneRootedTaylor
public import DOZZ.FourPoint.GammaHalfTwoRootedTaylorIsLittleO
public import DOZZ.FourPoint.Fusion.Coefficient

/-! # The shift relation for `2 < γ² < 4`

By the diagonal formula, on `(0, 1)` the reduced function is the explicit profile
`T(u) = C₋ (φ(u) + ρ u^κ ψ(u))` with `φ, ψ` smooth near `0`, `φ(0) = ψ(0) = 1` and `1 < κ < 2`.
Its second derivative is, by the regularity of the negative moment, the expectation of the second
moment field, which is the integrand of the one- and two-rooted Taylor terms. The Taylor formula
with a singular endpoint therefore identifies the sum of these terms at `t ∈ (0, 1/4]` with
`T(t)/K - C₋/K - C₋ φ'(0) t/K = (C₋/K)(φ(t) - 1 - φ'(0) t) + (C₋/K) ρ t^κ ψ(t)`. Comparing with
the asymptotics of the rooted terms (`-p A t^κ + o(t^κ)`) gives `ρ C₋ = -K p A`, which is the
shift relation by the identification of the rooted coefficient. -/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

/-- Structure constants only depend on the almost sure class of the measure. -/
theorem bpz_structureConstant_congr {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {M N : Ω → Measure ℂ} (hMN : ∀ᵐ ω ∂P, M ω = N ω) (γ μ α₁ α₂ α₃ : ℝ) :
    structureConstant P M γ μ α₁ α₂ α₃ = structureConstant P N γ μ α₁ α₂ α₃ := by
  unfold structureConstant
  have h : (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P) =
      ∫⁻ ω, rho γ (N ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P :=
    lintegral_congr_ae (hMN.mono fun ω h => by dsimp only; rw [h])
  rw [h]

/-- A complex little-o at zero along the positive reals. -/
theorem bpz_littleO_along_reals {κ : ℝ} {f : ℂ → ℂ} (hf : IsComplexLittleOAtZero κ f) :
    Tendsto (fun t : ℝ => f (t : ℂ) / ((t ^ κ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 0) := by
  have hof : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[>] 0) (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 ((0 : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.tendsto 0
      rw [Complex.ofReal_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact Complex.ofReal_ne_zero.mpr ht.ne'
  have h := hf.comp hof
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
  simp only [Function.comp, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le κ)]

/-- **The shift relation for `2 < γ² < 4`**, for a measurable GMC measure. -/
theorem bpz_shift_large_gamma_meas {Ω : Type*} [MeasurableSpace Ω] {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hMm : Measurable M)
    (hdiag : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
        (‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃) (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
          gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
            ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2)) :
    gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
        (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ =
        -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
          structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ := by
  have hQ : Q γ = 2 / γ + γ / 2 := rfl
  -- exponents
  set p : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ with hp_def
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hsp : fourPointSExp γ (-(γ / 2)) α₁ α₂ α₃ = p := by
    unfold fourPointSExp
    rw [hp_def]
    ring
  set κ : ℝ := γ * (Q γ - α₁) with hκ
  have hκe : κ = 2 + γ ^ 2 / 2 - γ * α₁ := by rw [hκ, hQ]; field_simp
  have hκ1 : 1 < κ := by
    have h1 : γ * α₁ < γ * (2 / γ) := mul_lt_mul_of_pos_left hαhi hγ
    have h2 : γ * (2 / γ) = 2 := by field_simp
    rw [hκe]
    linarith only [h1, h2, hγsq]
  have hκ2 : κ < 2 := by
    have h1 : γ * (γ / 2) < γ * α₁ := mul_lt_mul_of_pos_left hαlo hγ
    rw [hκe]
    linarith only [h1]
  -- the explicit profile
  set a' := gaussParameterA γ (γ / 2) α₁ α₂ α₃ with ha'
  set b' := gaussParameterB γ (γ / 2) α₁ α₂ α₃ with hb'
  set c' := gaussParameterC γ (γ / 2) α₁ with hc'
  set ρ := gaussCoefficientRatio a' b' c' with hρ
  set Cm := structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ with hCm
  obtain ⟨hc0, hc1⟩ := bpz_gaussParameterC_half_mem hγ hαlo hαhi
  have h2c : 2 * (1 - c') = κ := bpz_gaussParameterC_half γ α₁
  set φ : ℝ → ℝ := fun u => Complex.normSq (H (a' : ℂ) (b' : ℂ) (c' : ℂ) (u : ℂ)) with hφ
  set ψ : ℝ → ℝ := fun u => Complex.normSq (H ((a' : ℂ) - c' + 1) ((b' : ℂ) - c' + 1)
    (2 - (c' : ℂ)) (u : ℂ)) with hψ
  have hcφ : ∀ n : ℕ, (c' : ℂ) ≠ -(n : ℂ) := bpz_ne_neg_nat_of_pos hc0
  have hcψ : ∀ n : ℕ, (2 - (c' : ℂ)) ≠ -(n : ℂ) := by
    have h := bpz_ne_neg_nat_of_pos (c := 2 - c') (by linarith only [hc1])
    intro n; push_cast at h; exact h n
  have hφd : ContDiffOn ℝ 2 φ (Ioo (-1) 1) := bpzHG_contDiffOn_normSq hH hcφ
  have hψd : ContDiffOn ℝ 2 ψ (Ioo (-1) 1) := bpzHG_contDiffOn_normSq hH hcψ
  have hφ0 : φ 0 = 1 := by
    simp only [hφ, Complex.ofReal_zero, bpzHG_eq_one_at_zero hH hcφ, map_one]
  have hψ0 : ψ 0 = 1 := by
    simp only [hψ, Complex.ofReal_zero, bpzHG_eq_one_at_zero hH hcψ, map_one]
  -- the normalization
  set K : ℝ := 2 * μ ^ (-p) / γ * Real.Gamma p with hK
  have hKpos : 0 < K := by
    have := Real.Gamma_pos_of_pos hp
    positivity
  set A₀ : ℝ := Cm / K with hA₀
  -- the negative moment and its derivatives
  have hχ : (0 : ℝ) < γ / 2 := by positivity
  have hγ4 : γ ^ 2 < 4 := by
    have h := mul_self_lt_mul_self hγ.le hγ2
    rw [← sq] at h
    linarith only [h]
  have ha1 : γ * (γ / 2) / 2 ≤ 1 := by linarith only [hγ4]
  have hα₁Q : α₁ < Q γ := by
    rw [hQ]
    have : 0 < γ / 2 := hχ
    linarith only [hαhi, this]
  obtain ⟨hd1, hd2⟩ := bpz_hasFDerivAt_moments P X hX hγ hγ2 M hM hMm hχ ha1 hα₁Q hα₂ hα₃ hp
  set F0 : ℂ → ℝ := fun z => ∫ ω, bpzSoftMassReal (γ * (γ / 2) / 2) 0
    (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) z ^ (-p) ∂P with hF0
  set F1 : ℂ → ℂ →L[ℝ] ℝ := fun z => ∫ ω, bpzMomField1 (γ * (γ / 2) / 2) p 0
    (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) z ∂P with hF1
  set F2 : ℂ → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun z => ∫ ω, bpzMomField2 (γ * (γ / 2) / 2) p 0
    (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (bpzBaseWeight γ (γ / 2) α₁ α₂ α₃) (M ω) z ∂P with hF2
  have hreg : ∀ u : ℝ, 0 < u → u < 1 → (u : ℂ) ∈ {z : ℂ | z ≠ 0 ∧ z ≠ 1} := by
    intro u hu0 hu1
    refine ⟨Complex.ofReal_ne_zero.mpr hu0.ne', fun h => ?_⟩
    have : u = 1 := by exact_mod_cast h
    linarith only [this, hu1]
  -- (f1) the moment is the explicit profile on `(0, 1)`
  have hf1 : ∀ u : ℝ, 0 < u → u < 1 → F0 u = A₀ * (φ u + ρ * (u ^ κ * ψ u)) := by
    intro u hu0 hu1
    have hz : (u : ℂ) ∈ gaussCutPlane := by
      show (u : ℂ).im ≠ 0 ∨ (0 < (u : ℂ).re ∧ (u : ℂ).re < 1)
      right
      simp only [Complex.ofReal_re]
      exact ⟨hu0, hu1⟩
    have h1 := bpz_fourPointT_eq_moment P X hX hγ hγ2 M hM hMm hχ hα₁Q hα₂ hα₃ μ
      (hreg u hu0 hu1).1 (hreg u hu0 hu1).2
    rw [hsp] at h1
    have h2 := hdiag (u : ℂ) hz
    rw [h1, bpzHG_norm_sq_eq_normSq, bpzHG_norm_sq_eq_normSq, bpzHG_normSq_gaussFMinus,
      bpzHG_normSq_gaussFPlus H a' b' c' hu0, h2c] at h2
    have e : K * F0 u = Cm * (φ u + ρ * (u ^ κ * ψ u)) := h2
    rw [hA₀, div_mul_eq_mul_div, eq_div_iff hKpos.ne', ← e]
    ring
  -- (f2) derivatives of the moment along the reals
  have hf2 : ∀ u : ℝ, 0 < u → u < 1 →
      HasDerivAt (fun v : ℝ => F0 v) (F1 u 1) u ∧
        HasDerivAt (fun v : ℝ => F1 v 1) (F2 u 1 1) u := by
    intro u hu0 hu1
    have hof : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u := by
      simpa using (hasDerivAt_id u).ofReal_comp
    constructor
    · exact (hd1 u (hreg u hu0 hu1)).comp_hasDerivAt u hof
    · have hc := (hd2 u (hreg u hu0 hu1)).clm_apply (hasFDerivAt_const (1 : ℂ) (u : ℂ))
      have h := hc.comp_hasDerivAt u hof
      simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at h
      exact h
  -- (f3) the derivatives are the explicit ones
  have hf3 : ∀ u : ℝ, 0 < u → u < 1 →
      F2 u 1 1 = A₀ * (deriv (deriv φ) u + ρ * (κ * (κ - 1) * u ^ (κ - 2) * ψ u +
        2 * (κ * u ^ (κ - 1) * deriv ψ u) + u ^ κ * deriv (deriv ψ) u)) := by
    intro u hu0 hu1
    have hev : (fun v : ℝ => F0 v) =ᶠ[𝓝 u] fun v => A₀ * (φ v + ρ * (v ^ κ * ψ v)) := by
      filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv using hf1 v hv.1 hv.2
    have hD1 : ∀ v : ℝ, 0 < v → v < 1 → F1 v 1 =
        A₀ * (deriv φ v + ρ * (κ * v ^ (κ - 1) * ψ v + v ^ κ * deriv ψ v)) := by
      intro v hv0 hv1
      have hev' : (fun v : ℝ => F0 v) =ᶠ[𝓝 v] fun v => A₀ * (φ v + ρ * (v ^ κ * ψ v)) := by
        filter_upwards [Ioo_mem_nhds hv0 hv1] with w hw using hf1 w hw.1 hw.2
      exact ((hf2 v hv0 hv1).1.congr_of_eventuallyEq hev'.symm).unique
        (bpzEP_hasDerivAt_profile hφd hψd A₀ ρ κ hv0 hv1)
    have hev1 : (fun v : ℝ => F1 v 1) =ᶠ[𝓝 u]
        fun v => A₀ * (deriv φ v + ρ * (κ * v ^ (κ - 1) * ψ v + v ^ κ * deriv ψ v)) := by
      filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv using hD1 v hv.1 hv.2
    have _ := hev
    exact ((hf2 u hu0 hu1).2.congr_of_eventuallyEq hev1.symm).unique
      (bpzEP_hasDerivAt_profile' hφd hψd A₀ ρ κ hu0 hu1)
  -- the asymptotics of the rooted terms
  obtain ⟨r₁, hr₁, hr₁o⟩ := DOZZ.Proofs.gammaHalf_oneRooted_Taylor_asymptotic P X M γ α₁ α₂ α₃
    hγ hγ4 hαlo hγsq hαhi hα₂ hα₃ hs hX hM
  have hr₂o := DOZZ.Proofs.gammaHalf_twoRooted_Taylor_is_littleO P X M γ α₁ α₂ α₃ hγ hγ2 hγsq
    hαlo hαhi hα₂ hα₃ hs hX hM
  set A : ℝ := gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p with hA
  -- (f4)–(f6): the identity along `(0, 1/4]`, in real parts
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      A₀ * ρ * ψ t = -(p * A) +
        ((r₁ t).re + (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p t).re) / t ^ κ -
          A₀ * ((φ t - φ 0 - deriv φ 0 * t) / t ^ κ) := by
    intro t ht0 ht
    have ht1 : t < 1 := by linarith only [ht]
    -- Taylor for the explicit profile
    have hT := bpz_taylor_singular (g := fun v => A₀ * (φ v + ρ * (v ^ κ * ψ v)))
      (g' := fun v => A₀ * (deriv φ v + ρ * (κ * v ^ (κ - 1) * ψ v + v ^ κ * deriv ψ v)))
      (g'' := fun v => A₀ * (deriv (deriv φ) v + ρ * (κ * (κ - 1) * v ^ (κ - 2) * ψ v +
        2 * (κ * v ^ (κ - 1) * deriv ψ v) + v ^ κ * deriv (deriv ψ) v)))
      ht0 (fun u hu => bpzEP_hasDerivAt_profile hφd hψd A₀ ρ κ hu.1 (by linarith only [hu.2, ht1]))
      (fun u hu => bpzEP_hasDerivAt_profile' hφd hψd A₀ ρ κ hu.1 (by linarith only [hu.2, ht1]))
      (bpzEP_tendsto_profile hφd hψd A₀ ρ (by linarith only [hκ1]))
      (bpzEP_tendsto_profile' hφd hψd A₀ ρ hκ1)
      (bpzEP_integrableOn_profile'' hφd hψd A₀ ρ hκ1 ht0 ht1)
    -- the rooted terms are the Taylor remainder
    have hR := bpz_rootedTerms_eq_integral P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hαlo hγsq hαhi hα₂ hα₃
      hp.le ht0 ht (g2 := fun v => A₀ * (deriv (deriv φ) v + ρ * (κ * (κ - 1) * v ^ (κ - 2) *
        ψ v + 2 * (κ * v ^ (κ - 1) * deriv ψ v) + v ^ κ * deriv (deriv ψ) v)))
      (fun u hu0 hu => by
        rw [← hf3 u hu0 (by linarith only [hu, ht1])]
        exact bpz_momField2_one_one_eq P X hX γ hγ hγ2 M hM hMm α₁ α₂ α₃ hα₁Q hα₂ hα₃ hp.le
          (hreg u hu0 (by linarith only [hu, ht1])).1 (hreg u hu0 (by linarith only [hu, ht1])).2)
    -- real parts
    have hRre := congrArg Complex.re hR
    simp only [Complex.add_re, Complex.ofReal_re] at hRre
    rw [hr₁ (t : ℂ)] at hRre
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, mul_zero, sub_zero, zero_mul,
      add_zero, neg_zero, Complex.norm_real, Real.norm_of_nonneg ht0.le, ← hκ, ← hp_def]
      at hRre
    have hT' := hT
    rw [hφ0] at hT'
    have e1 : -(p * A) * t ^ κ + (r₁ t).re + (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p t).re =
        A₀ * (φ t + ρ * (t ^ κ * ψ t)) - (A₀ * 1 + A₀ * deriv φ 0 * t) := by
      linarith only [hT', hRre]
    have htk : 0 < t ^ κ := Real.rpow_pos_of_pos ht0 κ
    have hR12 : (r₁ t).re + (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p t).re =
        A₀ * (φ t - 1 - deriv φ 0 * t) + (A₀ * ρ * ψ t + p * A) * t ^ κ := by
      linear_combination e1
    rw [hφ0, hR12, add_div, mul_div_cancel_right₀ _ htk.ne', mul_div_assoc]
    ring
  -- limits
  have hlimL : Tendsto (fun t : ℝ => A₀ * ρ * ψ t) (𝓝[>] 0) (𝓝 (A₀ * ρ)) := by
    have hmem : Ioo (-1 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    have hψc : Tendsto ψ (𝓝[>] 0) (𝓝 1) := by
      rw [← hψ0]
      exact ((bpzEP_continuousOn hψd).1.continuousAt hmem).tendsto.mono_left nhdsWithin_le_nhds
    simpa using hψc.const_mul (A₀ * ρ)
  have hre : ∀ {f : ℂ → ℂ}, IsComplexLittleOAtZero κ f →
      Tendsto (fun t : ℝ => (f t).re / t ^ κ) (𝓝[>] 0) (𝓝 0) := by
    intro f hf
    have h := (Complex.continuous_re.tendsto 0).comp (bpz_littleO_along_reals hf)
    simpa [Function.comp_def, Complex.div_ofReal_re] using h
  have hlimR : Tendsto (fun t : ℝ => -(p * A) +
      ((r₁ t).re + (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p t).re) / t ^ κ -
        A₀ * ((φ t - φ 0 - deriv φ 0 * t) / t ^ κ)) (𝓝[>] 0) (𝓝 (-(p * A) + 0 - A₀ * 0)) := by
    have hsum : Tendsto (fun t : ℝ => ((r₁ t).re + (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p
        t).re) / t ^ κ) (𝓝[>] 0) (𝓝 0) := by
      simpa [add_div] using (hre hr₁o).add (hre hr₂o)
    exact (tendsto_const_nhds.add hsum).sub ((bpzEP_tendsto_taylor hφd hκ2).const_mul A₀)
  have hev : (fun t : ℝ => A₀ * ρ * ψ t) =ᶠ[𝓝[>] 0] fun t : ℝ => -(p * A) +
      ((r₁ t).re + (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃ p t).re) / t ^ κ -
        A₀ * ((φ t - φ 0 - deriv φ 0 * t) / t ^ κ) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with t ht
    exact key t ht.1 ht.2
  have hlim := tendsto_nhds_unique (hlimL.congr' hev) hlimR
  rw [add_zero, mul_zero, sub_zero] at hlim
  have hA₀ρ : A₀ * ρ = -(p * A) := hlim
  -- (f7) the rooted coefficient
  have hcoef := fusion_normalized_rootedCoefficient P X hX γ hγ hγ2 M hM μ α₁ α₂ α₃ hμ hs
  have e1 : ρ * Cm = K * (A₀ * ρ) := by
    rw [hA₀]
    field_simp
  rw [e1, hA₀ρ]
  have e2 : K * -(p * A) = (2 * μ ^ (-p) / γ * Real.Gamma p) * (-p * A) := by
    rw [hK]; ring
  rw [e2]
  exact hcoef

/-- **The shift relation for `2 < γ² < 4`.** -/
theorem bpz_shift_large_gamma {Ω : Type*} [MeasurableSpace Ω] {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ)
    (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hdiag : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
        (‖gaussFMinus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃) (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
            (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2 +
          gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
            ‖gaussFPlus H (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
              (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) z‖ ^ 2)) :
    gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
        (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁) *
          structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ =
        -μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re *
          structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ := by
  obtain ⟨N, hNm, hNfin, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hN : IsGMCOf P X γ N := bpz_isGMCOf_congr hM hNfin hMN
  rw [bpz_structureConstant_congr P hMN, bpz_structureConstant_congr P hMN]
  refine bpz_shift_large_gamma_meas hH P X N γ μ α₁ α₂ α₃ hγ hγ2 hγsq hμ hαlo hαhi hα₂ hα₃ hs hX
    hN hNm fun z hz => ?_
  rw [← bpz_fourPointT_congr P hMN, ← bpz_structureConstant_congr P hMN]
  exact hdiag z hz

end DOZZ.Proofs
