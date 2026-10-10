/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.DualL
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.ShiftEquations.DualR.SegFactors
import DOZZ.ShiftEquations.Residual.Calibration
import DOZZ.ShiftEquations.Rbar.Continuation
import DOZZ.ShiftEquations.Shift.Reflection
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic

/-!
# The limits in the proof of the `2/γ` shift equation

As `η → 0⁺` along the crossed second dual seed ([KRV, §10.5]):

* `η C(a, b + η, c) → 2` when `a + b + c = 2Q` (the zero mode: `C = μ^{-s} Γ(s) C̄` with
  `s = η/γ` and `C̄ = 2/γ` at total charge `2Q`);
* `η R(γ/2 + η) → 2μπ R(γ)/(γ l(-γ²/4) l(γ²/4))`, from the first reflection shift
  (`DOZZ.reflectionR_first_shift_meromorphic`): the pole of `R` at `γ/2` comes from the zero of
  `l(2 - γη/2)`;
* `L(γ/2 - θ, γ/2 + η, 2/γ + θ)/η → -(1/γ) l(2(ε - Q)/γ) l(1 + 4/γ²)/l(1 - 2θ/γ)`, since
  `L` has the factor `1/l(-η/γ)`.

Also: a function meromorphic at a real point whose real restriction is continuous there is analytic
there.
-/

@[expose] public section

open MeasureTheory Filter Topology Set

namespace DOZZ.Proofs

/-- **Meromorphic and continuous along the reals implies analytic.** -/
theorem analyticAt_of_meromorphicAt_of_tendsto_ofReal {f : ℂ → ℂ} {x₀ : ℝ}
    (hf : MeromorphicAt f (x₀ : ℂ))
    (h : Tendsto (fun x : ℝ => f (x : ℂ)) (𝓝[≠] x₀) (𝓝 (f x₀))) : AnalyticAt ℂ f (x₀ : ℂ) := by
  have hreal := tendsto_ofReal_nhdsNE_slice x₀
  have hord : 0 ≤ meromorphicOrderAt f (x₀ : ℂ) := by
    by_contra hneg
    have hcob := (tendsto_cobounded_of_meromorphicOrderAt_neg (not_le.mp hneg)).comp hreal
    exact not_tendsto_atTop_of_tendsto_nhds h.norm (tendsto_norm_atTop_iff_cobounded.mpr hcob)
  obtain ⟨g, hg, hfg⟩ := hf.meromorphicOrderAt_nonneg_iff.mp hord
  have hfg' : ∀ᶠ x : ℝ in 𝓝[≠] x₀, f x = g x := hreal.eventually hfg
  have hglim : Tendsto (fun x : ℝ => g (x : ℂ)) (𝓝[≠] x₀) (𝓝 (g x₀)) :=
    ((hg.continuousAt.tendsto.comp Complex.continuous_ofReal.continuousAt.tendsto).mono_left
      nhdsWithin_le_nhds)
  have heq : f x₀ = g x₀ := tendsto_nhds_unique (h.congr' hfg') hglim
  exact hg.congr (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hfg.symm heq.symm)

/-- **The zero-mode limit**: `η C(a, b + η, c) → 2` when `a + b + c = 2Q` and all charges are
below `Q`. -/
theorem tendsto_mul_structureConstant_chargeZero {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (M : Ω → Measure ℂ) {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) {a b c : ℝ} (hsum : a + b + c = 2 * Q γ)
    (ha : a < Q γ) (hb : b < Q γ) (hc : c < Q γ) :
    Tendsto (fun η : ℝ => η * structureConstant P M γ μ a (b + η) c) (𝓝[>] 0) (𝓝 2) := by
  have : IsProbabilityMeasure P := hX.1
  obtain ⟨V₃, hV₃, hV₃mem, f₃, hf₃, hf₃eq⟩ :=
    unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM
  have h4 : 0 < 4 / γ := by positivity
  have hES0 : ExtendedSeiberg3 γ a b c :=
    extendedSeiberg3_of_lt hγ ha hb hc (by linarith) (by linarith) (by linarith) (by linarith)
  have hs : ∀ η : ℝ, sExp γ a (b + η) c = η / γ := fun η => by
    unfold sExp
    rw [show a + (b + η) + c - 2 * Q γ = η by linarith]
  -- continuity of the unit-volume structure constant along the curve
  have hγ0 : sExp γ a b c = 0 := by
    have := hs 0
    rwa [add_zero, zero_div] at this
  have hval : unitVolumeStructureConstant P M γ a b c = 2 / γ :=
    unitVolumeStructureConstant_zeroMode P M hγ0
  have hcurve : Continuous fun η : ℝ => complexifyNCharges ![a, b + η, c] := by
    unfold complexifyNCharges
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  have hmem0 : complexifyNCharges ![a, b + 0, c] ∈ V₃ := by
    rw [add_zero]
    exact hV₃mem ![a, b, c] hES0
  have hfc : ContinuousAt (fun η : ℝ => f₃ (complexifyNCharges ![a, b + η, c])) 0 :=
    ContinuousAt.comp (f := fun η : ℝ => complexifyNCharges ![a, b + η, c]) (x := 0)
      ((hf₃.differentiableAt (hV₃.mem_nhds hmem0)).continuousAt) hcurve.continuousAt
  have hES : ∀ᶠ η in 𝓝 (0 : ℝ), ExtendedSeiberg3 γ a (b + η) c :=
    eventually_extendedSeiberg3 (f₁ := fun _ => a) (f₂ := fun η => b + η) (f₃ := fun _ => c)
      continuousAt_const (by fun_prop) continuousAt_const (by simpa using hES0)
  have hCbar : Tendsto (fun η : ℝ => unitVolumeStructureConstant P M γ a (b + η) c) (𝓝 0)
      (𝓝 (2 / γ)) := by
    have h1 : Tendsto (fun η : ℝ => (f₃ (complexifyNCharges ![a, b + η, c])).re) (𝓝 0)
        (𝓝 ((f₃ (complexifyNCharges ![a, b + 0, c])).re)) :=
      (Complex.continuous_re.continuousAt.tendsto).comp hfc
    rw [add_zero, hf₃eq ![a, b, c] hES0] at h1
    simp only [Complex.ofReal_re] at h1
    rw [← hval]
    refine h1.congr' ?_
    filter_upwards [hES] with η hη
    rw [hf₃eq ![a, b + η, c] hη, Complex.ofReal_re]
    rfl
  -- the Gamma and power factors
  have hΓ : Tendsto (fun η : ℝ => Real.Gamma (η / γ + 1)) (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt Real.Gamma 1 :=
      (Real.differentiableAt_Gamma (fun m => by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        intro h
        linarith)).continuousAt
    have h := hc.tendsto.comp (show Tendsto (fun η : ℝ => η / γ + 1) (𝓝 0) (𝓝 1) by
      have : Continuous fun η : ℝ => η / γ + 1 := by fun_prop
      simpa using this.tendsto 0)
    rwa [Real.Gamma_one] at h
  have hpow : Tendsto (fun η : ℝ => μ ^ (-(η / γ))) (𝓝 0) (𝓝 1) := by
    have : Continuous fun η : ℝ => μ ^ (-(η / γ)) :=
      continuous_const.rpow (by fun_prop) fun _ => Or.inl hμ.ne'
    simpa using this.tendsto 0
  have hlim : Tendsto (fun η : ℝ => γ * Real.Gamma (η / γ + 1) * μ ^ (-(η / γ)) *
      unitVolumeStructureConstant P M γ a (b + η) c) (𝓝 0) (𝓝 (γ * 1 * 1 * (2 / γ))) :=
    ((tendsto_const_nhds.mul hΓ).mul hpow).mul hCbar
  rw [show γ * 1 * 1 * (2 / γ) = 2 by field_simp] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  rw [structureConstant_eq_mul_unitVolume, hs, Real.Gamma_add_one (div_ne_zero hη.ne' hγ.ne')]
  field_simp

/-- `Γ(2) = 1`. -/
theorem complex_Gamma_two : Complex.Gamma 2 = 1 := by
  have h := Complex.Gamma_nat_eq_factorial 1
  simp at h
  rw [show (2 : ℂ) = 1 + 1 by norm_num]
  exact h

/-- **The pole of `R` at `γ/2`**, from the first reflection shift
(`DOZZ.reflectionR_first_shift_meromorphic`): `η R(γ/2 + η) → 2μπ R(γ)/(γ l(-γ²/4) l(γ²/4))`. -/
theorem tendsto_mul_reflection_pole {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℂ → ℂ}
    (hRγ : AnalyticAt ℂ R (γ : ℂ))
    (hshift : ∀ᶠ z in codiscrete ℂ,
      R (z - γ / 2) = -(μ * Real.pi : ℂ) * R z /
        (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))) :
    Tendsto (fun η : ℝ => (η : ℂ) * R ((γ / 2 + η : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (2 * (μ * Real.pi : ℂ) * R γ /
        ((γ : ℂ) * (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4))))) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  -- the shift at `z = γ + η`
  have hev : ∀ᶠ η : ℝ in 𝓝[≠] 0, R (((γ + η : ℝ) : ℂ) - γ / 2) = -(μ * Real.pi : ℂ) *
      R ((γ + η : ℝ) : ℂ) / (lFun (-((γ : ℂ) ^ 2) / 4) *
        lFun ((γ : ℂ) * ((γ + η : ℝ) : ℂ) / 2 - (γ : ℂ) ^ 2 / 4) *
          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * ((γ + η : ℝ) : ℂ) / 2)) := by
    have ht : Tendsto (fun η : ℝ => ((γ + η : ℝ) : ℂ)) (𝓝[≠] 0) (𝓝[≠] (γ : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous fun η : ℝ => ((γ + η : ℝ) : ℂ) := by fun_prop
        have h0 := hc.tendsto 0
        simp only [add_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      · refine eventually_nhdsWithin_of_forall fun η (hη : η ≠ 0) => ?_
        simp only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj]
        intro h
        apply hη
        linarith
    exact ht.eventually ((eventually_codiscrete_iff_forall_eventually_nhdsNE.mp hshift) γ)
  -- the factor `η / l(2 - γη/2)`
  have hlim₁ : Tendsto (fun η : ℝ => (η : ℂ) * (lFun (2 - (γ : ℂ) * η / 2))⁻¹) (𝓝[>] 0)
      (𝓝 (-(2 / (γ : ℂ)))) := by
    have hG1 : ContinuousAt Complex.Gamma 1 := by
      have h := (analyticAt_Gamma_ofReal_pos (by norm_num : (0 : ℝ) < 1)).continuousAt
      rwa [Complex.ofReal_one] at h
    have hG2 : ContinuousAt Complex.Gamma 2 := by
      have h := (analyticAt_Gamma_ofReal_pos (by norm_num : (0 : ℝ) < 2)).continuousAt
      rwa [Complex.ofReal_ofNat] at h
    have hA : Tendsto (fun η : ℝ => Complex.Gamma ((γ : ℂ) * η / 2 + 1)) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun η : ℝ => (γ : ℂ) * η / 2 + 1 := by fun_prop
      have h0 := hc.tendsto 0
      simp only [Complex.ofReal_zero, mul_zero, zero_div, zero_add] at h0
      have h := hG1.tendsto.comp h0
      rwa [Complex.Gamma_one] at h
    have hB : Tendsto (fun η : ℝ => Complex.Gamma (2 - (γ : ℂ) * η / 2)) (𝓝 0) (𝓝 1) := by
      have hc : Continuous fun η : ℝ => (2 : ℂ) - (γ : ℂ) * η / 2 := by fun_prop
      have h0 := hc.tendsto 0
      simp only [Complex.ofReal_zero, mul_zero, zero_div, sub_zero] at h0
      have h := hG2.tendsto.comp h0
      rwa [complex_Gamma_two] at h
    have hC : Tendsto (fun η : ℝ => (γ : ℂ) * η / 2 - 1) (𝓝 0) (𝓝 (-1)) := by
      have hc : Continuous fun η : ℝ => (γ : ℂ) * η / 2 - 1 := by fun_prop
      simpa using hc.tendsto 0
    have hlim : Tendsto (fun η : ℝ => 2 / (γ : ℂ) * Complex.Gamma ((γ : ℂ) * η / 2 + 1) /
        (((γ : ℂ) * η / 2 - 1) * Complex.Gamma (2 - (γ : ℂ) * η / 2))) (𝓝 0)
        (𝓝 (2 / (γ : ℂ) * 1 / ((-1) * 1))) :=
      (tendsto_const_nhds.mul hA).div (hC.mul hB) (by norm_num)
    rw [show 2 / (γ : ℂ) * 1 / ((-1) * 1) = -(2 / (γ : ℂ)) by ring] at hlim
    refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      (Ioo_mem_nhdsGT (show (0 : ℝ) < 2 / γ by positivity))] with η (hη : 0 < η) hη2
    set v : ℂ := (γ : ℂ) * η / 2 with hv
    have hv0 : v ≠ 0 := by
      rw [hv]
      exact div_ne_zero (mul_ne_zero hγc (Complex.ofReal_ne_zero.mpr hη.ne')) two_ne_zero
    have hv1 : v - 1 ≠ 0 := by
      intro h
      have hre : (γ * η / 2 : ℝ) = 1 := by
        have : v = 1 := sub_eq_zero.mp h
        rw [hv] at this
        exact_mod_cast this
      have : γ * η / 2 < 1 := by
        have h2 := hη2.2
        rw [lt_div_iff₀ hγ] at h2
        linarith
      linarith
    -- `Γ(v + 1) = v (v - 1) Γ(v - 1)`
    have hrec : Complex.Gamma (v + 1) = v * ((v - 1) * Complex.Gamma (v - 1)) := by
      rw [Complex.Gamma_add_one v hv0, show v = (v - 1) + 1 by ring, Complex.Gamma_add_one _ hv1]
      ring_nf
    have hl : (lFun (2 - v))⁻¹ = Complex.Gamma (v - 1) / Complex.Gamma (2 - v) := by
      unfold lFun
      rw [inv_div, show 1 - (2 - v) = v - 1 by ring]
    rw [hl]
    have hG : Complex.Gamma (v - 1) = Complex.Gamma (v + 1) / (v * (v - 1)) := by
      rw [hrec]
      field_simp
    rw [hG]
    have hη' : (η : ℂ) = 2 / (γ : ℂ) * v := by
      rw [hv]
      field_simp
    rw [hη']
    field_simp
  -- the remaining factors
  have hR : Tendsto (fun η : ℝ => R ((γ + η : ℝ) : ℂ)) (𝓝 0) (𝓝 (R γ)) := by
    have hc : Continuous fun η : ℝ => ((γ + η : ℝ) : ℂ) := by fun_prop
    have h0 := hc.tendsto 0
    simp only [add_zero] at h0
    exact hRγ.continuousAt.tendsto.comp h0
  have hL : Tendsto (fun η : ℝ => (lFun ((γ : ℂ) ^ 2 / 4 + (γ : ℂ) * η / 2))⁻¹) (𝓝 0)
      (𝓝 (lFun ((γ : ℂ) ^ 2 / 4))⁻¹) := by
    have ha : AnalyticAt ℂ (fun s : ℂ => (lFun ((γ : ℂ) ^ 2 / 4 + (γ : ℂ) * s / 2))⁻¹) 0 := by
      refine analyticAt_inv_lFun_comp (f := fun s : ℂ => (γ : ℂ) ^ 2 / 4 + (γ : ℂ) * s / 2)
        (by fun_prop) ?_
      have h := analyticAt_Gamma_ofReal_pos (show (0 : ℝ) < 1 - γ ^ 2 / 4 by nlinarith)
      convert h using 1
      push_cast
      ring
    have h0 := Complex.continuous_ofReal.tendsto (0 : ℝ)
    rw [Complex.ofReal_zero] at h0
    have h := ha.continuousAt.tendsto.comp h0
    simp only [mul_zero, zero_div, add_zero] at h
    exact h
  have hmain : Tendsto (fun η : ℝ => -(μ * Real.pi : ℂ) * R ((γ + η : ℝ) : ℂ) *
      ((η : ℂ) * (lFun (2 - (γ : ℂ) * η / 2))⁻¹) * (lFun (-((γ : ℂ) ^ 2) / 4))⁻¹ *
        (lFun ((γ : ℂ) ^ 2 / 4 + (γ : ℂ) * η / 2))⁻¹) (𝓝[>] 0)
      (𝓝 (-(μ * Real.pi : ℂ) * R γ * (-(2 / (γ : ℂ))) * (lFun (-((γ : ℂ) ^ 2) / 4))⁻¹ *
        (lFun ((γ : ℂ) ^ 2 / 4))⁻¹)) :=
    ((((tendsto_const_nhds.mul (hR.mono_left nhdsWithin_le_nhds)).mul hlim₁).mul
      tendsto_const_nhds).mul (hL.mono_left nhdsWithin_le_nhds))
  rw [show -(μ * Real.pi : ℂ) * R γ * (-(2 / (γ : ℂ))) * (lFun (-((γ : ℂ) ^ 2) / 4))⁻¹ *
      (lFun ((γ : ℂ) ^ 2 / 4))⁻¹ = 2 * (μ * Real.pi : ℂ) * R γ /
        ((γ : ℂ) * (lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4))) by
    simp only [div_eq_mul_inv, mul_inv]
    ring] at hmain
  refine hmain.congr' ?_
  filter_upwards [nhdsWithin_mono _ (fun x (hx : (0 : ℝ) < x) => hx.ne') hev] with η hη
  rw [show ((γ / 2 + η : ℝ) : ℂ) = ((γ + η : ℝ) : ℂ) - γ / 2 by push_cast; ring, hη,
    show (γ : ℂ) * ((γ + η : ℝ) : ℂ) / 2 - (γ : ℂ) ^ 2 / 4 = (γ : ℂ) ^ 2 / 4 + (γ : ℂ) * η / 2 by
      push_cast; ring,
    show 2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * ((γ + η : ℝ) : ℂ) / 2 = 2 - (γ : ℂ) * η / 2 by
      push_cast; ring]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **The zero of the dual crossing coefficient at `α = γ/2`**:
`L(γ/2 - θ, γ/2 + η, 2/γ + θ)/η → -(1/γ) l(2(ε - Q)/γ) l(1 + 4/γ²)/l(1 - 2θ/γ)`. -/
theorem tendsto_dualLC_div {γ θ : ℝ} (hγ : 0 < γ) (hθ₁ : 0 < θ) :
    Tendsto (fun η : ℝ =>
        dualLC γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) / η) (𝓝[>] 0)
      (𝓝 (-(1 / (γ : ℂ)) * lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) * lFun (1 + 4 / (γ : ℂ) ^ 2) *
        (lFun (1 - 2 * θ / γ))⁻¹)) := by
  have hγc : (γ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hγ.ne'
  have hG1 : ContinuousAt Complex.Gamma 1 := by
    have h := (analyticAt_Gamma_ofReal_pos (by norm_num : (0 : ℝ) < 1)).continuousAt
    rwa [Complex.ofReal_one] at h
  -- the factors as functions of `η`
  have hA₂ : Tendsto (fun η : ℝ => lFun (1 + 4 / (γ : ℂ) ^ 2 - 2 * η / γ)) (𝓝 0)
      (𝓝 (lFun (1 + 4 / (γ : ℂ) ^ 2))) := by
    have ha : AnalyticAt ℂ (fun s : ℂ => lFun (1 + 4 / (γ : ℂ) ^ 2 - 2 * s / γ)) 0 := by
      refine analyticAt_lFun_comp (f := fun s : ℂ => 1 + 4 / (γ : ℂ) ^ 2 - 2 * s / γ)
        (by fun_prop) ?_
      have h := analyticAt_Gamma_ofReal_pos (show (0 : ℝ) < 1 + 4 / γ ^ 2 by positivity)
      convert h using 1
      push_cast
      ring
    have h0 := Complex.continuous_ofReal.tendsto (0 : ℝ)
    rw [Complex.ofReal_zero] at h0
    have h := ha.continuousAt.tendsto.comp h0
    simp only [mul_zero, zero_div, sub_zero] at h
    exact h
  have hA₃ : Tendsto (fun η : ℝ => (lFun (1 - (2 * θ + η) / γ))⁻¹) (𝓝 0)
      (𝓝 (lFun (1 - 2 * θ / γ))⁻¹) := by
    have ha : AnalyticAt ℂ (fun s : ℂ => (lFun (1 - (2 * θ + s) / γ))⁻¹) 0 := by
      refine analyticAt_inv_lFun_comp (f := fun s : ℂ => 1 - (2 * θ + s) / γ) (by fun_prop) ?_
      have h := analyticAt_Gamma_ofReal_pos (show (0 : ℝ) < 2 * θ / γ by positivity)
      convert h using 1
      push_cast
      ring
    have h0 := Complex.continuous_ofReal.tendsto (0 : ℝ)
    rw [Complex.ofReal_zero] at h0
    have h := ha.continuousAt.tendsto.comp h0
    simp only [add_zero] at h
    exact h
  have hB : Tendsto (fun η : ℝ => Complex.Gamma (1 + η / γ)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun η : ℝ => (1 : ℂ) + η / γ := by fun_prop
    have h0 := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_div, add_zero] at h0
    have h := hG1.tendsto.comp h0
    rwa [Complex.Gamma_one] at h
  have hC : Tendsto (fun η : ℝ => (Complex.Gamma (1 - η / γ))⁻¹) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun η : ℝ => (1 : ℂ) - η / γ := by fun_prop
    have h0 := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_div, sub_zero] at h0
    have h := (hG1.tendsto.comp h0).inv₀ (by rw [Complex.Gamma_one]; exact one_ne_zero)
    rwa [Complex.Gamma_one, inv_one] at h
  have hlim : Tendsto (fun η : ℝ => lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) *
      lFun (1 + 4 / (γ : ℂ) ^ 2 - 2 * η / γ) * (lFun (1 - (2 * θ + η) / γ))⁻¹ *
        (-(1 / (γ : ℂ)) * Complex.Gamma (1 + η / γ) * (Complex.Gamma (1 - η / γ))⁻¹)) (𝓝 0)
      (𝓝 (lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) * lFun (1 + 4 / (γ : ℂ) ^ 2) *
        (lFun (1 - 2 * θ / γ))⁻¹ * (-(1 / (γ : ℂ)) * 1 * 1))) :=
    ((tendsto_const_nhds.mul hA₂).mul hA₃).mul ((tendsto_const_nhds.mul hB).mul hC)
  rw [show lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) * lFun (1 + 4 / (γ : ℂ) ^ 2) *
      (lFun (1 - 2 * θ / γ))⁻¹ * (-(1 / (γ : ℂ)) * 1 * 1) = -(1 / (γ : ℂ)) *
        lFun (dualArg₁ γ ((γ / 2 - θ : ℝ) : ℂ)) * lFun (1 + 4 / (γ : ℂ) ^ 2) *
          (lFun (1 - 2 * θ / γ))⁻¹ by ring] at hlim
  refine (hlim.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  set u : ℂ := (η : ℂ) / γ with hu
  have hu0 : u ≠ 0 := div_ne_zero (Complex.ofReal_ne_zero.mpr hη.ne') hγc
  have h₂ : dualArg₂ γ ((γ / 2 + η : ℝ) : ℂ) = 1 + 4 / (γ : ℂ) ^ 2 - 2 * η / γ := by
    unfold dualArg₂
    push_cast
    field_simp
    ring
  have h₃ : dualArg₃ γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) =
      1 - (2 * θ + η) / γ := by
    unfold dualArg₃
    push_cast
    field_simp
    ring
  have h₄ : dualArg₄ γ ((γ / 2 - θ : ℝ) : ℂ) ((γ / 2 + η : ℝ) : ℂ) ((2 / γ + θ : ℝ) : ℂ) = -u := by
    unfold dualArg₄
    rw [hu]
    push_cast
    field_simp
    ring
  have hl₄ : (lFun (-u))⁻¹ = Complex.Gamma (1 + u) * (Complex.Gamma (-u))⁻¹ := by
    unfold lFun
    rw [inv_div, div_eq_mul_inv, show (1 : ℂ) - -u = 1 + u by ring]
  have hΓu : (Complex.Gamma (-u))⁻¹ = -u * (Complex.Gamma (1 - u))⁻¹ := by
    rw [show (1 : ℂ) - u = -u + 1 by ring, Complex.Gamma_add_one _ (neg_ne_zero.mpr hu0), mul_inv,
      ← mul_assoc, mul_inv_cancel₀ (neg_ne_zero.mpr hu0), one_mul]
  unfold dualLC
  rw [h₂, h₃, h₄]
  simp only [div_eq_mul_inv, mul_inv]
  rw [hl₄, hΓu, hu]
  have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
  field_simp

end DOZZ.Proofs

end
