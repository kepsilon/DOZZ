/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.Continuation
import DOZZ.Upsilon.FullShifts
import DOZZ.Upsilon.Uniqueness
import Mathlib.Analysis.Complex.HalfPlane
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.Real.Irrational

/-!
# Zero structure of the entire Upsilon function

The first reciprocal-Gamma shift gives the zero lattice and its local orders.
-/

@[expose] public section

open Complex Filter Topology

namespace DOZZ.Proofs

variable {γ : ℝ}

private noncomputable def upsilonB (γ : ℝ) : ℂ := ((γ / 2 : ℝ) : ℂ)

private noncomputable def upsilonLeftFactor (γ : ℝ) : ℂ → ℂ :=
  (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1) *
    Complex.Gamma (1 - upsilonB γ * z)) *
  (fun z => (Complex.Gamma (upsilonB γ * z))⁻¹)

private theorem upsilonB_cast (γ : ℝ) : upsilonB γ = (γ / 2 : ℂ) := by
  exact Complex.ofReal_div γ 2

private noncomputable def upsilonShiftN (γ : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) * upsilonB γ

private theorem upsilonShiftN_re (γ : ℝ) (n : ℕ) :
    (upsilonShiftN γ n).re = (n : ℝ) * (γ / 2) := by
  simp [upsilonShiftN, upsilonB, Complex.mul_re]

private theorem upsilonShiftN_succ (γ : ℝ) (n : ℕ) :
    upsilonShiftN γ (n + 1) = upsilonShiftN γ n + upsilonB γ := by
  simp [upsilonShiftN, Nat.cast_add]
  ring

private theorem reciprocalGamma_hasDerivAt_zero :
    HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) 1 0 := by
  have hGamma := Complex.tendsto_self_mul_Gamma_nhds_zero
  have hInv : Tendsto (fun z : ℂ => (z * Complex.Gamma z)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa using hGamma.inv₀ (by norm_num : (1 : ℂ) ≠ 0)
  have hprod_ne : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z * Complex.Gamma z ≠ 0 :=
    hGamma.eventually (isOpen_ne.mem_nhds (by norm_num : (1 : ℂ) ≠ 0))
  have hRatio :
      (fun z : ℂ => (z * Complex.Gamma z)⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z => z⁻¹ * (Complex.Gamma z)⁻¹) := by
    filter_upwards [hprod_ne] with z hz
    have hz0 : z ≠ 0 := by
      intro h
      subst z
      simp at hz
    have hΓ : Complex.Gamma z ≠ 0 := (mul_ne_zero_iff.mp hz).2
    field_simp [hz0, hΓ]
  have hSlope : Tendsto (fun z : ℂ => z⁻¹ * (Complex.Gamma z)⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    exact (tendsto_congr' hRatio).mp hInv
  have hDiffSlope : Tendsto
      (fun z : ℂ => z⁻¹ • ((Complex.Gamma z)⁻¹ - (Complex.Gamma 0)⁻¹))
      (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℂ)) := by
    simpa [Complex.Gamma_zero] using hSlope
  exact (hasDerivAt_iff_tendsto_slope_zero).mpr (by simpa using hDiffSlope)

private theorem differentiableAt_upsilonLeftUnitFactor
    (hγ : 0 < γ) :
    DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z)) 0 := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero hγ.ne' (by norm_num)
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1)) 0 := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl hb
  have hGammaOne : DifferentiableAt ℂ Complex.Gamma (1 : ℂ) := by
    exact Complex.differentiableAt_Gamma_one
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 - upsilonB γ * z) 0 := by
    fun_prop
  have hGammaComp : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (1 - upsilonB γ * z)) 0 := by
    have hGammaAt : DifferentiableAt ℂ Complex.Gamma
        (1 - upsilonB γ * (0 : ℂ)) := by
      simpa using hGammaOne
    exact DifferentiableAt.fun_comp' 0
      (f := fun z : ℂ => 1 - upsilonB γ * z) (g := Complex.Gamma) hGammaAt harg
  exact hpow.mul hGammaComp

private theorem upsilonLeftFactor_hasDerivAt_zero
    (hγ : 0 < γ) : HasDerivAt (upsilonLeftFactor γ) 1 0 := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact div_ne_zero hγ.ne' (by norm_num)
  have hlin : HasDerivAt (fun z : ℂ => upsilonB γ * z) (upsilonB γ) 0 := by
    simpa using (hasDerivAt_const_mul (upsilonB γ) :
      HasDerivAt (fun z : ℂ => upsilonB γ * z) (upsilonB γ) 0)
  have hrecip : HasDerivAt
      (fun z : ℂ => (Complex.Gamma (upsilonB γ * z))⁻¹) (upsilonB γ) 0 := by
    have hRecipAt : HasDerivAt (fun z : ℂ => (Complex.Gamma z)⁻¹) 1
        (upsilonB γ * (0 : ℂ)) := by
      simpa using reciprocalGamma_hasDerivAt_zero
    simpa only [Function.comp_def, one_mul] using
      HasDerivAt.comp (0 : ℂ) hRecipAt hlin
  have hOuterDiff := differentiableAt_upsilonLeftUnitFactor hγ
  have hA := hOuterDiff.hasDerivAt.mul hrecip
  simpa [upsilonLeftFactor, Complex.Gamma_zero, Complex.Gamma_one,
    Complex.cpow_neg, hb] using hA

/-- The derivative at zero is the value one half-period to the right. -/
theorem IsUpsilon.deriv_zero {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) : deriv U 0 = U (γ / 2) := by
  have hFactor := upsilonLeftFactor_hasDerivAt_zero hγ
  have hFactor0 : upsilonLeftFactor γ 0 = 0 := by
    simp [upsilonLeftFactor, Complex.Gamma_zero]
  have hUshift : DifferentiableAt ℂ (fun z : ℂ => U (z + upsilonB γ)) 0 := by
    exact DifferentiableAt.fun_comp' 0 (f := fun z : ℂ => z + upsilonB γ)
      (g := U) (hU.1 (0 + upsilonB γ)) (by fun_prop)
  have hProd := hFactor.mul hUshift.hasDerivAt
  have hProd' : HasDerivAt
      (upsilonLeftFactor γ * fun z : ℂ => U (z + upsilonB γ))
      (U (upsilonB γ)) 0 := by
    have hFactor0 : upsilonLeftFactor γ 0 = 0 := by
      simp [upsilonLeftFactor, Complex.Gamma_zero]
    simpa [hFactor0] using hProd
  have hLocalEq :
      (fun z : ℂ => U z) =ᶠ[𝓝 (0 : ℂ)]
        (upsilonLeftFactor γ * fun z : ℂ => U (z + upsilonB γ)) := by
    have hOpen : IsOpen {z : ℂ | z.re < 2 / γ} := Complex.isOpen_re_lt (2 / γ)
    have h0 : (0 : ℂ) ∈ {z : ℂ | z.re < 2 / γ} := by
      dsimp
      have hbound : 0 < 2 / γ := by positivity
      simpa using hbound
    filter_upwards [hOpen.mem_nhds h0] with z hz
    have hShift := IsUpsilon.shift_b_reciprocal hγ hγ2 hU z hz
    have hFactorEq : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
      change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z) *
        (Complex.Gamma (upsilonB γ * z))⁻¹ * U (z + upsilonB γ)) = U z
      rw [upsilonB_cast]
      simpa [mul_assoc] using hShift
    change U z = (upsilonLeftFactor γ * fun w : ℂ => U (w + upsilonB γ)) z
    rw [Pi.mul_apply]
    exact hFactorEq.symm
  have hUderiv := hProd'.congr_of_eventuallyEq hLocalEq
  calc
    deriv U 0 = U (upsilonB γ) := hUderiv.deriv
    _ = U (γ / 2) := by rw [upsilonB_cast]

private theorem IsUpsilon.left_product {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) :
    ∀ (N : ℕ) (z : ℂ),
      (∀ j ∈ Finset.range N, (z + upsilonShiftN γ j).re < 2 / γ) →
      U z = U (z + upsilonShiftN γ N) *
        ∏ j ∈ Finset.range N, upsilonLeftFactor γ (z + upsilonShiftN γ j) := by
  intro N
  induction N with
  | zero =>
      intro z hz
      simp [upsilonShiftN]
  | succ N ih =>
      intro z hstage
      have hz0 : z.re < 2 / γ := by
        simpa [upsilonShiftN] using hstage 0 (by simp)
      have hShift := IsUpsilon.shift_b_reciprocal hγ hγ2 hU z hz0
      have hfirst : upsilonLeftFactor γ z * U (z + upsilonB γ) = U z := by
        change ((upsilonB γ) ^ ((γ : ℂ) * z - 1) *
          Complex.Gamma (1 - upsilonB γ * z) *
          (Complex.Gamma (upsilonB γ * z))⁻¹ * U (z + upsilonB γ)) = U z
        rw [upsilonB_cast]
        simpa [mul_assoc] using hShift
      have hstage' : ∀ j ∈ Finset.range N,
          ((z + upsilonB γ) + upsilonShiftN γ j).re < 2 / γ := by
        intro j hj
        have hj' : j + 1 ∈ Finset.range (N + 1) := by
          apply Finset.mem_range.mpr
          exact Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have h := hstage (j + 1) hj'
        have harg : z + upsilonB γ + upsilonShiftN γ j =
            z + upsilonShiftN γ (j + 1) := by
          rw [upsilonShiftN_succ]
          ring
        rw [harg]
        exact h
      have htail := ih (z + upsilonB γ) hstage'
      have hend : z + upsilonB γ + upsilonShiftN γ N =
          z + upsilonShiftN γ (N + 1) := by
        rw [upsilonShiftN_succ]
        ring
      have hprod :
          (∏ j ∈ Finset.range N,
            upsilonLeftFactor γ ((z + upsilonB γ) + upsilonShiftN γ j)) =
          ∏ j ∈ Finset.range N,
            upsilonLeftFactor γ (z + upsilonShiftN γ (j + 1)) := by
        apply Finset.prod_congr rfl
        intro j hj
        have harg : z + upsilonB γ + upsilonShiftN γ j =
            z + upsilonShiftN γ (j + 1) := by
          rw [upsilonShiftN_succ]
          ring
        rw [harg]
      rw [← hfirst, htail, hend, hprod, Finset.prod_range_succ']
      simp only [upsilonShiftN, Nat.cast_zero, zero_mul, add_zero]
      ring

private theorem exists_upsilonShiftN_between_zero_and_B (hγ : 0 < γ) (z : ℂ)
    (hz : z.re ≤ 0) :
    ∃ N : ℕ, 0 < (z + upsilonShiftN γ N).re ∧
      (z + upsilonShiftN γ N).re ≤ γ / 2 := by
  have hb : 0 < γ / 2 := by positivity
  let y : ℝ := -z.re / (γ / 2)
  have hy : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg (neg_nonneg.mpr hz) hb.le
  let N : ℕ := Nat.floor y + 1
  have hNcast : (N : ℝ) = (Nat.floor y : ℝ) + 1 := by simp [N]
  have hylt : y < (N : ℝ) := by
    rw [hNcast]
    exact Nat.lt_floor_add_one y
  have hNle : (N : ℝ) ≤ y + 1 := by
    rw [hNcast]
    have hfloor := Nat.floor_le hy
    linarith
  have hzy : z.re = -(y * (γ / 2)) := by
    dsimp [y]
    field_simp [ne_of_gt hb]
  have hlow : 0 < z.re + (N : ℝ) * (γ / 2) := by
    have hmul := mul_lt_mul_of_pos_right hylt hb
    rw [hzy]
    linarith only [hmul]
  have hupp : z.re + (N : ℝ) * (γ / 2) ≤ γ / 2 := by
    have hmul := mul_le_mul_of_nonneg_right hNle hb.le
    rw [hzy]
    linarith only [hmul]
  refine ⟨N, ?_, ?_⟩
  · rw [Complex.add_re, upsilonShiftN_re]
    simpa using hlow
  · rw [Complex.add_re, upsilonShiftN_re]
    exact hupp

private theorem upsilon_arg_eq_lattice_iff (hγ : 0 < γ) (j n : ℕ) (z : ℂ) :
    upsilonB γ * (z + upsilonShiftN γ j) = -(n : ℂ) ↔
      z = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (div_pos hγ (by norm_num)).ne'
  have hshiftCast : upsilonShiftN γ j =
      (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := by
    change ((j : ℝ) : ℂ) * ((γ / 2 : ℝ) : ℂ) = _
    exact (Complex.ofReal_mul _ _).symm
  have hdivCast : (n : ℂ) / upsilonB γ =
      (((n : ℝ) / (γ / 2) : ℝ) : ℂ) := by
    change ((n : ℝ) : ℂ) / ((γ / 2 : ℝ) : ℂ) = _
    exact (Complex.ofReal_div _ _).symm
  have hreal : (n : ℝ) / (γ / 2) = (n : ℝ) * (2 / γ) := by
    field_simp [hγ.ne']
  constructor
  · intro harg
    have hmul : upsilonB γ * z = -(n : ℂ) - upsilonB γ * upsilonShiftN γ j := by
      calc
        upsilonB γ * z =
            upsilonB γ * (z + upsilonShiftN γ j) -
              upsilonB γ * upsilonShiftN γ j := by ring
        _ = _ := by rw [harg]
    have hsolve : z = -(n : ℂ) / upsilonB γ - upsilonShiftN γ j := by
      calc
        z = 1 * z := by simp
        _ = (upsilonB γ)⁻¹ * (upsilonB γ * z) := by
          calc
            1 * z = (upsilonB γ)⁻¹ * upsilonB γ * z := by
              rw [inv_mul_cancel₀ hb, one_mul]
            _ = (upsilonB γ)⁻¹ * (upsilonB γ * z) := by ring
        _ = (upsilonB γ)⁻¹ *
            (-(n : ℂ) - upsilonB γ * upsilonShiftN γ j) := by rw [hmul]
        _ = _ := by field_simp [hb]
    rw [neg_div, hdivCast, hshiftCast, hreal] at hsolve
    calc
      z = -(((n : ℝ) * (2 / γ) : ℝ) : ℂ) -
          (((j : ℝ) * (γ / 2) : ℝ) : ℂ) := hsolve
      _ = -((j : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
        push_cast
        ring
  · intro h
    rw [h, hshiftCast]
    rw [upsilonB_cast]
    push_cast
    field_simp [hγ.ne']
    ring

private theorem upsilonLeftFactor_eq_zero_iff (hγ : 0 < γ) {z : ℂ}
    (hz : z.re ≤ 0) :
    upsilonLeftFactor γ z = 0 ↔
      ∃ n : ℕ, upsilonB γ * z = -(n : ℂ) := by
  have hbR : 0 < γ / 2 := by positivity
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact hbR.ne'
  have hbzre : (upsilonB γ * z).re = (γ / 2) * z.re := by
    simp [upsilonB, Complex.mul_re]
  have hGamma1 : Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re, hbzre]
      have hmul : (γ / 2) * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbR.le hz
      linarith)
  have hpow : upsilonB γ ^ ((γ : ℂ) * z - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
  have houter :
      upsilonB γ ^ ((γ : ℂ) * z - 1) * Complex.Gamma (1 - upsilonB γ * z) ≠ 0 :=
    mul_ne_zero hpow hGamma1
  change (upsilonB γ ^ ((γ : ℂ) * z - 1) *
      Complex.Gamma (1 - upsilonB γ * z)) *
      (Complex.Gamma (upsilonB γ * z))⁻¹ = 0 ↔ _
  rw [mul_eq_zero]
  constructor
  · rintro (hbad | hrecip)
    · exact (houter hbad).elim
    · rw [inv_eq_zero] at hrecip
      have hzero := (Complex.Gamma_eq_zero_iff (upsilonB γ * z)).mp hrecip
      exact hzero
  · rintro ⟨n, harg⟩
    right
    rw [inv_eq_zero, harg, Complex.Gamma_neg_nat_eq_zero]

private theorem upsilonLeftOuter_differentiableAt (hγ : 0 < γ) (w : ℂ)
    (hRe : 0 < (1 - upsilonB γ * w).re) :
    DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1) *
        Complex.Gamma (1 - upsilonB γ * z)) w := by
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (div_pos hγ (by norm_num)).ne'
  have hGammaArg : ∀ n : ℕ, 1 - upsilonB γ * w ≠ -(n : ℂ) := by
    intro n heq
    rw [Complex.sub_re, Complex.one_re] at hRe
    have hre := congrArg Complex.re heq
    rw [Complex.sub_re, Complex.one_re] at hre
    have hright : (-(n : ℂ)).re = -(n : ℝ) := by simp
    rw [hright] at hre
    linarith
  have hpow : DifferentiableAt ℂ
      (fun z : ℂ => upsilonB γ ^ ((γ : ℂ) * z - 1)) w := by
    apply DifferentiableAt.const_cpow
    · fun_prop
    · exact Or.inl hb
  have hGammaAt : DifferentiableAt ℂ Complex.Gamma (1 - upsilonB γ * w) :=
    Complex.differentiableAt_Gamma _ hGammaArg
  have harg : DifferentiableAt ℂ (fun z : ℂ => 1 - upsilonB γ * z) w := by
    fun_prop
  have hGammaComp : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (1 - upsilonB γ * z)) w := by
    exact DifferentiableAt.fun_comp' w
      (f := fun z : ℂ => 1 - upsilonB γ * z) (g := Complex.Gamma) hGammaAt harg
  exact hpow.mul hGammaComp

private theorem upsilonLeftFactor_differentiableAt_of_re_nonpos
    (hγ : 0 < γ) {w : ℂ} (hw : w.re ≤ 0) :
    DifferentiableAt ℂ (upsilonLeftFactor γ) w := by
  have hbR : 0 < γ / 2 := by positivity
  have hbzre : (upsilonB γ * w).re = (γ / 2) * w.re := by
    simp [upsilonB, Complex.mul_re]
  have hArgRe : 0 < (1 - upsilonB γ * w).re := by
    rw [Complex.sub_re, Complex.one_re, hbzre]
    have hmul : (γ / 2) * w.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbR.le hw
    linarith
  have houter := upsilonLeftOuter_differentiableAt hγ w hArgRe
  have hrecip : DifferentiableAt ℂ
      (fun z : ℂ => (Complex.Gamma (upsilonB γ * z))⁻¹) w := by
    exact DifferentiableAt.fun_comp' w
      (f := fun z : ℂ => upsilonB γ * z)
      (g := fun z : ℂ => (Complex.Gamma z)⁻¹)
      Complex.differentiable_one_div_Gamma.differentiableAt (by fun_prop)
  exact houter.mul hrecip

private theorem upsilonLeftFactor_deriv_ne_zero_at_lattice (hγ : 0 < γ)
    (w : ℂ) (n : ℕ) (harg : upsilonB γ * w = -(n : ℂ)) :
    deriv (upsilonLeftFactor γ) w ≠ 0 := by
  have hbR : 0 < γ / 2 := by positivity
  have hb : upsilonB γ ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact hbR.ne'
  have hGammaArgRe : 0 < (1 - upsilonB γ * w).re := by
    rw [harg, Complex.sub_re, Complex.one_re]
    simp
    positivity
  have hOuterDiff := upsilonLeftOuter_differentiableAt hγ w hGammaArgRe
  let R : ℂ → ℂ := fun z => (Complex.Gamma z)⁻¹
  have hRdiff : DifferentiableAt ℂ R (-(n : ℂ)) := by
    exact Complex.differentiable_one_div_Gamma.differentiableAt
  have hRder : HasDerivAt R (deriv R (-(n : ℂ))) (-(n : ℂ)) := hRdiff.hasDerivAt
  have hlin : HasDerivAt (fun z : ℂ => upsilonB γ * z) (upsilonB γ) w := by
    simpa using (hasDerivAt_const_mul (upsilonB γ) :
      HasDerivAt (fun z : ℂ => upsilonB γ * z) (upsilonB γ) w)
  have hRecipDeriv : HasDerivAt
      (fun z : ℂ => (Complex.Gamma (upsilonB γ * z))⁻¹)
      (deriv R (-(n : ℂ)) * upsilonB γ) w := by
    simpa only [Function.comp_def] using hRder.comp_of_eq w hlin harg.symm
  have hproduct := hOuterDiff.hasDerivAt.mul hRecipDeriv
  have hfactorDeriv : deriv (upsilonLeftFactor γ) w =
      (upsilonB γ ^ ((γ : ℂ) * w - 1) *
        Complex.Gamma (1 - upsilonB γ * w)) *
        (deriv R (-(n : ℂ)) * upsilonB γ) := by
    have h := hproduct.deriv
    simpa [upsilonLeftFactor, Function.comp_def, R, harg,
      Complex.Gamma_neg_nat_eq_zero] using h
  rw [hfactorDeriv]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hb)
    · exact Complex.Gamma_ne_zero_of_re_pos hGammaArgRe
  · exact mul_ne_zero (deriv_one_div_Gamma_ne_zero_neg_nat n) hb

private theorem IsUpsilon.zero_left_iff {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) (hz : z.re ≤ 0) :
    U z = 0 ↔ ∃ m n : ℕ, z = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
  obtain ⟨N, hEnd0, hEndB⟩ := exists_upsilonShiftN_between_zero_and_B hγ z hz
  have hbpos : 0 < γ / 2 := by positivity
  have hEndQ : (z + upsilonShiftN γ N).re < Q γ := by
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      have hpos : 0 < 2 / γ := by positivity
      linarith
    exact hEndB.trans_lt hbQ
  have hStageLe : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re ≤ 0 := by
    intro j hj
    have hjN : j + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hmul := mul_le_mul_of_nonneg_right
      (show (j : ℝ) + 1 ≤ (N : ℝ) by exact_mod_cast hjN)
      (show 0 ≤ γ / 2 by positivity)
    rw [add_mul] at hmul
    have hstep : (z + upsilonShiftN γ j).re + γ / 2 ≤
        (z + upsilonShiftN γ N).re := by
      rw [Complex.add_re, Complex.add_re, upsilonShiftN_re, upsilonShiftN_re]
      linarith
    linarith [hstep, hEndB]
  have hStage : ∀ j ∈ Finset.range N,
      (z + upsilonShiftN γ j).re < 2 / γ := by
    intro j hj
    have hjle := hStageLe j hj
    have hpos : 0 < 2 / γ := by positivity
    linarith
  have hformula := IsUpsilon.left_product hγ hγ2 hU N z hStage
  have hEndNe : U (z + upsilonShiftN γ N) ≠ 0 := by
    rw [hU.2 _ hEnd0 hEndQ]
    exact Complex.exp_ne_zero _
  have hUzero : U z = 0 ↔
      (∏ j ∈ Finset.range N,
        upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 := by
    rw [hformula, mul_eq_zero]
    simp [hEndNe]
  constructor
  · intro hzero
    have hprod := hUzero.mp hzero
    obtain ⟨j, hj, hfactor⟩ := Finset.prod_eq_zero_iff.mp hprod
    have hzj := hStageLe j hj
    obtain ⟨n, harg⟩ := (upsilonLeftFactor_eq_zero_iff hγ hzj).mp hfactor
    have hrep := (upsilon_arg_eq_lattice_iff hγ j n z).mp harg
    exact ⟨j, n, hrep⟩
  · rintro ⟨m, n, hrep⟩
    have hy : 0 ≤ -z.re / (γ / 2) := by
      exact div_nonneg (neg_nonneg.mpr hz) (by positivity)
    let y : ℝ := -z.re / (γ / 2)
    have hmle : (m : ℝ) ≤ y := by
      have hrepRe := congrArg Complex.re hrep
      have hb := hbpos
      have hrepRe' : z.re = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ)) := by
        simpa using hrepRe
      dsimp [y]
      apply (le_div_iff₀ hb).2
      rw [hrepRe']
      have hn : 0 ≤ (n : ℝ) * (2 / γ) := by positivity
      linarith
    have hmN : m < N := by
      have hzy : z.re = -(y * (γ / 2)) := by
        dsimp [y]
        field_simp [ne_of_gt hbpos]
      have hEnd0' : 0 < z.re + (N : ℝ) * (γ / 2) := by
        have hEnd0'' := hEnd0
        rw [Complex.add_re, upsilonShiftN_re] at hEnd0''
        exact hEnd0''
      rw [hzy] at hEnd0'
      have hyltNmul : y * (γ / 2) < (N : ℝ) * (γ / 2) := by
        linarith only [hEnd0']
      have hyltN : y < (N : ℝ) := lt_of_mul_lt_mul_right hyltNmul hbpos.le
      exact_mod_cast lt_of_le_of_lt hmle hyltN
    have hzj : (z + upsilonShiftN γ m).re ≤ 0 := hStageLe m (by
      apply Finset.mem_range.mpr
      exact hmN)
    have harg := (upsilon_arg_eq_lattice_iff hγ m n z).2 hrep
    have hfactor := (upsilonLeftFactor_eq_zero_iff hγ hzj).2 ⟨n, harg⟩
    have hprod :
        (∏ j ∈ Finset.range N,
          upsilonLeftFactor γ (z + upsilonShiftN γ j)) = 0 :=
      Finset.prod_eq_zero_iff.mpr ⟨m, Finset.mem_range.mpr hmN, hfactor⟩
    exact hUzero.mpr hprod

/-- The zeros are the two reflected negative reciprocal-Gamma lattices. -/
theorem IsUpsilon.eq_zero_iff {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (z : ℂ) :
    U z = 0 ↔ ∃ m n : ℕ, z = -(m * (γ / 2) + n * (2 / γ) : ℝ) ∨
      z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
  constructor
  · intro hz
    by_cases hleft : z.re ≤ 0
    · obtain ⟨m, n, hrep⟩ :=
        (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).mp hz
      exact ⟨m, n, Or.inl hrep⟩
    · have hzpos : 0 < z.re := lt_of_not_ge hleft
      by_cases hmid : z.re < Q γ
      · have hzexp := hU.2 z hzpos hmid
        have hexpZero : Complex.exp (upsilonLog γ z) = 0 := by
          simpa [hz] using hzexp.symm
        exact (Complex.exp_ne_zero _ hexpZero).elim
      · have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith
        have hreflect : U ((Q γ : ℂ) - z) = 0 := by
          rw [IsUpsilon.reflect hγ hγ2 hU z]
          exact hz
        obtain ⟨m, n, hrep⟩ :=
          (IsUpsilon.zero_left_iff hγ hγ2 hU ((Q γ : ℂ) - z) hreflectRe).mp hreflect
        have hright : z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
          calc
            z = (Q γ : ℂ) - ((Q γ : ℂ) - z) := by ring
            _ = (Q γ : ℂ) -
                (-((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ)) := by rw [hrep]
            _ = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
              push_cast
              ring
        exact ⟨m, n, Or.inr hright⟩
  · rintro ⟨m, n, hrep | hrep⟩
    · have hleft : z.re ≤ 0 := by
        rw [hrep]
        simp only [Complex.neg_re, Complex.ofReal_re]
        have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
        exact neg_nonpos.mpr hn
      exact (IsUpsilon.zero_left_iff hγ hγ2 hU z hleft).2 ⟨m, n, hrep⟩
    · have hreflectRep : (Q γ : ℂ) - z =
          -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
        calc
          (Q γ : ℂ) - z = (Q γ : ℂ) - (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by
            rw [hrep]
          _ = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
            push_cast
            ring
      have hreflectRe : ((Q γ : ℂ) - z).re ≤ 0 := by
        rw [hreflectRep]
        simp only [Complex.neg_re, Complex.ofReal_re]
        have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
        exact neg_nonpos.mpr hn
      have hleftzero := (IsUpsilon.zero_left_iff hγ hγ2 hU
        ((Q γ : ℂ) - z) hreflectRe).2
        ⟨m, n, hreflectRep⟩
      exact (IsUpsilon.reflect hγ hγ2 hU z).symm.trans hleftzero

/-- A negative lattice zero is simple when its lattice representation is unique. -/
theorem IsUpsilon.deriv_ne_zero_of_unique {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (m n : ℕ)
    (huniq : ∀ m' n' : ℕ,
      (m' : ℝ) * (γ / 2) + n' * (2 / γ) =
        m * (γ / 2) + n * (2 / γ) → m' = m ∧ n' = n) :
    deriv U (-(m * (γ / 2) + n * (2 / γ) : ℝ)) ≠ 0 := by
  let z₀ : ℂ := -(m * (γ / 2) + n * (2 / γ) : ℝ)
  have hz₀re : z₀.re ≤ 0 := by
    have hn : 0 ≤ (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by positivity
    change -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ)) ≤ 0
    exact neg_nonpos.mpr hn
  obtain ⟨N, hEnd0, hEndB⟩ := exists_upsilonShiftN_between_zero_and_B hγ z₀ hz₀re
  have hb : 0 < γ / 2 := by positivity
  have hEndQ : (z₀ + upsilonShiftN γ N).re < Q γ := by
    have hbQ : γ / 2 < Q γ := by
      unfold Q
      have hpos : 0 < 2 / γ := by positivity
      linarith
    exact hEndB.trans_lt hbQ
  have hStageLe : ∀ j ∈ Finset.range N,
      (z₀ + upsilonShiftN γ j).re ≤ 0 := by
    intro j hj
    have hjN : j + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)
    have hmul := mul_le_mul_of_nonneg_right
      (show (j : ℝ) + 1 ≤ (N : ℝ) by exact_mod_cast hjN)
      (show 0 ≤ γ / 2 by positivity)
    rw [add_mul] at hmul
    have hstep : (z₀ + upsilonShiftN γ j).re + γ / 2 ≤
        (z₀ + upsilonShiftN γ N).re := by
      rw [Complex.add_re, Complex.add_re, upsilonShiftN_re, upsilonShiftN_re]
      linarith
    linarith [hstep, hEndB]
  have hStage : ∀ j ∈ Finset.range N,
      (z₀ + upsilonShiftN γ j).re < 2 / γ := by
    intro j hj
    have hjle := hStageLe j hj
    have hpos : 0 < 2 / γ := by positivity
    linarith
  have hz₀repr : z₀ = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
    rfl
  have hEnd0Real : 0 < z₀.re + (N : ℝ) * (γ / 2) := by
    have h := hEnd0
    rw [Complex.add_re, upsilonShiftN_re] at h
    exact h
  have hmMul : (m : ℝ) * (γ / 2) < (N : ℝ) * (γ / 2) := by
    rw [hz₀repr] at hEnd0Real
    simp only [Complex.neg_re, Complex.ofReal_re] at hEnd0Real
    have hn : 0 ≤ (n : ℝ) * (2 / γ) := by positivity
    linarith only [hEnd0Real, hn]
  have hmN : m < N := by
    exact_mod_cast (lt_of_mul_lt_mul_right hmMul hb.le)
  let S : Finset ℕ := Finset.range N
  let f : ℕ → ℂ → ℂ := fun j w => upsilonLeftFactor γ (w + upsilonShiftN γ j)
  let P : ℂ → ℂ := fun w => ∏ j ∈ S, f j w
  let R : ℂ → ℂ := fun w => ∏ j ∈ S.erase m, f j w
  let E : ℂ → ℂ := fun w => U (w + upsilonShiftN γ N)
  have hmS : m ∈ S := by
    dsimp [S]
    exact Finset.mem_range.mpr hmN
  have hzm : upsilonB γ * (z₀ + upsilonShiftN γ m) = -(n : ℂ) :=
    (upsilon_arg_eq_lattice_iff hγ m n z₀).2 hz₀repr
  have hfm0 : f m z₀ = 0 := by
    dsimp [f]
    exact (upsilonLeftFactor_eq_zero_iff hγ (hStageLe m hmS)).2 ⟨n, hzm⟩
  have hfmDerivNe : deriv (f m) z₀ ≠ 0 := by
    have hwre : (z₀ + upsilonShiftN γ m).re ≤ 0 := hStageLe m hmS
    have hdiff := upsilonLeftFactor_differentiableAt_of_re_nonpos hγ hwre
    have hlin : HasDerivAt (fun w : ℂ => w + upsilonShiftN γ m) 1 z₀ := by
      simpa using (hasDerivAt_id z₀).add_const (upsilonShiftN γ m)
    have hcomp := hdiff.hasDerivAt.comp (z₀) hlin
    have hderiv : deriv (f m) z₀ =
        deriv (upsilonLeftFactor γ) (z₀ + upsilonShiftN γ m) := by
      have := hcomp.deriv
      simpa [f, Function.comp_def] using this
    rw [hderiv]
    exact upsilonLeftFactor_deriv_ne_zero_at_lattice hγ
      (z₀ + upsilonShiftN γ m) n hzm
  have hRdiff : DifferentiableAt ℂ R z₀ := by
    dsimp [R]
    apply DifferentiableAt.fun_finsetProd
    intro j hj
    have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
    exact DifferentiableAt.fun_comp' z₀
      (f := fun w : ℂ => w + upsilonShiftN γ j)
      (g := upsilonLeftFactor γ)
      (upsilonLeftFactor_differentiableAt_of_re_nonpos hγ (hStageLe j hjS))
      (by fun_prop)
  have hRne : R z₀ ≠ 0 := by
    dsimp [R]
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hjS : j ∈ S := (Finset.mem_erase.mp hj).2
    have hjNe : j ≠ m := (Finset.mem_erase.mp hj).1
    intro hzero
    obtain ⟨n', harg⟩ :=
      (upsilonLeftFactor_eq_zero_iff hγ (hStageLe j hjS)).mp hzero
    have hrepj := (upsilon_arg_eq_lattice_iff hγ j n' z₀).mp harg
    have hsum : (j : ℝ) * (γ / 2) + (n' : ℝ) * (2 / γ) =
        (m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) := by
      have hRe := congrArg Complex.re (hrepj.symm.trans hz₀repr)
      simpa only [Complex.neg_re, Complex.ofReal_re] using neg_injective hRe
    exact hjNe (huniq j n' hsum).1
  have hP_eq : P = (f m) * R := by
    funext w
    dsimp [P, R]
    rw [← Finset.prod_erase_mul S (fun j => f j w) hmS]
    ring
  have hfmDiff : DifferentiableAt ℂ (f m) z₀ := by
    exact DifferentiableAt.fun_comp' z₀
      (f := fun w : ℂ => w + upsilonShiftN γ m)
      (g := upsilonLeftFactor γ)
      (upsilonLeftFactor_differentiableAt_of_re_nonpos hγ (hStageLe m hmS))
      (by fun_prop)
  have hPdiff : DifferentiableAt ℂ P z₀ := by
    rw [hP_eq]
    exact DifferentiableAt.mul hfmDiff hRdiff
  have hPderiv : deriv P z₀ = deriv (f m) z₀ * R z₀ := by
    rw [hP_eq, deriv_mul hfmDiff hRdiff]
    simp [hfm0]
  have hPne : deriv P z₀ ≠ 0 := by
    rw [hPderiv]
    exact mul_ne_zero hfmDerivNe hRne
  have hEndNe : E z₀ ≠ 0 := by
    dsimp [E]
    rw [hU.2 _ hEnd0 hEndQ]
    exact Complex.exp_ne_zero _
  have hStageEvent : ∀ᶠ w in 𝓝 z₀, ∀ j ∈ S,
      (w + upsilonShiftN γ j).re < 2 / γ := by
    rw [eventually_all_finset S]
    intro j hj
    have hpoint : (z₀ + upsilonShiftN γ j).re < 2 / γ := by
      have := hStageLe j hj
      have hpos : 0 < 2 / γ := by positivity
      linarith
    have hopen : IsOpen {w : ℂ | w.re < 2 / γ} := Complex.isOpen_re_lt _
    have hmem : z₀ + upsilonShiftN γ j ∈ {w : ℂ | w.re < 2 / γ} := hpoint
    have hevent := (by fun_prop : ContinuousAt
      (fun w : ℂ => w + upsilonShiftN γ j) z₀).eventually (hopen.mem_nhds hmem)
    exact hevent
  have hLocalEq : (fun w : ℂ => U w) =ᶠ[𝓝 z₀] (E * P) := by
    filter_upwards [hStageEvent] with w hw
    have hformula := IsUpsilon.left_product hγ hγ2 hU N w hw
    simpa [E, P, f, S] using hformula
  have hEdiff : DifferentiableAt ℂ E z₀ := by
    exact DifferentiableAt.fun_comp' z₀
      (f := fun w : ℂ => w + upsilonShiftN γ N) (g := U)
      (hU.1 _ ) (by fun_prop)
  have hProductHas := hEdiff.hasDerivAt.mul hPdiff.hasDerivAt
  have hUhas := hProductHas.congr_of_eventuallyEq hLocalEq
  have hderivU : deriv U z₀ = E z₀ * deriv P z₀ := by
    have h := hUhas.deriv
    simpa [hfm0, hP_eq] using h
  have hz₀deriv : deriv U z₀ ≠ 0 := by
    rw [hderivU]
    exact mul_ne_zero hEndNe hPne
  simpa [z₀] using hz₀deriv

private theorem lattice_representation_unique_of_irrational (hγ : 0 < γ)
    (hirr : Irrational (γ ^ 2)) (m n : ℕ) :
    ∀ m' n' : ℕ,
      (m' : ℝ) * (γ / 2) + n' * (2 / γ) =
        m * (γ / 2) + n * (2 / γ) → m' = m ∧ n' = n := by
  intro m' n' hsum
  by_cases hm : m' = m
  · subst m'
    have hcoef : 2 / γ ≠ 0 := (by positivity : 0 < 2 / γ).ne'
    have hn : (n' : ℝ) = (n : ℝ) := by
      have hprod : ((n' : ℝ) - n) * (2 / γ) = 0 := by linear_combination hsum
      rcases mul_eq_zero.mp hprod with hdiff | hcoef'
      · exact sub_eq_zero.mp hdiff
      · exact (hcoef hcoef').elim
    exact ⟨rfl, Nat.cast_injective hn⟩
  · have hscaled :
        ((m' : ℝ) - m) * γ ^ 2 + 4 * ((n' : ℝ) - n) = 0 := by
      have h := congrArg (fun x : ℝ => x * (2 * γ)) hsum
      field_simp [hγ.ne'] at h
      linear_combination h
    let a : ℤ := -4 * ((n' : ℤ) - n)
    let b : ℤ := (m' : ℤ) - m
    have hb : b ≠ 0 := by
      intro hzero
      apply hm
      have hcast : (m' : ℝ) = (m : ℝ) := by
        have := congrArg (fun x : ℤ => (x : ℝ)) hzero
        simp [b] at this
        linarith
      exact Nat.cast_injective hcast
    have hcastA : (a : ℝ) = -(4 * ((n' : ℝ) - n)) := by
      simp [a]
    have hcastB : (b : ℝ) = (m' : ℝ) - m := by
      simp [b]
    have hratio : γ ^ 2 = (a : ℝ) / (b : ℝ) := by
      rw [hcastA, hcastB]
      have hdReal : (m' : ℝ) - m ≠ 0 := by
        rw [← hcastB]
        exact Int.cast_ne_zero.mpr hb
      field_simp [hdReal]
      linear_combination hscaled
    exact False.elim ((hirr.ne_rational a b) hratio)

/-- Irrational `γ²` makes every zero in either lattice simple. -/
theorem IsUpsilon.deriv_ne_zero_of_irrational {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (hirr : Irrational (γ ^ 2)) (z : ℂ) (hz : U z = 0) :
    deriv U z ≠ 0 := by
  obtain ⟨m, n, hneg | hpos⟩ := (IsUpsilon.eq_zero_iff hγ hγ2 hU z).mp hz
  · have hsimple := IsUpsilon.deriv_ne_zero_of_unique hγ hγ2 hU m n
      (lattice_representation_unique_of_irrational hγ hirr m n)
    simpa [hneg] using hsimple
  · let w : ℂ := (Q γ : ℂ) - z
    have hreflectRep : w = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
      dsimp [w]
      calc
        (Q γ : ℂ) - z = (Q γ : ℂ) -
            (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by rw [hpos]
        _ = -((m : ℝ) * (γ / 2) + (n : ℝ) * (2 / γ) : ℝ) := by
          push_cast
          ring
    have hsimple := IsUpsilon.deriv_ne_zero_of_unique hγ hγ2 hU m n
      (lattice_representation_unique_of_irrational hγ hirr m n)
    rw [← hreflectRep] at hsimple
    have hlin : HasDerivAt (fun x : ℂ => (Q γ : ℂ) - x) (-1) z := by
      exact (hasDerivAt_id z).const_sub (Q γ : ℂ)
    have hchain := (hU.1 (w)).hasDerivAt.comp z hlin
    have hreflectFun : (fun x : ℂ => U ((Q γ : ℂ) - x)) = U := by
      funext x
      exact IsUpsilon.reflect hγ hγ2 hU x
    have hderivEq := congrArg (fun f : ℂ → ℂ => deriv f z) hreflectFun
    have hchainDeriv : deriv (fun x : ℂ => U ((Q γ : ℂ) - x)) z =
        deriv U w * (-1) := by
      simpa [w, Function.comp_def] using hchain.deriv
    have hderiv : deriv U z = deriv U w * (-1) := by
      exact hderivEq.symm.trans hchainDeriv
    rw [hderiv]
    exact mul_ne_zero hsimple (by norm_num)

end DOZZ.Proofs

end
