/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.RtheorAnalytic
public import DOZZ.Statements.Brownian.IsReflectionData
public import DOZZ.Statements.Brownian.IsSourceLateralProjection
public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
public import DOZZ.Statements.Defs.ExtendedSeiberg3
import DOZZ.Brownian.Reflection.PositiveFinite
import DOZZ.Complex.Basic
import DOZZ.DOZZAlgebra.ReflectionShifts
import DOZZ.DOZZAlgebra.ReflectionLimit
import Mathlib.Topology.Instances.Irrational
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import DOZZ.Brownian.Reflection.WitnessIndependence
import DOZZ.Brownian.ReflectionPoleIsolation
import DOZZ.Roots.Existence
import DOZZ.GMC.Assembly.AdmissibleGMC

/-!
# `R = R^DOZZ` from the shift equations

This is the argument of [KRV, §10.6]. Let
`ψ = R / R^DOZZ`, a meromorphic function on a strip around the real axis. The common `γ/2` shift
equation (`reflectionR_first_shift_meromorphic`) makes `ψ` periodic. The `2/γ` shift equations
(`reflectionR_dual_shift_unknown_constant`) make it quasi-periodic, with multiplier
`c_γ / c_γ^DOZZ`. On the physical interval `ψ` is the explicit positive ratio `reflectionDOZZRatio`,
so the multiplier is one. For irrational `γ²` the two periods are rationally independent, so `ψ` is
constant, and the endpoint normalizations `R(Q) = R^DOZZ(Q) = -1` force `ψ = 1`. Continuity of
both coefficients off the Gamma poles then gives equality at every pole-free physical charge. The
remaining couplings follow by continuity in `γ` (`reflection_endpoint_and_gamma_continuity`), since
couplings with irrational square accumulate at every `γ₀`.

The last two theorems prove both Brownian `R_theor` statements from the statements
`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionR_dual_shift_unknown_constant` and
`DOZZ.reflection_endpoint_and_gamma_continuity`.
The three statements are taken verbatim as hypotheses at universe `0`. A reference equator
GFF and its GMC family supply the probability space, and witness independence moves every
coefficient onto one witness family.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The physical reflection interval is longer than the first period: `γ/2 + γ/2 < Q γ`. -/
theorem half_add_half_lt_Q {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ / 2 + γ / 2 < Q γ := by
  unfold Q
  have h : γ / 2 < 2 / γ := by
    rw [div_lt_div_iff₀ two_pos hγ]
    exact mul_self_lt_mul_self hγ.le hγ2
  linarith only [h]

/-- The first-shift denominator, in the form of the DOZZ shift. -/
noncomputable def reflectionFirstShiftDenom (γ : ℝ) (w : ℂ) : ℂ :=
  lFun (-(γ ^ 2 / 4)) * lFun (γ * w / 2 - γ ^ 2 / 4) * lFun (2 + γ ^ 2 / 2 - γ * w / 2)

/-- The dual-shift denominator, in the form of the DOZZ dual shift. -/
noncomputable def reflectionDualShiftDenom (γ : ℝ) (w : ℂ) : ℂ :=
  lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) * lFun (2 * w / γ) * lFun (2 + (4 / γ ^ 2 : ℝ) - 2 * w / γ)

/-- The multiplier of the DOZZ dual shift. -/
noncomputable def reflectionDOZZDualConst (γ μ : ℝ) : ℂ :=
  ((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / lFun ((4 / γ ^ 2 : ℝ) : ℂ)

/-- The first-shift denominator vanishes only on a codiscrete exceptional set. -/
theorem reflectionFirstShiftDenom_ne_zero {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᶠ w in Filter.codiscrete ℂ, reflectionFirstShiftDenom γ w ≠ 0 := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have hq : 0 < γ ^ 2 / 4 := by positivity
  have hq1 : γ ^ 2 / 4 < 1 := by linarith only [pow_lt_pow_left₀ hγ2 hγ.le two_ne_zero]
  have h0 : lFun (-((γ : ℂ) ^ 2 / 4)) ≠ 0 := by
    refine lFun_ne_zero_of_forall_ne_int fun n hn => ?_
    have hn' : -(γ ^ 2 / 4) = (n : ℝ) := by exact_mod_cast hn
    rcases lt_trichotomy n 0 with hlt | heq | hgt
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      linarith only [hn', this, hq1]
    · rw [heq, Int.cast_zero] at hn'
      linarith only [hn', hq]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast hgt
      linarith only [hn', this, hq]
  have h1 := eventually_affine_lFun_ne_zero (c := (γ : ℂ) / 2) (d := -((γ : ℂ) ^ 2 / 4))
    (div_ne_zero hγc two_ne_zero)
  have h2 := eventually_affine_lFun_ne_zero (c := -((γ : ℂ) / 2)) (d := 2 + (γ : ℂ) ^ 2 / 2)
    (neg_ne_zero.mpr (div_ne_zero hγc two_ne_zero))
  filter_upwards [h1, h2] with w hw1 hw2
  unfold reflectionFirstShiftDenom
  refine mul_ne_zero (mul_ne_zero h0 ?_) ?_
  · convert hw1 using 2
    ring
  · convert hw2 using 2
    ring

/-- The dual-shift denominator vanishes only on a codiscrete exceptional set, when `4/γ²` is not
an integer. -/
theorem reflectionDualShiftDenom_ne_zero {γ : ℝ} (hγ : 0 < γ)
    (hγk : ∀ n : ℤ, 4 / γ ^ 2 ≠ n) :
    ∀ᶠ w in Filter.codiscrete ℂ, reflectionDualShiftDenom γ w ≠ 0 := by
  have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ.ne'
  have h0 : lFun (-((4 / γ ^ 2 : ℝ) : ℂ)) ≠ 0 := by
    refine lFun_ne_zero_of_forall_ne_int fun n hn => hγk (-n) ?_
    have hn' : -(4 / γ ^ 2) = (n : ℝ) := by exact_mod_cast hn
    push_cast
    linarith only [hn']
  have h1 := eventually_affine_lFun_ne_zero (c := 2 / (γ : ℂ)) (d := 0)
    (div_ne_zero two_ne_zero hγc)
  have h2 := eventually_affine_lFun_ne_zero (c := -(2 / (γ : ℂ)))
    (d := 2 + ((4 / γ ^ 2 : ℝ) : ℂ)) (neg_ne_zero.mpr (div_ne_zero two_ne_zero hγc))
  filter_upwards [h1, h2] with w hw1 hw2
  unfold reflectionDualShiftDenom
  refine mul_ne_zero (mul_ne_zero h0 ?_) ?_
  · convert hw1 using 2
    ring
  · convert hw2 using 2
    ring

/-- The DOZZ dual multiplier is nonzero when `4/γ²` is not an integer. -/
theorem reflectionDOZZDualConst_ne_zero {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hγk : ∀ n : ℤ, 4 / γ ^ 2 ≠ n) : reflectionDOZZDualConst γ μ ≠ 0 := by
  have hbase : ((dozzBase γ μ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (dozzBase_pos hγ hγ2 hμ).ne'
  refine div_ne_zero ?_ (lFun_ne_zero_of_forall_ne_int fun n hn => hγk n (by exact_mod_cast hn))
  exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by
    exact_mod_cast (div_pos (by norm_num : (0 : ℝ) < 4) (by positivity)).ne')).mpr hbase

/-- Irrationality of `γ²` excludes integer values of `4/γ²`. -/
theorem four_div_sq_ne_int_of_irrational {γ : ℝ} (hγirr : Irrational (γ ^ 2)) (n : ℤ) :
    4 / γ ^ 2 ≠ n := by
  intro h
  have hγ0 : γ ^ 2 ≠ 0 := hγirr.ne_zero
  have hγ1 : γ ≠ 0 := fun h0 => hγ0 (by rw [h0]; ring)
  have hmul : γ ^ 2 * (n : ℝ) = 4 := by
    rw [← h]
    field_simp
  have hn0 : (n : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmul
    norm_num at hmul
  have hsq : γ ^ 2 = ((4 / n : ℚ) : ℝ) := by
    push_cast
    exact eq_div_of_mul_eq hn0 hmul
  exact hγirr ⟨4 / n, hsq.symm⟩

/-- Two meromorphic functions on strips that agree on a real interval share their punctured germ
at every point of the smaller strip. -/
theorem eventuallyEq_nhdsNE_strip_of_eq_on_Ioo {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂)
    {f g : ℂ → ℂ} (hf : MeromorphicOn f (horizontalStrip h₁))
    (hg : MeromorphicOn g (horizontalStrip h₂)) {a b : ℝ} (hab : a < b)
    (hfg : ∀ y ∈ Ioo a b, f (y : ℂ) = g (y : ℂ)) :
    ∀ z ∈ horizontalStrip (min h₁ h₂), f =ᶠ[𝓝[≠] z] g := by
  have hh : 0 < min h₁ h₂ := lt_min hh₁ hh₂
  have hsub₁ : horizontalStrip (min h₁ h₂) ⊆ horizontalStrip h₁ := fun z hz => by
    simp only [horizontalStrip, mem_ofPred_eq] at hz ⊢
    exact lt_of_lt_of_le hz (min_le_left _ _)
  have hsub₂ : horizontalStrip (min h₁ h₂) ⊆ horizontalStrip h₂ := fun z hz => by
    simp only [horizontalStrip, mem_ofPred_eq] at hz ⊢
    exact lt_of_lt_of_le hz (min_le_right _ _)
  have hx₀ : (a + b) / 2 ∈ Ioo a b := ⟨by linarith only [hab], by linarith only [hab]⟩
  have hmem : (((a + b) / 2 : ℝ) : ℂ) ∈ horizontalStrip (min h₁ h₂) :=
    ofReal_mem_horizontalStrip hh _
  have h0 : f =ᶠ[𝓝[≠] (((a + b) / 2 : ℝ) : ℂ)] g :=
    eventuallyEq_nhdsNE_of_eq_on_Ioo hx₀ (hf _ (hsub₁ hmem)) (hg _ (hsub₂ hmem)) hfg
  exact eventuallyEq_nhdsNE_of_isPreconnected (convex_horizontalStrip _).isPreconnected
    (hf.mono_set hsub₁) (hg.mono_set hsub₂) hmem h0

/-- The quotient by the DOZZ coefficient of a solution of the first shift equation is
`γ/2`-periodic as a germ at every point. -/
theorem reflectionQuotient_period {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    {R : ℂ → ℂ}
    (hshift : ∀ᶠ z in codiscrete ℂ,
      R (z - γ / 2) =
        -(μ * Real.pi : ℂ) * R z /
          (lFun (-((γ : ℂ) ^ 2) / 4) *
            lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
            lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2))) (z : ℂ) :
    (fun w => R (w + ((γ / 2 : ℝ) : ℂ)) / reflectionDOZZ γ μ (w + ((γ / 2 : ℝ) : ℂ))) =ᶠ[𝓝[≠] z]
      fun w => R w / reflectionDOZZ γ μ w := by
  have hK : -(μ * Real.pi : ℂ) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast hμ.ne') (by exact_mod_cast Real.pi_ne_zero))
  have hR : ∀ᶠ w in Filter.codiscrete ℂ,
      R (w - (γ : ℂ) / 2) = -(μ * Real.pi : ℂ) * R w / reflectionFirstShiftDenom γ w := by
    filter_upwards [hshift] with w hw
    rw [hw, reflectionFirstShiftDenom, neg_div]
  have hRD : ∀ᶠ w in Filter.codiscrete ℂ,
      reflectionDOZZ γ μ (w - (γ : ℂ) / 2) =
        -(μ * Real.pi : ℂ) * reflectionDOZZ γ μ w / reflectionFirstShiftDenom γ w := by
    filter_upwards [reflectionDOZZ_shift_b hγ hγ2 hμ] with w hw
    rw [hw, reflectionFirstShiftDenom]
  have hper := div_comp_sub_eq_of_shift hK hR hRD (reflectionFirstShiftDenom_ne_zero hγ hγ2)
  have hshifted := eventually_codiscrete_comp_add hper ((γ : ℂ) / 2)
  have hcast : (((γ / 2 : ℝ)) : ℂ) = (γ : ℂ) / 2 := by push_cast; ring
  filter_upwards [eventually_nhdsNE_of_eventually_codiscrete hshifted z] with w hw
  rw [hcast]
  simpa only [add_sub_cancel_right] using hw.symm

/-- The quotient by the DOZZ coefficient of a solution of the dual shift equation with multiplier
`c` is quasi-periodic under `2/γ`, with multiplier `c / c^DOZZ`. -/
theorem reflectionQuotient_dualShift {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hγirr : Irrational (γ ^ 2)) {R : ℂ → ℂ} {c : ℂ}
    (hshift : ∀ᶠ z in codiscrete ℂ,
      R z = -c * R (z + 2 / γ) /
        (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
          lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ))) :
    ∀ᶠ w in codiscrete ℂ, R w / reflectionDOZZ γ μ w =
      c / reflectionDOZZDualConst γ μ * (R (w + 2 / γ) / reflectionDOZZ γ μ (w + 2 / γ)) := by
  have hγk := four_div_sq_ne_int_of_irrational hγirr
  have hγk' : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ) := fun k hk => hγk k (by exact_mod_cast hk)
  have hden : ∀ w : ℂ, lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * w / γ) *
      lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * w / γ) = reflectionDualShiftDenom γ w := by
    intro w
    unfold reflectionDualShiftDenom
    have e1 : (-4 / (γ : ℂ) ^ 2) = -((4 / γ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : (2 + 4 / (γ : ℂ) ^ 2 - 2 * w / γ) = 2 + ((4 / γ ^ 2 : ℝ) : ℂ) - 2 * w / γ := by
      push_cast; ring
    rw [e1, e2]
  have hR : ∀ᶠ w in codiscrete ℂ,
      R w = -c * R (w + 2 / γ) / reflectionDualShiftDenom γ w := by
    filter_upwards [hshift] with w hw
    rw [hw, hden]
  have hRD : ∀ᶠ w in codiscrete ℂ, reflectionDOZZ γ μ w =
      -reflectionDOZZDualConst γ μ * reflectionDOZZ γ μ (w + 2 / γ) /
        reflectionDualShiftDenom γ w := by
    filter_upwards [reflectionDOZZ_shift_binv hγ hγ2 hγk' hμ] with w hw
    rw [hw, reflectionDualShiftDenom, reflectionDOZZDualConst]
  exact div_eq_mul_div_comp_add_of_shift (reflectionDOZZDualConst_ne_zero hγ hγ2 hμ hγk) hR hRD
    (reflectionDualShiftDenom_ne_zero hγ hγk)

/-- On a punctured neighborhood of a physical charge, the quotient of an interpolant of the
probabilistic coefficient by the DOZZ coefficient is the explicit ratio
`reflectionDOZZRatio`. -/
theorem reflectionQuotient_eventually_eq_ratio {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {γ μ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ) {R : ℂ → ℂ}
    (hRα : ∀ α : ℝ, γ / 2 < α → α < Q γ → R (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ))
    {x : ℝ} (hx : x ∈ Ioo (γ / 2) (Q γ)) :
    ∀ᶠ y : ℝ in 𝓝[≠] x, R (y : ℂ) / reflectionDOZZ γ μ (y : ℂ) =
      (reflectionDOZZRatio γ μ y (reflectionBarR P γ y (B y) Z) : ℂ) := by
  filter_upwards [reflectionPoleFree_eventually_nhdsNE hγ x,
    nhdsWithin_le_nhds (Ioo_mem_nhds hx.1 hx.2)] with y hpole hy
  rw [hRα y hy.1 hy.2]
  exact reflectionR_div_reflectionDOZZ P γ μ y (B y) Z hγ hγ2 hμ ⟨hy.1, hy.2⟩ hpole

/-- **`R = R^DOZZ` at irrational `γ²`**, from the two reflection shift equations
(`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionR_dual_shift_unknown_constant`) for
interpolants of the probabilistic coefficient along one witness family, continuity of `R̄` along
that family, and the endpoint limit `R → -1`. -/
theorem reflectionR_eq_reflectionDOZZ_of_shifts
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α : ℝ, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z)
    {h₁ h₂ : ℝ} (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) {R₁ R₂ : ℂ → ℂ}
    (hR₁ : MeromorphicOn R₁ {z | |z.im| < h₁}) (hR₂ : MeromorphicOn R₂ {z | |z.im| < h₂})
    (hR₁α : ∀ α : ℝ, γ / 2 < α → α < Q γ → R₁ (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ))
    (hR₂α : ∀ α : ℝ, γ / 2 < α → α < Q γ → R₂ (α : ℂ) = (reflectionR P γ μ α (B α) Z : ℂ))
    (hshift₁ : ∀ᶠ z in codiscrete ℂ,
      R₁ (z - γ / 2) =
        -(μ * Real.pi : ℂ) * R₁ z /
          (lFun (-((γ : ℂ) ^ 2) / 4) *
            lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
            lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    {c : ℂ}
    (hshift₂ : ∀ᶠ z in codiscrete ℂ,
      R₂ z = -c * R₂ (z + 2 / γ) /
        (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
          lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)))
    (hBar : ContinuousOn (fun α => reflectionBarR P γ α (B α) Z) (Ioo (γ / 2) (Q γ)))
    (hEnd : Tendsto (fun α => reflectionR P γ μ α (B α) Z) (𝓝[<] (Q γ)) (𝓝 (-1)))
    {α : ℝ} (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α) :
    (reflectionR P γ μ α (B α) Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) := by
  have hQ : γ / 2 < Q γ := by linarith only [half_add_half_lt_Q hγ hγ2, hγ]
  have hh : 0 < min h₁ h₂ := lt_min hh₁ hh₂
  have hsub₁ : horizontalStrip (min h₁ h₂) ⊆ {z : ℂ | |z.im| < h₁} := fun z hz => by
    simp only [horizontalStrip, mem_ofPred_eq] at hz ⊢
    exact lt_of_lt_of_le hz (min_le_left _ _)
  set RD := reflectionDOZZ γ μ with hRD_def
  set F : ℂ → ℂ := fun w => R₁ w / RD w with hF_def
  have hFm : MeromorphicOn F (horizontalStrip (min h₁ h₂)) :=
    (hR₁.mono_set hsub₁).div ((meromorphicOn_reflectionDOZZ γ μ hγ hγ2 hμ).mono_set
      (subset_univ _))
  -- the two interpolants share their punctured germs on the common strip
  have hR₁₂ : ∀ z ∈ horizontalStrip (min h₁ h₂), R₁ =ᶠ[𝓝[≠] z] R₂ :=
    eventuallyEq_nhdsNE_strip_of_eq_on_Ioo hh₁ hh₂ hR₁ hR₂ hQ
      (fun y hy => (hR₁α y hy.1 hy.2).trans (hR₂α y hy.1 hy.2).symm)
  -- first period `γ/2`
  have hp₁ : ∀ z ∈ horizontalStrip (min h₁ h₂),
      (fun w => F (w + ((γ / 2 : ℝ) : ℂ))) =ᶠ[𝓝[≠] z] F :=
    fun z _ => reflectionQuotient_period hγ hγ2 hμ hshift₁ z
  -- dual quasi-period `2/γ`
  have hdual := reflectionQuotient_dualShift (μ := μ) hγ hγ2 hμ hγirr hshift₂
  set κ := c / reflectionDOZZDualConst γ μ with hκ_def
  have hT₂ : ((2 / γ : ℝ) : ℂ) = 2 / (γ : ℂ) := by push_cast; ring
  have hq : ∀ z ∈ horizontalStrip (min h₁ h₂),
      F =ᶠ[𝓝[≠] z] fun w => κ * F (w + ((2 / γ : ℝ) : ℂ)) := by
    intro z hz
    have hzT : z + ((2 / γ : ℝ) : ℂ) ∈ horizontalStrip (min h₁ h₂) :=
      add_ofReal_mem_horizontalStrip hz _
    have h1 : F =ᶠ[𝓝[≠] z] fun w => R₂ w / RD w :=
      (hR₁₂ z hz).mono fun w hw => by
        show R₁ w / RD w = R₂ w / RD w
        rw [hw]
    have h2 : ∀ᶠ w in 𝓝[≠] z, R₁ (w + ((2 / γ : ℝ) : ℂ)) = R₂ (w + ((2 / γ : ℝ) : ℂ)) :=
      (tendsto_add_const_nhdsNE z _).eventually (hR₁₂ _ hzT)
    filter_upwards [h1, h2, eventually_nhdsNE_of_eventually_codiscrete hdual z] with w hw1 hw2 hw3
    rw [hw1, hw3]
    show κ * (R₂ (w + 2 / (γ : ℂ)) / RD (w + 2 / (γ : ℂ))) =
      κ * (R₁ (w + ((2 / γ : ℝ) : ℂ)) / RD (w + ((2 / γ : ℝ) : ℂ)))
    rw [hw2, hT₂]
  -- positivity and continuity on the physical interval force the multiplier to be one
  have hE : ContinuousOn (fun x => reflectionDOZZRatio γ μ x (reflectionBarR P γ x (B x) Z))
      (Ioo (γ / 2) (Q γ)) :=
    continuousOn_reflectionDOZZRatio γ μ hγ hγ2 hμ _ hBar
  have hEpos : ∀ x ∈ Ioo (γ / 2) (Q γ),
      0 < reflectionDOZZRatio γ μ x (reflectionBarR P γ x (B x) Z) :=
    fun x hx => reflectionDOZZRatio_pos γ μ x _ hγ hγ2 hμ ⟨hx.1, hx.2⟩
      (reflectionBarR_positive_finite P γ x hγ hγ2 ⟨hx.1, hx.2⟩ (B x) Z (hData x hx.1 hx.2)).1
  have hfE : ∀ x ∈ Ioo (γ / 2) (Q γ), ∀ᶠ y : ℝ in 𝓝[≠] x,
      F (y : ℂ) = (reflectionDOZZRatio γ μ y (reflectionBarR P γ y (B y) Z) : ℂ) :=
    fun x hx => reflectionQuotient_eventually_eq_ratio P hγ hγ2 hμ B Z hR₁α hx
  have hκ : κ = 1 :=
    quasiPeriod_multiplier_eq_one hh hFm (by positivity : (0 : ℝ) < γ / 2)
      (fun z hz => (hp₁ z hz).symm) hq (half_add_half_lt_Q hγ hγ2) hE hEpos hfE
  -- the two periods are rationally independent, so the quotient is constant
  have hirr : ∀ q : ℚ, (γ / 2) / (2 / γ) ≠ (q : ℝ) := by
    intro q hq'
    have hsq : γ ^ 2 = ((4 * q : ℚ) : ℝ) := by
      push_cast
      rw [← hq']
      field_simp
      norm_num
    exact hγirr ⟨4 * q, hsq.symm⟩
  have hp₂ : ∀ z ∈ horizontalStrip (min h₁ h₂),
      (fun w => F (w + ((2 / γ : ℝ) : ℂ))) =ᶠ[𝓝[≠] z] F := by
    intro z hz
    filter_upwards [hq z hz] with w hw
    rw [hw, hκ, one_mul]
  obtain ⟨c₀, hc₀, -⟩ := meromorphicOn_strip_constant_of_dense_periods (min h₁ h₂) hh F hFm
    (γ / 2) (2 / γ) (by positivity) (by positivity) hirr hp₁ hp₂
  -- the endpoint normalizations identify the constant
  have hleft : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[<] (Q γ)) (𝓝[≠] ((Q γ : ℝ) : ℂ)) :=
    (tendsto_ofReal_nhdsNE (Q γ)).mono_left (nhdsWithin_mono _ fun y hy => ne_of_lt hy)
  have hconst : ∀ᶠ y : ℝ in 𝓝[<] (Q γ), F (y : ℂ) = c₀ :=
    hleft.eventually (hc₀ _ (ofReal_mem_horizontalStrip hh _))
  have hnum : Tendsto (fun y : ℝ => (reflectionR P γ μ y (B y) Z : ℂ)) (𝓝[<] (Q γ))
      (𝓝 (-1)) := by
    have h := (Complex.continuous_ofReal.tendsto (-1 : ℝ)).comp hEnd
    rw [Complex.ofReal_neg, Complex.ofReal_one] at h
    exact h
  have hden : Tendsto (fun y : ℝ => RD (y : ℂ)) (𝓝[<] (Q γ)) (𝓝 (-1)) :=
    (reflectionDOZZ_tendsto_Q hγ hγ2 hμ).comp hleft
  have hratio : Tendsto (fun y : ℝ => F (y : ℂ)) (𝓝[<] (Q γ)) (𝓝 1) := by
    have h := hnum.div hden (by norm_num)
    rw [show ((-1 : ℂ) / -1) = 1 by norm_num] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hQ] with y hy
    show (reflectionR P γ μ y (B y) Z : ℂ) / RD y = R₁ y / RD y
    rw [hR₁α y hy.1 hy.2]
  have hc₁ : c₀ = 1 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' (hconst.mono fun y hy => hy.symm)) hratio
  -- equality off the poles, by continuity of both coefficients
  have hone : ∀ᶠ y : ℝ in 𝓝[≠] α, F (y : ℂ) = 1 := by
    have h := (tendsto_ofReal_nhdsNE α).eventually (hc₀ _ (ofReal_mem_horizontalStrip hh α))
    simpa only [hc₁] using h
  have heq : ∀ᶠ y : ℝ in 𝓝[≠] α, (reflectionR P γ μ y (B y) Z : ℂ) = RD (y : ℂ) := by
    filter_upwards [hone, reflectionPoleFree_eventually_nhdsNE hγ α,
      nhdsWithin_le_nhds (Ioo_mem_nhds hα.1 hα.2)] with y hy hpole hyI
    have hne := reflectionDOZZ_ofReal_ne_zero γ μ y hγ hγ2 hμ ⟨hyI.1, hyI.2⟩ hpole
    rw [← hR₁α y hyI.1 hyI.2]
    exact (div_eq_one_iff_eq hne).mp hy
  have hcont₁ : ContinuousAt (fun y : ℝ => (reflectionR P γ μ y (B y) Z : ℂ)) α :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_reflectionR_formula hγ hμ hα hPole
      (hBar.continuousAt (Ioo_mem_nhds hα.1 hα.2)))
  have hcont₂ := continuousAt_reflectionDOZZ_ofReal hγ hγ2 hμ hα hPole
  exact tendsto_nhds_unique ((hcont₁.tendsto.mono_left nhdsWithin_le_nhds).congr' heq)
    (hcont₂.tendsto.mono_left nhdsWithin_le_nhds)

/-- The positive integers form a closed subset of the reals. -/
theorem isClosed_range_natCast_succ : IsClosed (Set.range fun n : ℕ => ((n + 1 : ℕ) : ℝ)) := by
  have h := Nat.isClosedEmbedding_coe_real.isClosedMap (Set.range fun n : ℕ => n + 1)
    (isClosed_discrete _)
  rwa [← Set.range_comp] at h

/-- The reflection exponent is continuous in the coupling constant at a fixed charge. -/
theorem continuousAt_reflectionExponent_gamma {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (α : ℝ) :
    ContinuousAt (fun γ : ℝ => reflectionExponent γ α) γ₀ := by
  unfold reflectionExponent Q
  exact (continuousAt_const.mul (((continuousAt_const.div continuousAt_id hγ₀.ne').add
    (continuousAt_id.div_const 2)).sub continuousAt_const)).div continuousAt_id hγ₀.ne'

/-- Freedom from reflection poles is an open condition on the coupling constant. -/
theorem reflectionPoleFree_eventually_nhds_gamma {γ₀ α : ℝ} (hγ₀ : 0 < γ₀)
    (hPole : ReflectionPoleFree γ₀ α) : ∀ᶠ γ in 𝓝 γ₀, ReflectionPoleFree γ α := by
  have hmem : reflectionExponent γ₀ α ∈ (Set.range fun n : ℕ => ((n + 1 : ℕ) : ℝ))ᶜ := by
    rintro ⟨n, hn⟩
    exact hPole n hn.symm
  filter_upwards [(continuousAt_reflectionExponent_gamma hγ₀ α).preimage_mem_nhds
    (isClosed_range_natCast_succ.isOpen_compl.mem_nhds hmem)] with γ hγ n hn
  exact hγ ⟨n, hn.symm⟩

/-- Physicality of a fixed charge is an open condition on the coupling constant. -/
theorem eventually_physical_gamma {γ₀ α : ℝ} (hγ₀ : 0 < γ₀) (hγ₀2 : γ₀ < 2)
    (hα : γ₀ / 2 < α ∧ α < Q γ₀) :
    ∀ᶠ γ in 𝓝 γ₀, 0 < γ ∧ γ < 2 ∧ γ / 2 < α ∧ α < Q γ := by
  have hQ : ContinuousAt (fun γ : ℝ => Q γ) γ₀ := by
    unfold Q
    exact (continuousAt_const.div continuousAt_id hγ₀.ne').add (continuousAt_id.div_const 2)
  filter_upwards [lt_mem_nhds hγ₀, gt_mem_nhds hγ₀2,
    (continuousAt_id.div_const 2).eventually_lt continuousAt_const hα.1,
    continuousAt_const.eventually_lt hQ hα.2] with γ h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

/-- The DOZZ base is continuous in the coupling constant on `(0, 2)`. -/
theorem continuousAt_dozzBase_gamma {γ₀ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀2 : γ₀ < 2) (μ : ℝ) :
    ContinuousAt (fun γ : ℝ => dozzBase γ μ) γ₀ := by
  have heq : (fun γ : ℝ => dozzBase γ μ) = fun γ : ℝ =>
      Real.pi * μ * (Real.Gamma (γ ^ 2 / 4) / Real.Gamma (1 - γ ^ 2 / 4)) := by
    funext γ
    rw [dozzBase, lFun_gammaSq_real, Complex.ofReal_re]
  rw [heq]
  have hq : 0 < γ₀ ^ 2 / 4 := by positivity
  have hq1 : 0 < 1 - γ₀ ^ 2 / 4 := by
    linarith only [pow_lt_pow_left₀ hγ₀2 hγ₀.le two_ne_zero]
  have hG1 : ContinuousAt (fun γ : ℝ => Real.Gamma (γ ^ 2 / 4)) γ₀ := by
    have hs : ∀ m : ℕ, γ₀ ^ 2 / 4 ≠ -m := fun m hm => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith only [hm, this, hq]
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt
      (by fun_prop)
  have hG2 : ContinuousAt (fun γ : ℝ => Real.Gamma (1 - γ ^ 2 / 4)) γ₀ := by
    have hs : ∀ m : ℕ, 1 - γ₀ ^ 2 / 4 ≠ -m := fun m hm => by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith only [hm, this, hq1]
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt
      (by fun_prop)
  exact continuousAt_const.mul (hG1.div hG2 (Real.Gamma_pos_of_pos hq1).ne')

/-- Off the Gamma poles, the DOZZ coefficient at a fixed real charge is continuous in the
coupling constant. -/
theorem continuousAt_reflectionDOZZ_gamma {γ₀ μ α : ℝ} (hγ₀ : 0 < γ₀) (hγ₀2 : γ₀ < 2)
    (hμ : 0 < μ) (hα : γ₀ / 2 < α ∧ α < Q γ₀) (hPole : ReflectionPoleFree γ₀ α) :
    ContinuousAt (fun γ : ℝ => reflectionDOZZ γ μ (α : ℂ)) γ₀ := by
  have hev : (fun γ : ℝ =>
      ((-(dozzBase γ μ ^ reflectionExponent γ α) *
        (Real.Gamma (-(γ * (Q γ - α) / 2)) / Real.Gamma (γ * (Q γ - α) / 2)) *
        (Real.Gamma (-reflectionExponent γ α) / Real.Gamma (reflectionExponent γ α)) : ℝ) : ℂ))
      =ᶠ[𝓝 γ₀] fun γ : ℝ => reflectionDOZZ γ μ (α : ℂ) := by
    filter_upwards [Ioo_mem_nhds hγ₀ hγ₀2] with γ hγ
    exact (reflectionDOZZ_ofReal γ μ α hγ.1 hγ.2 hμ).symm
  refine ContinuousAt.congr ?_ hev
  apply Complex.continuous_ofReal.continuousAt.comp
  have hp := continuousAt_reflectionExponent_gamma hγ₀ α
  have ht : ContinuousAt (fun γ : ℝ => γ * (Q γ - α) / 2) γ₀ := by
    unfold Q
    exact (continuousAt_id.mul (((continuousAt_const.div continuousAt_id hγ₀.ne').add
      (continuousAt_id.div_const 2)).sub continuousAt_const)).div_const 2
  have hpos := (reflectionExponent_in_subcritical_range γ₀ α hγ₀ hα).2.1
  have htα := reflectionGammaArg_mem_Ioo hγ₀ hα
  have hbase : 0 < dozzBase γ₀ μ := dozzBase_pos hγ₀ hγ₀2 hμ
  have hG1 : ContinuousAt (fun γ : ℝ => Real.Gamma (-(γ * (Q γ - α) / 2))) γ₀ := by
    have hs : ∀ m : ℕ, -(γ₀ * (Q γ₀ - α) / 2) ≠ -m := by
      intro m hm
      have hm' : γ₀ * (Q γ₀ - α) / 2 = m := by linarith only [hm]
      rcases Nat.eq_zero_or_pos m with h0 | hm0
      · rw [h0, Nat.cast_zero] at hm'; linarith only [hm', htα.1]
      · have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
        linarith only [hm', this, htα.2]
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt ht.neg
  have hG2 : ContinuousAt (fun γ : ℝ => Real.Gamma (γ * (Q γ - α) / 2)) γ₀ := by
    have hs : ∀ m : ℕ, γ₀ * (Q γ₀ - α) / 2 ≠ -m := by
      intro m hm
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith only [hm, this, htα.1]
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt ht
  have hG3 : ContinuousAt (fun γ : ℝ => Real.Gamma (-reflectionExponent γ α)) γ₀ := by
    have hs : ∀ m : ℕ, -(reflectionExponent γ₀ α) ≠ -m := by
      intro m hm
      have hpm : reflectionExponent γ₀ α = m := by linarith only [hm]
      rcases Nat.eq_zero_or_pos m with h0 | hm0
      · rw [h0, Nat.cast_zero] at hpm; linarith only [hpm, hpos]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm0
        exact hPole k (by rw [hpm]; push_cast; ring)
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt hp.neg
  have hG4 : ContinuousAt (fun γ : ℝ => Real.Gamma (reflectionExponent γ α)) γ₀ := by
    have hs : ∀ m : ℕ, reflectionExponent γ₀ α ≠ -m := by
      intro m hm
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith only [hm, this, hpos]
    exact ContinuousAt.comp (g := Real.Gamma) (Real.differentiableAt_Gamma hs).continuousAt hp
  have hpowb : ContinuousAt (fun γ : ℝ => dozzBase γ μ ^ reflectionExponent γ α) γ₀ :=
    (continuousAt_dozzBase_gamma hγ₀ hγ₀2 μ).rpow hp (Or.inl hbase.ne')
  have hne2 : Real.Gamma (γ₀ * (Q γ₀ - α) / 2) ≠ 0 := (Real.Gamma_pos_of_pos htα.1).ne'
  have hne4 : Real.Gamma (reflectionExponent γ₀ α) ≠ 0 := (Real.Gamma_pos_of_pos hpos).ne'
  exact (hpowb.neg.mul (hG1.div hG2 hne2)).mul (hG3.div hG4 hne4)

/-- Couplings with irrational square accumulate at every positive `γ₀`: along irrational
`x → γ₀²`, the square roots tend to `γ₀`. -/
theorem tendsto_sqrt_nhdsWithin_irrational {γ₀ : ℝ} (hγ₀ : 0 < γ₀) :
    Tendsto Real.sqrt (𝓝[{x : ℝ | Irrational x}] (γ₀ ^ 2)) (𝓝 γ₀) := by
  have h := (Real.continuous_sqrt.tendsto (γ₀ ^ 2)).mono_left
    (nhdsWithin_le_nhds (s := {x : ℝ | Irrational x}))
  rwa [Real.sqrt_sq hγ₀.le] at h

/-- **Continuity extension in `γ`.** If the probabilistic coefficient along a witness family is
continuous on compact pole-free physical sets of `(γ, α)`
(`DOZZ.reflection_endpoint_and_gamma_continuity`), and equals the DOZZ coefficient whenever `γ²`
is irrational, then it equals the DOZZ coefficient at every pole-free physical pair. -/
theorem reflectionR_eq_reflectionDOZZ_of_irrational_of_continuousOn
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : ℝ) (hμ : 0 < μ)
    (B : ℝ → ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hirr : ∀ γ : ℝ, 0 < γ → γ < 2 → Irrational (γ ^ 2) → ∀ α : ℝ, γ / 2 < α → α < Q γ →
      ReflectionPoleFree γ α →
        (reflectionR P γ μ α (B γ α) (Z γ) : ℂ) = reflectionDOZZ γ μ (α : ℂ))
    (hcont : ∀ K : Set (ℝ × ℝ), IsCompact K →
      (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) →
        (∀ q ∈ K, ReflectionPoleFree q.1 q.2) →
          ContinuousOn (fun q => reflectionR P q.1 μ q.2 (B q.1 q.2) (Z q.1)) K)
    {γ₀ α₀ : ℝ} (hγ₀ : 0 < γ₀) (hγ₀2 : γ₀ < 2) (hα₀ : γ₀ / 2 < α₀ ∧ α₀ < Q γ₀)
    (hPole : ReflectionPoleFree γ₀ α₀) :
    (reflectionR P γ₀ μ α₀ (B γ₀ α₀) (Z γ₀) : ℂ) = reflectionDOZZ γ₀ μ (α₀ : ℂ) := by
  have hgood : ∀ᶠ γ in 𝓝 γ₀,
      (0 < γ ∧ γ < 2 ∧ γ / 2 < α₀ ∧ α₀ < Q γ) ∧ ReflectionPoleFree γ α₀ :=
    (eventually_physical_gamma hγ₀ hγ₀2 hα₀).and (reflectionPoleFree_eventually_nhds_gamma hγ₀ hPole)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hgood
  have hKgood : ∀ q ∈ Icc (γ₀ - δ / 2) (γ₀ + δ / 2) ×ˢ ({α₀} : Set ℝ),
      (0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) ∧ ReflectionPoleFree q.1 q.2 := by
    intro q hq
    have hq2 : q.2 = α₀ := hq.2
    have hdist : dist q.1 γ₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith only [hq.1.1, hq.1.2, hδ]
    rw [hq2]
    exact hball hdist
  have hC := hcont _ (isCompact_Icc.prod isCompact_singleton) (fun q hq => (hKgood q hq).1)
    (fun q hq => (hKgood q hq).2)
  have hRcont : ContinuousAt (fun γ => reflectionR P γ μ α₀ (B γ α₀) (Z γ)) γ₀ := by
    have hmaps : MapsTo (fun γ : ℝ => (γ, α₀)) (Icc (γ₀ - δ / 2) (γ₀ + δ / 2))
        (Icc (γ₀ - δ / 2) (γ₀ + δ / 2) ×ˢ ({α₀} : Set ℝ)) :=
      fun γ hγ => ⟨hγ, rfl⟩
    have hon : ContinuousOn ((fun q : ℝ × ℝ => reflectionR P q.1 μ q.2 (B q.1 q.2) (Z q.1)) ∘
        fun γ : ℝ => (γ, α₀)) (Icc (γ₀ - δ / 2) (γ₀ + δ / 2)) :=
      hC.comp (Continuous.prodMk_left α₀).continuousOn hmaps
    exact hon.continuousAt (Icc_mem_nhds (by linarith only [hδ]) (by linarith only [hδ]))
  have hDcont := continuousAt_reflectionDOZZ_gamma (μ := μ) hγ₀ hγ₀2 hμ hα₀ hPole
  have hne : NeBot (𝓝[{x : ℝ | Irrational x}] (γ₀ ^ 2)) :=
    mem_closure_iff_nhdsWithin_neBot.1 (dense_irrational _)
  have hsqrt := tendsto_sqrt_nhdsWithin_irrational hγ₀
  have hpos : ∀ᶠ x in 𝓝[{x : ℝ | Irrational x}] (γ₀ ^ 2), 0 < x :=
    nhdsWithin_le_nhds (lt_mem_nhds (by positivity))
  have hev : ∀ᶠ x in 𝓝[{x : ℝ | Irrational x}] (γ₀ ^ 2),
      (reflectionR P (Real.sqrt x) μ α₀ (B (Real.sqrt x) α₀) (Z (Real.sqrt x)) : ℂ) =
        reflectionDOZZ (Real.sqrt x) μ (α₀ : ℂ) := by
    filter_upwards [hsqrt.eventually hgood, self_mem_nhdsWithin, hpos] with x hx hirrx hx0
    have hirr' : Irrational (Real.sqrt x ^ 2) := by
      rw [Real.sq_sqrt hx0.le]
      exact hirrx
    exact hirr _ hx.1.1 hx.1.2.1 hirr' α₀ hx.1.2.2.1 hx.1.2.2.2 hx.2
  have h1 : Tendsto (fun x => (reflectionR P (Real.sqrt x) μ α₀ (B (Real.sqrt x) α₀)
      (Z (Real.sqrt x)) : ℂ)) (𝓝[{x : ℝ | Irrational x}] (γ₀ ^ 2))
      (𝓝 (reflectionR P γ₀ μ α₀ (B γ₀ α₀) (Z γ₀) : ℂ)) :=
    (Complex.continuous_ofReal.continuousAt.comp hRcont).tendsto.comp hsqrt
  have h2 : Tendsto (fun x => reflectionDOZZ (Real.sqrt x) μ (α₀ : ℂ))
      (𝓝[{x : ℝ | Irrational x}] (γ₀ ^ 2)) (𝓝 (reflectionDOZZ γ₀ μ (α₀ : ℂ))) :=
    hDcont.tendsto.comp hsqrt
  exact tendsto_nhds_unique (h1.congr' hev) h2

/-- Continuity on compact physical sets of `(γ, α)` gives continuity of every fixed-coupling slice
on the physical interval. -/
theorem continuousOn_slice_of_compact_physical {f : ℝ × ℝ → ℝ} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2)
    (hf : ∀ K : Set (ℝ × ℝ), IsCompact K →
      (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) → ContinuousOn f K) :
    ContinuousOn (fun a => f (γ, a)) (Ioo (γ / 2) (Q γ)) := by
  intro a ha
  obtain ⟨m, hm, hm1, hm2⟩ : ∃ m : ℝ, 0 < m ∧ m ≤ a - γ / 2 ∧ m ≤ Q γ - a :=
    ⟨min (a - γ / 2) (Q γ - a), lt_min (sub_pos.mpr ha.1) (sub_pos.mpr ha.2), min_le_left _ _,
      min_le_right _ _⟩
  have hsub : Icc (a - m / 2) (a + m / 2) ⊆ Ioo (γ / 2) (Q γ) := fun b hb =>
    ⟨by linarith only [hb.1, hm1, hm], by linarith only [hb.2, hm2, hm]⟩
  have hKphys : ∀ q ∈ ({γ} : Set ℝ) ×ˢ Icc (a - m / 2) (a + m / 2),
      0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1 := by
    intro q hq
    have h1 : q.1 = γ := hq.1
    have h2 := hsub hq.2
    rw [h1]
    exact ⟨hγ, hγ2, h2.1, h2.2⟩
  have hon := hf _ (isCompact_singleton.prod isCompact_Icc) hKphys
  have hslice : ContinuousOn (fun b => f (γ, b)) (Icc (a - m / 2) (a + m / 2)) :=
    hon.comp (Continuous.prodMk_right γ).continuousOn fun b hb => ⟨rfl, hb⟩
  exact (hslice.continuousAt (Icc_mem_nhds (by linarith only [hm]) (by linarith only [hm]))).continuousWithinAt

/-- **`R = R^DOZZ` off the poles**, from the statements
`DOZZ.reflectionR_first_shift_meromorphic`, `DOZZ.reflectionR_dual_shift_unknown_constant` and
`DOZZ.reflection_endpoint_and_gamma_continuity` (taken verbatim, at universe `0`). -/
theorem reflection_Rtheor_off_poles_of_shift_equations
    (hFirst : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
        (M : Ω → Measure ℂ) (γ μ : ℝ)
        (_ : 0 < γ) (_ : γ < 2) (_ : 0 < μ)
        (_ : IsEquatorGFF P X) (_ : IsGMCOf P X γ M),
        ∃ B : ℝ → Ω → BrownianPath ×
            BrownianPath,
          ∃ Z : Ω → Measure ℝ,
            IsSourceLateralProjection P X γ M Z ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                IsReflectionData P γ α (B α) Z) ∧
                ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
                  MeromorphicOn R {z | |z.im| < h} ∧
                  (∀ α : ℝ, γ / 2 < α → α < Q γ →
                    R (α : ℂ) =
                      (reflectionR P γ μ α (B α) Z : ℂ)) ∧
                  ∀ᶠ z in codiscrete ℂ,
                    R (z - γ / 2) =
                      -(μ * Real.pi : ℂ) * R z /
                        (lFun (-((γ : ℂ) ^ 2) / 4) *
                          lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                          lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)))
    (hDual : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
        (M : Ω → Measure ℂ) (γ μ : ℝ)
        (_ : 0 < γ) (_ : γ < 2) (_ : Irrational (γ ^ 2)) (_ : 0 < μ)
        (_ : IsEquatorGFF P X) (_ : IsGMCOf P X γ M),
        ∃ B : ℝ → Ω → BrownianPath ×
            BrownianPath,
          ∃ Z : Ω → Measure ℝ,
            IsSourceLateralProjection P X γ M Z ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                IsReflectionData P γ α (B α) Z) ∧
                ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
                  MeromorphicOn R {z | |z.im| < h} ∧
                  (∀ α : ℝ, γ / 2 < α → α < Q γ →
                    R (α : ℂ) =
                      (reflectionR P γ μ α (B α) Z : ℂ)) ∧
                  ∃ cγ : ℂ, cγ ≠ 0 ∧
                    cγ = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧
                    ∀ᶠ z in codiscrete ℂ,
                      R z = -cγ * R (z + 2 / γ) /
                        (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
                          lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)))
    (hCont : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        (X : Ω → Distr) (M : ℝ → Ω → Measure ℂ) (_ : IsEquatorGFF P X)
        (μ : ℝ) (_ : 0 < μ)
        (_ : ∀ γ, 0 < γ → γ < 2 → IsGMCOf P X γ (M γ)),
        ∃ B : ℝ → ℝ → Ω →
            BrownianPath × BrownianPath,
          ∃ Z : ℝ → Ω → Measure ℝ,
            (∀ γ, 0 < γ → γ < 2 →
              IsSourceLateralProjection P X γ (M γ) (Z γ) ∧
                ∀ α, γ / 2 < α → α < Q γ →
                  IsReflectionData P γ α (B γ α) (Z γ)) ∧
              (∀ γ, 0 < γ → γ < 2 →
                Tendsto (fun α : ℝ =>
                  reflectionBarR P γ α (B γ α) (Z γ))
                  (𝓝[<] (Q γ)) (𝓝 1) ∧
                Tendsto (fun α : ℝ =>
                  reflectionR P γ μ α (B γ α) (Z γ))
                  (𝓝[<] (Q γ)) (𝓝 (-1))) ∧
              (∀ K : Set (ℝ × ℝ), IsCompact K →
                (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧ q.1 / 2 < q.2 ∧ q.2 < Q q.1) →
                  ContinuousOn (fun q => reflectionBarR P q.1 q.2 (B q.1 q.2) (Z q.1)) K ∧
                    ((∀ q ∈ K, ReflectionPoleFree q.1 q.2) →
                      ContinuousOn (fun q => reflectionR P q.1 μ q.2 (B q.1 q.2) (Z q.1)) K)) ∧
              ∀ K : Set (ℝ × (Fin 3 → ℝ)), IsCompact K →
                (∀ q ∈ K, 0 < q.1 ∧ q.1 < 2 ∧
                  ExtendedSeiberg3 q.1 (q.2 0) (q.2 1) (q.2 2)) →
                  ContinuousOn (fun q => unitVolumeStructureConstant P (M q.1) q.1
                    (q.2 0) (q.2 1) (q.2 2)) K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ α : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : γ / 2 < α ∧ α < Q γ) (hPole : ReflectionPoleFree γ α)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    (reflectionR P γ μ α B Z : ℂ) = reflectionDOZZ γ μ (α : ℂ) := by
  -- a reference equator GFF with its GMC family
  obtain ⟨-, Ω₀, _, P₀, X₀, -, hX₀, -⟩ := dozz_existence 1 one_pos one_lt_two
  have hMex : ∀ g : ℝ, ∃ M : Ω₀ → Measure ℂ, 0 < g → g < 2 → IsGMCOf P₀ X₀ g M := by
    intro g
    by_cases hg : 0 < g ∧ g < 2
    · obtain ⟨-, M, -, hM⟩ := equatorGFF_circle_average_GMC_exists P₀ X₀ hX₀ g hg.1 hg.2
      exact ⟨M, fun _ _ => hM⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hg⟩
  choose M₀ hM₀ using hMex
  -- endpoint and continuity data (`hCont`) along one witness family
  obtain ⟨B₀, Z₀, hData₀, hEnd₀, hCont₀, -⟩ := hCont P₀ X₀ M₀ hX₀ μ hμ hM₀
  rw [reflectionR_eq_of_isReflectionData P P₀ γ μ α B Z (B₀ γ α) (Z₀ γ) hData
    ((hData₀ γ hγ hγ2).2 α hα.1 hα.2)]
  -- continuity in the coupling reduces to irrational `γ²`
  refine reflectionR_eq_reflectionDOZZ_of_irrational_of_continuousOn P₀ μ hμ B₀ Z₀ ?_
    (fun K hK hKphys hKpole => (hCont₀ K hK hKphys).2 hKpole) hγ hγ2 hα hPole
  intro g hg hg2 hirr a ha1 ha2 hPole'
  have hD₀ : ∀ b : ℝ, g / 2 < b → b < Q g → IsReflectionData P₀ g b (B₀ g b) (Z₀ g) :=
    (hData₀ g hg hg2).2
  -- the two shift laws (`hFirst`, `hDual`) for interpolants along their own witnesses
  obtain ⟨B₁, Z₁, -, hD₁, h₁, hh₁, R₁, hR₁, hR₁α, hshift₁⟩ :=
    hFirst P₀ X₀ (M₀ g) g μ hg hg2 hμ hX₀ (hM₀ g hg hg2)
  obtain ⟨B₂, Z₂, -, hD₂, h₂, hh₂, R₂, hR₂, hR₂α, c, -, -, hshift₂⟩ :=
    hDual P₀ X₀ (M₀ g) g μ hg hg2 hirr hμ hX₀ (hM₀ g hg hg2)
  -- witness independence moves both interpolants onto the reference family
  have hR₁' : ∀ b : ℝ, g / 2 < b → b < Q g →
      R₁ (b : ℂ) = (reflectionR P₀ g μ b (B₀ g b) (Z₀ g) : ℂ) := fun b h1 h2 => by
    rw [hR₁α b h1 h2, reflectionR_eq_of_isReflectionData P₀ P₀ g μ b (B₁ b) Z₁ (B₀ g b) (Z₀ g)
      (hD₁ b h1 h2) (hD₀ b h1 h2)]
  have hR₂' : ∀ b : ℝ, g / 2 < b → b < Q g →
      R₂ (b : ℂ) = (reflectionR P₀ g μ b (B₀ g b) (Z₀ g) : ℂ) := fun b h1 h2 => by
    rw [hR₂α b h1 h2, reflectionR_eq_of_isReflectionData P₀ P₀ g μ b (B₂ b) Z₂ (B₀ g b) (Z₀ g)
      (hD₂ b h1 h2) (hD₀ b h1 h2)]
  have hBar : ContinuousOn (fun b => reflectionBarR P₀ g b (B₀ g b) (Z₀ g)) (Ioo (g / 2) (Q g)) :=
    continuousOn_slice_of_compact_physical
      (f := fun q => reflectionBarR P₀ q.1 q.2 (B₀ q.1 q.2) (Z₀ q.1)) hg hg2
      (fun K hK hKphys => (hCont₀ K hK hKphys).1)
  exact reflectionR_eq_reflectionDOZZ_of_shifts P₀ g μ hg hg2 hirr hμ (B₀ g) (Z₀ g) hD₀ hh₁ hh₂
    hR₁ hR₂ hR₁' hR₂' hshift₁ hshift₂ hBar (hEnd₀ g hg hg2).2 ⟨ha1, ha2⟩ hPole'


end DOZZ.Proofs

end
