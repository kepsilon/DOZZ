/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelScores

/-!
# Parameter derivative of the conditioned-kernel score

The ordered coupling needs the score to be increasing and one-Lipschitz in its drift parameter.
This file proves the derivative formula and its pointwise bounds away from the zero-parameter
limit.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- The derivative of `a ↦ a coth (a*y)` in the positive parameter regime. -/
noncomputable def conditionedKernelScoreParameterSlope (a y : ℝ) : ℝ :=
  (Real.sinh (a * y) * Real.cosh (a * y) - a * y) / Real.sinh (a * y) ^ 2

/-- Derivative of the conditioned-kernel score in its parameter. -/
theorem hasDerivAt_conditionedKernelScore_parameter
    {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    HasDerivAt (fun x : ℝ => conditionedKernelScore x y)
      (conditionedKernelScoreParameterSlope a y) a := by
  have harg : HasDerivAt (fun x : ℝ => x * y) y a := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id a).mul_const y
  have hcosh := (Real.hasDerivAt_cosh (a * y)).comp a harg
  have hsinh := (Real.hasDerivAt_sinh (a * y)).comp a harg
  have hcosh' : HasDerivAt (fun x : ℝ => Real.cosh (x * y))
      (Real.sinh (a * y) * y) a := by
    convert hcosh using 1
    · funext x
      rfl
  have hsinh' : HasDerivAt (fun x : ℝ => Real.sinh (x * y))
      (Real.cosh (a * y) * y) a := by
    convert hsinh using 1
    funext x
    rfl
  have hnum := (hasDerivAt_id a).mul hcosh'
  have hsinh_pos : 0 < Real.sinh (a * y) :=
    Real.sinh_pos_iff.mpr (mul_pos ha hy)
  have hquot := hnum.div hsinh' hsinh_pos.ne'
  have hquot' : HasDerivAt (fun x : ℝ =>
      x * Real.cosh (x * y) / Real.sinh (x * y))
      (((Real.cosh (a * y) + a * (Real.sinh (a * y) * y)) * Real.sinh (a * y) -
        a * Real.cosh (a * y) * (Real.cosh (a * y) * y)) /
        Real.sinh (a * y) ^ 2) a := by
    convert hquot using 1
    · funext x
      rfl
    · simp [id_eq]
  have htrig : Real.cosh (a * y) ^ 2 - Real.sinh (a * y) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (a * y)
  have hderiv :
      ((Real.cosh (a * y) + a * (Real.sinh (a * y) * y)) * Real.sinh (a * y) -
        a * Real.cosh (a * y) * (Real.cosh (a * y) * y)) /
        Real.sinh (a * y) ^ 2 =
      conditionedKernelScoreParameterSlope a y := by
    dsimp [conditionedKernelScoreParameterSlope]
    field_simp [hsinh_pos.ne']
    have htrig' : Real.sinh (a * y) ^ 2 - Real.cosh (a * y) ^ 2 = -1 := by
      nlinarith [htrig]
    calc
      (Real.sinh (a * y) * (Real.cosh (a * y) + a * y * Real.sinh (a * y)) -
          a * y * Real.cosh (a * y) ^ 2) =
        Real.cosh (a * y) * Real.sinh (a * y) +
          a * y * (Real.sinh (a * y) ^ 2 - Real.cosh (a * y) ^ 2) := by ring
      _ = Real.cosh (a * y) * Real.sinh (a * y) - a * y := by rw [htrig']; ring
  change HasDerivAt (fun x : ℝ => x * Real.cosh (x * y) / Real.sinh (x * y))
    (conditionedKernelScoreParameterSlope a y) a
  convert hquot' using 1
  exact hderiv.symm

/-- The score parameter derivative lies between zero and one. -/
theorem conditionedKernelScoreParameterSlope_bounds
    {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    0 ≤ conditionedKernelScoreParameterSlope a y ∧
      conditionedKernelScoreParameterSlope a y ≤ 1 := by
  let u : ℝ := a * y
  have hu : 0 < u := mul_pos ha hy
  have hs : 0 < Real.sinh u := Real.sinh_pos_iff.mpr hu
  have hcosh : 1 ≤ Real.cosh u := Real.one_le_cosh u
  have hself : u ≤ Real.sinh u := Real.self_le_sinh_iff.mpr hu.le
  have hlow : 0 ≤ Real.sinh u * Real.cosh u - u := by
    have hprod : Real.sinh u ≤ Real.sinh u * Real.cosh u := by
      nlinarith [mul_nonneg (le_of_lt hs) (sub_nonneg.mpr hcosh)]
    linarith
  have hexp : 1 - Real.exp (-2 * u) ≤ 2 * u := by
    have h := Real.add_one_le_exp (-2 * u)
    nlinarith
  have hupperNumerator : Real.sinh u * Real.cosh u - u ≤ Real.sinh u ^ 2 := by
    have hcs : Real.cosh u - Real.sinh u = Real.exp (-u) := Real.cosh_sub_sinh u
    have hprod : Real.sinh u * Real.exp (-u) = (1 - Real.exp (-2 * u)) / 2 := by
      rw [Real.sinh_eq]
      calc
        (Real.exp u - Real.exp (-u)) / 2 * Real.exp (-u) =
            (Real.exp u * Real.exp (-u) - Real.exp (-u) * Real.exp (-u)) / 2 := by ring
        _ = (Real.exp (u + -u) - Real.exp (-u + -u)) / 2 := by
          rw [← Real.exp_add u (-u), ← Real.exp_add (-u) (-u)]
        _ = (1 - Real.exp (-2 * u)) / 2 := by
          congr 1
          rw [show u + -u = 0 by ring, Real.exp_zero,
            show -u + -u = -2 * u by ring]
    have hbound : Real.sinh u * Real.exp (-u) ≤ u := by
      rw [hprod]
      linarith
    have hcsMul := congrArg (fun z => Real.sinh u * z) hcs
    nlinarith [hcsMul, hbound]
  have hden : 0 < Real.sinh u ^ 2 := sq_pos_of_pos hs
  constructor
  · dsimp [conditionedKernelScoreParameterSlope, u]
    exact div_nonneg hlow (le_of_lt hden)
  · dsimp [conditionedKernelScoreParameterSlope, u]
    exact (div_le_one hden).2 hupperNumerator

/-- The conditioned-kernel score has the continuous zero-parameter limit `1/y`. -/
theorem conditionedKernelScore_tendsto_zero_parameter
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun a : ℝ => conditionedKernelScore a y)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / y)) := by
  have hxy : Tendsto (fun a : ℝ => a * y) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a * y) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hden_ne : ∀ᶠ a : ℝ in 𝓝[≠] (0 : ℝ), a * y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : a ≠ 0 := by simpa using ha
    exact mul_ne_zero ha0 hy.ne'
  have hratio : Tendsto (fun a : ℝ => Real.sinh (a * y) / (a * y))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hden_ne).mp
      (Real.isEquivalent_sinh.comp_tendsto hxy)
  have hcosh : Tendsto (fun a : ℝ => Real.cosh (a * y))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_cosh.tendsto (0 : ℝ)).comp hxy
    simpa [Function.comp_def] using h
  have hscaled : Tendsto
      (fun a : ℝ => Real.cosh (a * y) / (Real.sinh (a * y) / (a * y)) * (1 / y))
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / y)) := by
    have h := (hcosh.div hratio (by norm_num)).mul_const (1 / y)
    simpa using h
  have heq : (fun a : ℝ => conditionedKernelScore a y) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun a => Real.cosh (a * y) / (Real.sinh (a * y) / (a * y)) * (1 / y)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : a ≠ 0 := by simpa using ha
    have hsne : Real.sinh (a * y) ≠ 0 :=
      Real.sinh_ne_zero.mpr (mul_ne_zero ha0 hy.ne')
    dsimp [conditionedKernelScore]
    field_simp [ha0, hy.ne', hsne]
  exact hscaled.congr' heq.symm

/-- Increasing the positive parameter increases the score by at most the parameter increment. -/
theorem conditionedKernelScore_increment_bounds
    {a b y : ℝ} (ha : 0 < a) (hy : 0 < y) (hab : a ≤ b) :
    0 ≤ conditionedKernelScore b y - conditionedKernelScore a y ∧
      conditionedKernelScore b y - conditionedKernelScore a y ≤ b - a := by
  by_cases hEq : a = b
  · subst b
    simp
  have hablt : a < b := lt_of_le_of_ne hab hEq
  let f : ℝ → ℝ := fun x => conditionedKernelScore x y
  let f' : ℝ → ℝ := fun x => conditionedKernelScoreParameterSlope x y
  have hfc : ContinuousOn f (Set.Icc a b) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le ha hx.1
    have hsne : Real.sinh (x * y) ≠ 0 :=
      Real.sinh_ne_zero.mpr (mul_ne_zero hxpos.ne' hy.ne')
    have hnum : ContinuousAt (fun z : ℝ => z * Real.cosh (z * y)) x := by fun_prop
    have hden : ContinuousAt (fun z : ℝ => Real.sinh (z * y)) x := by fun_prop
    have hcont := hnum.div hden hsne
    simpa [f, conditionedKernelScore, Pi.div_def] using hcont.continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x := by
    intro x hx
    have hxpos : 0 < x := lt_trans ha hx.1
    simpa [f, f'] using hasDerivAt_conditionedKernelScore_parameter hxpos hy
  obtain ⟨x, hx, hmean⟩ :=
    exists_hasDerivAt_eq_slope f f' hablt hfc hderiv
  have hbounds := conditionedKernelScoreParameterSlope_bounds
    (lt_trans ha hx.1) hy
  have hquotLo : 0 ≤ (conditionedKernelScore b y - conditionedKernelScore a y) / (b - a) := by
    rw [← hmean]
    exact hbounds.1
  have hquotHi : (conditionedKernelScore b y - conditionedKernelScore a y) / (b - a) ≤ 1 := by
    rw [← hmean]
    exact hbounds.2
  have hba : 0 < b - a := sub_pos.mpr hablt
  have hdiffLo : 0 ≤ conditionedKernelScore b y - conditionedKernelScore a y := by
    rcases (div_nonneg_iff.mp hquotLo) with ⟨hn, _⟩ | ⟨_, hd⟩
    · exact hn
    · have : 0 ≤ b - a := le_of_lt hba
      linarith
  have hdiffHi : conditionedKernelScore b y - conditionedKernelScore a y ≤ b - a :=
    by simpa only [one_mul] using (div_le_iff₀ hba).mp hquotHi
  exact ⟨hdiffLo, by simpa using hdiffHi⟩

/-- Combining state antitonicity with the one-Lipschitz parameter bound controls a mixed
parameter-and-state increment. This is the score estimate in the shifted-density comparison for
the upper quantile bound. -/
theorem conditionedKernelScore_mixed_increment_upper
    {a b y z : ℝ} (ha : 0 < a) (hy : 0 < y) (hyz : y ≤ z) (hab : a ≤ b) :
    conditionedKernelScore b z - conditionedKernelScore a y ≤ b - a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hstate : conditionedKernelScore b z ≤ conditionedKernelScore b y := by
    by_cases hyz' : y = z
    · simp [hyz']
    · have hyz'' : y < z := lt_of_le_of_ne hyz hyz'
      exact ((conditionedKernelScore_strictAntiOn_state hb)
        (Set.mem_Ioi.mpr hy) (Set.mem_Ioi.mpr (lt_of_lt_of_le hy hyz)) hyz'').le
  have hparam := conditionedKernelScore_increment_bounds ha hy hab
  linarith

end DOZZ.Proofs

end
