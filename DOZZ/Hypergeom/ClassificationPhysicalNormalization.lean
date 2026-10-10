/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationCoefficientRatio
public import DOZZ.Hypergeom.PhysicalRange
public import DOZZ.Hypergeom.ODE.ConnectionEndpointLimits

/-! The physical normalization from continuity at the regular puncture. -/

@[expose] public section

namespace DOZZ.Proofs

open Filter Set
open scoped Topology

private theorem real_open_unit_not_int {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    ∀ n : ℤ, x ≠ (n : ℝ) := by
  intro n hn
  have hnreal0 : (0 : ℝ) ≤ (n : ℝ) := by rw [← hn]; exact hx0.le
  have hnreal1 : (n : ℝ) < 1 := by rw [← hn]; exact hx1
  have hn0 : 0 ≤ n := by exact_mod_cast hnreal0
  have hn1 : n < 1 := by exact_mod_cast hnreal1
  have hnzero : n = 0 := by omega
  subst n
  exact hx0.ne' (by simpa using hn)

private theorem tendsto_real_positive_cpow_zero (c : ℝ) (hc : c < 1) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ (1 - (c : ℂ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
  let e : ℝ := 1 - c
  have he : 0 < e := by dsimp [e]; linarith
  have hreal : Tendsto (fun x : ℝ => x ^ e) F (nhds 0) := by
    have hid : Tendsto (fun x : ℝ => x) F (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : ℝ => e) F (nhds e) := tendsto_const_nhds
    have h := (Real.continuousAt_rpow (0, e) (Or.inr he)).tendsto.comp
      (hid.prodMk_nhds hconst)
    simpa [Function.comp_def, Real.zero_rpow he.ne'] using h
  have hnorm : (fun x : ℝ => ‖(x : ℂ) ^ (1 - (c : ℂ))‖) =ᶠ[F]
      (fun x : ℝ => x ^ e) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hbase : (x : ℂ) = (x : ℝ) := rfl
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [e, Complex.sub_re]
  rw [tendsto_congr' hnorm]
  exact hreal

/-- In the strict physical range, continuity at zero fixes the coefficient in
[KRV, (Fundrelation1)] to `T 0`. -/
theorem real_gauss_solution_physical_normalization
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (γ χ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hsum : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (T : ℂ → ℝ)
    (hT : IsRealGaussSolution (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) T)
    (hcont : ContinuousAt T 0) :
    ∀ z ∈ gaussCutPlane,
      T z = T 0 *
        (‖gaussFMinus H (gaussParameterA γ χ α₁ α₂ α₃)
          (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) z‖ ^ 2 +
        gaussCoefficientRatio (gaussParameterA γ χ α₁ α₂ α₃)
          (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) *
          ‖gaussFPlus H (gaussParameterA γ χ α₁ α₂ α₃)
            (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) z‖ ^ 2) := by
  let a := gaussParameterA γ χ α₁ α₂ α₃
  let b := gaussParameterB γ χ α₁ α₂ α₃
  let c := gaussParameterC γ χ α₁
  obtain ⟨ha, hab, hbc, hc1, hδ, hδ1, _, hK₂⟩ :=
    gauss_physical_parameter_range γ χ α₁ α₂ α₃ hγ hγ₂ hχ hsum hα₁ hα₂ hα₃
  have hCpos : 0 < c := by dsimp [c]; linarith [ha, hab, hbc]
  have hcn : ∀ n : ℤ, c ≠ (n : ℝ) :=
    real_open_unit_not_int hCpos hc1
  have hδn : ∀ n : ℤ, c - a - b ≠ (n : ℝ) := by
    exact real_open_unit_not_int hδ hδ1
  obtain ⟨coeff, hcoeff, _⟩ :=
    real_gauss_solution_coefficient_ratio hH a b c hcn hδn hK₂.ne' T hT
  let F : Filter ℝ := nhdsWithin 0 (Ioi 0)
  have hrealCast : Tendsto (fun x : ℝ => (x : ℂ)) F (nhds 0) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds)
  have hcN : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n hn
    have hreal : c = -(n : ℝ) := by exact_mod_cast hn
    have hnle : -(n : ℝ) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
    linarith [hCpos, hreal, hnle]
  have hminus : Tendsto
      (fun x : ℝ => gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) F (nhds 1) := by
    have h := (gaussFamily_tendsto_one_at_zero hH (a : ℂ) (b : ℂ) (c : ℂ) hcN).comp hrealCast
    simpa [Function.comp_def, gaussFMinus] using h
  have hcplus : ∀ n : ℕ, (2 - (c : ℂ)) ≠ -(n : ℂ) := by
    intro n hn
    have hnRe : 2 - c = -(n : ℝ) := by
      have h := congrArg Complex.re hn
      simpa using h
    have hEqR : c = 2 + n := by linarith
    linarith [hc1, hEqR]
  have hseed : Tendsto
      (fun x : ℝ => H ((a : ℂ) - (c : ℂ) + 1)
        ((b : ℂ) - (c : ℂ) + 1) (2 - (c : ℂ)) (x : ℂ)) F (nhds 1) := by
    exact (gaussFamily_tendsto_one_at_zero hH _ _ _ hcplus).comp hrealCast
  have hpower : Tendsto (fun x : ℝ => (x : ℂ) ^ (1 - (c : ℂ))) F (nhds 0) :=
    tendsto_real_positive_cpow_zero c hc1
  have hplus : Tendsto
      (fun x : ℝ => gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)) F (nhds 0) := by
    simpa [Function.comp_def, gaussFPlus] using hpower.mul hseed
  have hminusNorm : Tendsto
      (fun x : ℝ => ‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖) F (nhds 1) := by
    simpa [Function.comp_def] using continuous_norm.continuousAt.tendsto.comp hminus
  have hplusNorm : Tendsto
      (fun x : ℝ => ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖) F (nhds 0) := by
    simpa [Function.comp_def] using continuous_norm.continuousAt.tendsto.comp hplus
  have hminusSq : Tendsto
      (fun x : ℝ => ‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2) F (nhds 1) := by
    simpa using hminusNorm.pow 2
  have hplusSq : Tendsto
      (fun x : ℝ => ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2) F (nhds 0) := by
    simpa using hplusNorm.pow 2
  have hbracket : Tendsto
      (fun x : ℝ => ‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2 +
        gaussCoefficientRatio a b c *
          ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2) F (nhds 1) := by
    simpa using hminusSq.add (tendsto_const_nhds.mul hplusSq)
  have hRHS : Tendsto
      (fun x : ℝ => coeff * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2 +
        gaussCoefficientRatio a b c *
          ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2)) F (nhds coeff) := by
    simpa using tendsto_const_nhds.mul hbracket
  have hTlim : Tendsto (fun x : ℝ => T (x : ℂ)) F (nhds (T 0)) :=
    hcont.tendsto.comp hrealCast
  have hcut : ∀ᶠ x : ℝ in F, (x : ℂ) ∈ gaussCutPlane := by
    have hlt : ∀ᶠ x : ℝ in F, x < 1 := by
      exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
        (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [self_mem_nhdsWithin, hlt] with x hx hxlt
    change (x : ℂ).im ≠ 0 ∨ (0 < (x : ℂ).re ∧ (x : ℂ).re < 1)
    right
    simp only [Complex.ofReal_re]
    exact ⟨hx, hxlt⟩
  have hEq : (fun x : ℝ => T (x : ℂ)) =ᶠ[F]
      (fun x => coeff * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2 +
        gaussCoefficientRatio a b c *
          ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2)) := by
    filter_upwards [hcut] with x hx
    exact hcoeff (x : ℂ) hx
  have hRHS' : Tendsto
      (fun x : ℝ => coeff * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2 +
        gaussCoefficientRatio a b c *
          ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (x : ℂ)‖ ^ 2)) F (nhds (T 0)) :=
    hTlim.congr' hEq
  have hFne : NeBot F := by
    dsimp [F]
    exact (isGLB_Ioi : IsGLB (Ioi (0 : ℝ)) 0).nhdsWithin_neBot ⟨1, by norm_num⟩
  have hcoeff0 : coeff = T 0 := tendsto_nhds_unique' hFne hRHS hRHS'
  intro z hz
  change T z = T 0 * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2 +
    gaussCoefficientRatio a b c *
      ‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2)
  rw [← hcoeff0]
  exact hcoeff z hz

end DOZZ.Proofs
