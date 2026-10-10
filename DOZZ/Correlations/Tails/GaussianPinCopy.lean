/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.GaussianRegression
public import Mathlib.Probability.Independence.Basic

/-! Replace the correlated pin by an independent copy after Gaussian regression.
The full coordinate law is preserved, including the pin coordinate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

/-- The regressed Gaussian family can be restored with an independent copy of the pin.
The equality concerns the whole product sigma algebra, not only scalar marginals. -/
theorem gaussian_pin_copy_law
    {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : Option I → Ω → ℝ) (hZ : IsGaussianProcess Z P)
    (hZm : Measurable (fun ω j => Z j ω))
    (v : ℝ) (hv : v ≠ 0) (hvar : covariance (Z none) (Z none) P = v) :
    P.map (fun ω j => Z j ω) =
      (P.prod P).map (fun q j => j.elim (Z none q.2) (fun i =>
        Z (some i) q.1 + (covariance (Z (some i)) (Z none) P / v) *
          (Z none q.2 - Z none q.1))) := by
  let : IsProbabilityMeasure P := hZ.isProbabilityMeasure
  let a : I → ℝ := fun i => covariance (Z (some i)) (Z none) P / v
  let R : Ω → I → ℝ := fun ω i => Z (some i) ω - a i * Z none ω
  have hN : Measurable (Z none) := (measurable_pi_apply none).comp hZm
  have hR : Measurable R := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((measurable_pi_apply (some i)).comp hZm).sub (hN.const_mul (a i))
  have hi : IndepFun (Z none) R P := gaussian_regression_indep P Z hZ v hv hvar
  have hNR := hi.map_prod_eq_prod_map_map hN.aemeasurable hR.aemeasurable
  have hRc : Measurable (fun q : Ω × Ω => R q.1) := hR.comp measurable_fst
  have hNc : Measurable (fun q : Ω × Ω => Z none q.2) := hN.comp measurable_snd
  have hcopy := (indepFun_prod (μ := P) (ν := P) hR hN).symm.map_prod_eq_prod_map_map
    hNc.aemeasurable hRc.aemeasurable
  have hNmap : (P.prod P).map (fun q : Ω × Ω => Z none q.2) = P.map (Z none) := by
    rw [← Function.comp_def, ← Measure.map_map hN measurable_snd,
      measurePreserving_snd.map_eq]
  have hRmap : (P.prod P).map (fun q : Ω × Ω => R q.1) = P.map R := by
    rw [← Function.comp_def, ← Measure.map_map hR measurable_fst,
      measurePreserving_fst.map_eq]
  rw [hNmap, hRmap, ← hNR] at hcopy
  let restore : ℝ × (I → ℝ) → Option I → ℝ := fun q j =>
    j.elim q.1 (fun i => q.2 i + a i * q.1)
  have hr : Measurable restore := by
    apply measurable_pi_iff.mpr
    intro j
    cases j with
    | none => exact measurable_fst
    | some i =>
      exact ((measurable_pi_apply i).comp measurable_snd).add
        (measurable_fst.const_mul (a i))
  have he := congrArg (fun μ => μ.map restore) hcopy
  rw [Measure.map_map hr (hNc.prodMk hRc),
    Measure.map_map hr (hN.prodMk hR)] at he
  have hsource : (restore ∘ fun ω => (Z none ω, R ω)) = fun ω j => Z j ω := by
    funext ω j
    cases j <;> simp only [restore, Function.comp_def, Option.elim_none,
      Option.elim_some, R]
    all_goals ring
  have htarget : (restore ∘ fun q : Ω × Ω => (Z none q.2, R q.1)) =
      fun q j => j.elim (Z none q.2) (fun i =>
        Z (some i) q.1 + (covariance (Z (some i)) (Z none) P / v) *
          (Z none q.2 - Z none q.1)) := by
    funext q j
    cases j <;> simp only [restore, Function.comp_def, Option.elim_none,
      Option.elim_some, R, a]
    all_goals ring
  rw [hsource, htarget] at he
  exact he.symm


end DOZZ.Proofs
