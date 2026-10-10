/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.CircleCovarianceL2Limit

/-! Uniform bounded-continuous approximants for exponential circle-covariance weights. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private noncomputable def gmcExpBCF
    (γ : ℝ) (f : BoundedContinuousFunction ℂ ℝ) (K : ℝ)
    (hf : ∀ x, |f x| ≤ K) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.mk
    ⟨fun x => Real.exp (γ * f x),
      Real.continuous_exp.comp (continuous_const.mul f.continuous)⟩
    ⟨2 * Real.exp (|γ| * K), by
      intro x y
      rw [Real.dist_eq]
      have harg (z : ℂ) : γ * f z ≤ |γ| * K := by
        calc
          γ * f z ≤ |γ * f z| := le_abs_self _
          _ = |γ| * |f z| := abs_mul _ _
          _ ≤ |γ| * K := mul_le_mul_of_nonneg_left (hf z) (abs_nonneg γ)
      have hexp (z : ℂ) : Real.exp (γ * f z) ≤ Real.exp (|γ| * K) :=
        Real.exp_le_exp.mpr (harg z)
      calc
        |Real.exp (γ * f x) - Real.exp (γ * f y)| ≤
            |Real.exp (γ * f x)| + |Real.exp (γ * f y)| := abs_sub _ _
        _ ≤ Real.exp (|γ| * K) + Real.exp (|γ| * K) := by
              exact add_le_add
                (by rw [abs_of_nonneg (Real.exp_nonneg _)]; exact hexp x)
                (by rw [abs_of_nonneg (Real.exp_nonneg _)]; exact hexp y)
        _ = 2 * Real.exp (|γ| * K) := by ring⟩

/-- The covariance weights `exp (γ c_r)` admit a BCF family which agrees with them eventually
and converges uniformly to `exp (γ c)`. The initial radii are filled by the limit weight so the
family is bounded-continuous at every parameter. -/
theorem equatorGFF_circleCovariance_exp_weight_family
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (γ : ℝ) (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x r) L) c atTop) :
    ∃ u : ℝ → BoundedContinuousFunction ℂ ℝ, ∃ w : BoundedContinuousFunction ℂ ℝ,
      (∀ r x, 0 ≤ u r x) ∧ (∀ x, 0 ≤ w x) ∧
      TendstoUniformly (fun r x => u r x) w atTop ∧
      (∀ᶠ r : ℝ in atTop, ∀ x : ℂ,
        u r x = Real.exp (γ * gaussianCovariance P (fun ω => Xc ω x r) L)) := by
  let cov : ℝ → ℂ → ℝ := fun r x => gaussianCovariance P (fun ω => Xc ω x r) L
  let covCont (r : ℝ) : C(ℂ, ℝ) :=
    ⟨cov r, continuous_gaussianCovariance_circle_of_IsGaussianL2Limit
      P X hX Xc hXc L hL r⟩
  have hnear : ∀ᶠ r : ℝ in atTop, ∀ x : ℂ, dist (c x) (cov r x) < 1 := by
    exact (Metric.tendstoUniformly_iff.mp hc) 1 zero_lt_one
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp hnear
  let K : ℝ := ‖c‖ + 1
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcBound (x : ℂ) : |c x| ≤ K := by
    calc
      |c x| = ‖c x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖c‖ := c.norm_coe_le_norm x
      _ ≤ K := by dsimp [K]; linarith [norm_nonneg c]
  have hcovBound (r : ℝ) (hr : R ≤ r) (x : ℂ) : |cov r x| ≤ K := by
    have hclose := hR r hr x
    have hdiff : |cov r x - c x| < 1 := by
      simpa [Real.dist_eq, abs_sub_comm] using hclose
    calc
      |cov r x| = |(cov r x - c x) + c x| := by congr 1; ring
      _ ≤ |cov r x - c x| + |c x| := abs_add_le _ _
      _ ≤ 1 + ‖c‖ := add_le_add (le_of_lt hdiff) (by
        calc
          |c x| = ‖c x‖ := (Real.norm_eq_abs _).symm
          _ ≤ ‖c‖ := c.norm_coe_le_norm x)
      _ = K := by dsimp [K]; ring
  let covBCF (r : ℝ) : BoundedContinuousFunction ℂ ℝ :=
    if hr : R ≤ r then
      BoundedContinuousFunction.mk (covCont r)
        ⟨2 * K, by
          intro x y
          rw [Real.dist_eq]
          calc
            |cov r x - cov r y| ≤ |cov r x| + |cov r y| := abs_sub _ _
            _ ≤ K + K := add_le_add (hcovBound r hr x) (hcovBound r hr y)
            _ = 2 * K := by ring⟩
    else c
  have hcovBCF_bound (r : ℝ) (x : ℂ) : |covBCF r x| ≤ K := by
    dsimp only [covBCF]
    by_cases hr : R ≤ r
    · rw [dite_eq_left hr]
      exact hcovBound r hr x
    · rw [dite_eq_right hr]
      exact hcBound x
  have hcovBCF_eq (r : ℝ) (hr : R ≤ r) (x : ℂ) : covBCF r x = cov r x := by
    change (if h : R ≤ r then (BoundedContinuousFunction.mk (covCont r)
      ⟨2 * K, by
        intro x y
        rw [Real.dist_eq]
        calc
          |cov r x - cov r y| ≤ |cov r x| + |cov r y| := abs_sub _ _
          _ ≤ K + K := add_le_add (hcovBound r h x) (hcovBound r h y)
          _ = 2 * K := by ring⟩ : BoundedContinuousFunction ℂ ℝ) else c) x = cov r x
    rw [dite_eq_left hr]
    rfl
  let w : BoundedContinuousFunction ℂ ℝ := gmcExpBCF γ c K hcBound
  let u : ℝ → BoundedContinuousFunction ℂ ℝ := fun r => gmcExpBCF γ (covBCF r) K
    (hcovBCF_bound r)
  have hu (r : ℝ) (x : ℂ) : 0 ≤ u r x := Real.exp_nonneg _
  have hw (x : ℂ) : 0 ≤ w x := Real.exp_nonneg _
  have heventR : ∀ᶠ r : ℝ in atTop, R ≤ r :=
    Filter.eventually_atTop.2 ⟨R, fun r hr => hr⟩
  have huEq (r : ℝ) (hr : R ≤ r) (x : ℂ) : u r x = Real.exp (γ * cov r x) := by
    change Real.exp (γ * covBCF r x) = Real.exp (γ * cov r x)
    rw [hcovBCF_eq r hr x]
  have hwEq (x : ℂ) : w x = Real.exp (γ * c x) := by
    rfl
  have hgcont : Continuous (fun t : ℝ => Real.exp (γ * t)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have huc : UniformContinuousOn (fun t : ℝ => Real.exp (γ * t)) (Set.Icc (-K) K) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hgcont.continuousOn
  have huniform : TendstoUniformly (fun r x => u r x) w atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.mp huc) ε hε
    have hclose : ∀ᶠ r : ℝ in atTop, ∀ x : ℂ, dist (c x) (cov r x) < δ :=
      (Metric.tendstoUniformly_iff.mp hc) δ hδ
    filter_upwards [hclose, heventR] with r hclose hr x
    rw [hwEq, huEq r hr x]
    apply hcontrol (c x) ?_ (cov r x) ?_ (hclose x)
    · exact abs_le.mp (hcBound x)
    · have hbound := hcovBound r hr x
      exact abs_le.mp hbound
  refine ⟨u, w, hu, hw, huniform, ?_⟩
  filter_upwards [heventR] with r hr x
  exact huEq r hr x

end DOZZ.Proofs
