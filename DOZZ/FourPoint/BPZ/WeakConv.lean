/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.Grid
public import DOZZ.FourPoint.BPZ.ConvProb
public import DOZZ.FourPoint.BPZ.WardStarPrep

/-! # Weak convergence in probability of random measures: deterministic part

A sequence of finite random measures `μ n` converges weakly in probability to `μ₀` if the
integrals of bounded measurable functions with bounded support converge in probability. To pass
such convergence to double integrals of kernels that are only continuous off the diagonal, the
double integral is compared with the finite grid sums `∑ μ(Q_i) ∫ H(c_i, y) dμ(y)`. The error is
controlled by the kernel's modulus of continuity away from the diagonal and by the near-diagonal
mass `∫_{|x| ≤ ρ} μ(B(x, t)) dμ(x)`, which tends to zero as `t → 0` for a measure without atoms. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Weak convergence in probability of finite random measures, tested against bounded
measurable functions with bounded support. -/
structure BPZWeakConv (P : Measure Ω) (μ : ℕ → Ω → Measure ℂ) (μ₀ : Ω → Measure ℂ) : Prop where
  meas : ∀ n, Measurable (μ n)
  meas₀ : Measurable μ₀
  fin : ∀ n ω, IsFiniteMeasure (μ n ω)
  fin₀ : ∀ ω, IsFiniteMeasure (μ₀ ω)
  conv : ∀ f : ℂ → ℝ, Measurable f → ∀ C R : ℝ, (∀ x, |f x| ≤ C) → (∀ x, R < ‖x‖ → f x = 0) →
    TendstoInMeasure P (fun n ω => ∫ x, f x ∂μ n ω) atTop (fun ω => ∫ x, f x ∂μ₀ ω)

/-- Iterated integrals against two measurable families of finite measures are measurable. -/
theorem bpz_measurable_double_integral {μ ν : Ω → Measure ℂ} (hμ : Measurable μ)
    (hμfin : ∀ ω, IsFiniteMeasure (μ ω)) (hν : Measurable ν)
    (hνfin : ∀ ω, IsFiniteMeasure (ν ω)) (g : ℂ → ℂ → ℝ)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun ω => ∫ x, ∫ y, g x y ∂ν ω ∂μ ω) := by
  have hin : Measurable (fun p : Ω × ℂ => ∫ y, g p.2 y ∂ν p.1) :=
    measurable_integral_finite_family ν hν hνfin g hg
  have hout := measurable_integral_finite_family μ hμ hμfin
    (fun ω' x => ∫ y, g x y ∂ν ω') hin
  exact hout.comp (measurable_id.prodMk measurable_id)

/-- The near-diagonal kernel `1{|x| ≤ ρ} 1{|y - x| < t}`. -/
noncomputable def bpzNearKernel (ρ t : ℝ) (x y : ℂ) : ℝ :=
  if ‖x‖ ≤ ρ ∧ dist y x < t then 1 else 0

/-- The near-diagonal mass `∫_{|x| ≤ ρ} μ(B(x, t)) dμ(x)`. -/
noncomputable def bpzNearDiag (ρ t : ℝ) (μ : Measure ℂ) : ℝ :=
  ∫ x, ∫ y, bpzNearKernel ρ t x y ∂μ ∂μ

theorem measurable_bpzNearKernel (ρ t : ℝ) : Measurable (Function.uncurry (bpzNearKernel ρ t)) := by
  have hs : MeasurableSet {p : ℂ × ℂ | ‖p.1‖ ≤ ρ ∧ dist p.2 p.1 < t} :=
    (measurableSet_le continuous_fst.norm.measurable measurable_const).inter
      (measurableSet_lt (continuous_snd.dist continuous_fst).measurable measurable_const)
  exact Measurable.ite hs measurable_const measurable_const

theorem bpzNearKernel_nonneg (ρ t : ℝ) (x y : ℂ) : 0 ≤ bpzNearKernel ρ t x y := by
  unfold bpzNearKernel; split_ifs <;> norm_num

theorem bpzNearKernel_le_one (ρ t : ℝ) (x y : ℂ) : bpzNearKernel ρ t x y ≤ 1 := by
  unfold bpzNearKernel; split_ifs <;> norm_num

theorem bpzNearKernel_mono {ρ ρ' t t' : ℝ} (hρ : ρ ≤ ρ') (ht : t ≤ t') (x y : ℂ) :
    bpzNearKernel ρ t x y ≤ bpzNearKernel ρ' t' x y := by
  unfold bpzNearKernel
  by_cases h : ‖x‖ ≤ ρ ∧ dist y x < t
  · rw [ite_eq_left h, ite_eq_left ⟨h.1.trans hρ, h.2.trans_le ht⟩]
  · rw [ite_eq_right h]; exact bpzNearKernel_nonneg ρ' t' x y

/-- The inner integral of the near-diagonal kernel is the mass of a ball. -/
theorem integral_bpzNearKernel (μ : Measure ℂ) [IsFiniteMeasure μ] (ρ t : ℝ) (x : ℂ) :
    ∫ y, bpzNearKernel ρ t x y ∂μ = if ‖x‖ ≤ ρ then μ.real (Metric.ball x t) else 0 := by
  by_cases hx : ‖x‖ ≤ ρ
  · rw [ite_eq_left hx]
    have heq : (fun y => bpzNearKernel ρ t x y) = (Metric.ball x t).indicator 1 := by
      funext y
      simp only [bpzNearKernel, hx, true_and, Set.indicator, Metric.mem_ball, Pi.one_apply]
    rw [heq, integral_indicator_one measurableSet_ball]
  · rw [ite_eq_right hx]
    have heq : (fun y => bpzNearKernel ρ t x y) = fun _ => 0 := by
      funext y
      simp only [bpzNearKernel, hx, false_and, ite_false]
    rw [heq, integral_zero]

theorem bpzNearDiag_nonneg (ρ t : ℝ) (μ : Measure ℂ) : 0 ≤ bpzNearDiag ρ t μ :=
  integral_nonneg fun x => integral_nonneg fun y => bpzNearKernel_nonneg ρ t x y

theorem integrable_of_bdd_finite {μ : Measure ℂ} [IsFiniteMeasure μ] {f : ℂ → ℝ}
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

/-- Inner integrals of a bounded kernel are bounded and measurable. -/
theorem bpz_inner_integral_bdd {μ : Measure ℂ} [IsFiniteMeasure μ] {g : ℂ → ℂ → ℝ}
    {C : ℝ} (hC : ∀ x y, |g x y| ≤ C) (x : ℂ) :
    |∫ y, g x y ∂μ| ≤ C * μ.real Set.univ := by
  rw [← Real.norm_eq_abs]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => g x y) (C := C)
    (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC x y)
  exact this

theorem bpzNearDiag_mono {ρ ρ' t t' : ℝ} (hρ : ρ ≤ ρ') (ht : t ≤ t') (μ : Measure ℂ)
    [IsFiniteMeasure μ] : bpzNearDiag ρ t μ ≤ bpzNearDiag ρ' t' μ := by
  have hmeas : ∀ ρ t, Measurable fun x => ∫ y, bpzNearKernel ρ t x y ∂μ := fun ρ t =>
    ((measurable_bpzNearKernel ρ t).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  refine integral_mono (integrable_of_bdd_finite (hmeas ρ t) (C := μ.real Set.univ) ?_)
    (integrable_of_bdd_finite (hmeas ρ' t') (C := μ.real Set.univ) ?_) fun x => ?_
  · intro x
    simpa using bpz_inner_integral_bdd (μ := μ) (g := bpzNearKernel ρ t) (C := 1)
      (fun x y => by
        rw [abs_of_nonneg (bpzNearKernel_nonneg ρ t x y)]
        exact bpzNearKernel_le_one ρ t x y) x
  · intro x
    simpa using bpz_inner_integral_bdd (μ := μ) (g := bpzNearKernel ρ' t') (C := 1)
      (fun x y => by
        rw [abs_of_nonneg (bpzNearKernel_nonneg ρ' t' x y)]
        exact bpzNearKernel_le_one ρ' t' x y) x
  · exact integral_mono (integrable_of_bdd_finite ((measurable_bpzNearKernel ρ t).comp
      (measurable_const.prodMk measurable_id)) (C := 1) fun y => by
        rw [abs_of_nonneg (bpzNearKernel_nonneg ρ t x y)]; exact bpzNearKernel_le_one ρ t x y)
      (integrable_of_bdd_finite ((measurable_bpzNearKernel ρ' t').comp
        (measurable_const.prodMk measurable_id)) (C := 1) fun y => by
        rw [abs_of_nonneg (bpzNearKernel_nonneg ρ' t' x y)]
        exact bpzNearKernel_le_one ρ' t' x y)
      fun y => bpzNearKernel_mono hρ ht x y

end DOZZ.Proofs
