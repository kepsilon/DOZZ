/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterCircleLaw
public import DOZZ.GMC.Moments.InversionCircleAdmissible

/-! Global law of the translated equator-pinned circle process.
Subtracting the circle at the new equator cancels the old pin potentials at every
circle coordinate, even when the circle is not contained in the local insertion disk. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- The translated process pinned on its unit circle has the full origin circle covariance. -/
theorem unpinned_circle_covariance_global
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p q : ℂ × ℝ) :
    covariance (fun ω => Xc ω (z+p.1) p.2 - Xc ω z 0)
      (fun ω => Xc ω (z+q.1) q.2 - Xc ω z 0) P =
    covariance (fun ω => Xc ω p.1 p.2) (fun ω => Xc ω q.1 q.2) P := by
  let : IsProbabilityMeasure P := hX.1
  have hzpin := circle_pin_exterior z 0
    (by simpa only [neg_zero, Real.exp_zero, one_add_one_eq_two] using hz)
  simp only [neg_zero, Real.exp_zero] at hzpin
  rw [covariance_fun_sub_fun_sub (hc.2.1 _ _) (hc.2.1 _ _) (hc.2.1 _ _) (hc.2.1 _ _),
    covariance_comm (fun ω => Xc ω z 0) (fun ω => Xc ω (z+q.1) q.2),
    circleAverage_covariance P X Xc hX hc (z+p.1) (z+q.1),
    circleAverage_covariance P X Xc hX hc (z+p.1) z,
    circleAverage_covariance P X Xc hX hc (z+q.1) z,
    offCenter_origin_variance X Xc hX hc z hz,
    circleAverage_covariance P X Xc hX hc p.1 q.1]
  simp only [add_sub_add_left_eq_sub, add_sub_cancel_left, neg_zero, Real.exp_zero, hzpin]
  ring

/-- Complete translated circle vectors have the origin law, without a cutoff-chart restriction. -/
theorem unpinned_circle_global_fdd
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : ι → ℂ × ℝ) :
    P.map (fun ω i => Xc ω (z+(p i).1) (p i).2 - Xc ω z 0) =
      P.map (fun ω i => Xc ω (p i).1 (p i).2) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨hG, hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hU := isGaussianProcess_sub_reindexed hG
    (fun i => (z+(p i).1, (p i).2)) (fun _ => (z, 0))
  have hmU i : (∫ ω, Xc ω (z+(p i).1) (p i).2 - Xc ω z 0 ∂P) = 0 := by
    rw [integral_sub ((hc.2.1 _ _).integrable (by norm_num))
      ((hc.2.1 _ _).integrable (by norm_num)), hm, hm, sub_self]
  apply map_eq_of_centeredJointlyGaussian_of_covariance_eq P P _ _
    (centeredJointlyGaussian_of_isGaussianProcess P _ hU hmU)
    (centeredJointlyGaussian_of_isGaussianProcess P _ (hG.comp_right p)
      (fun i => hm _ _))
  intro i j
  have h := unpinned_circle_covariance_global P X Xc hX hc z hz (p i) (p j)
  rw [covariance, covariance, hmU, hmU, hm, hm] at h
  simpa only [sub_zero, gaussianCovariance, Function.comp_def] using h

/-- The global unpinned translated process is an admissible equator regularization on
any open chart, so the existing GMC construction applies directly. -/
theorem unpinned_circle_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (U : Set ℂ) (hU : IsOpen U) :
    IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) 1
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨hG, hmean⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  apply inversionCircle_admissible_of_geometry X hX
    (fun ω x r => Xc ω (z+x) r - Xc ω z 0)
  · intro r
    exact (hm.comp (measurable_fst.prodMk
      ((measurable_const.add measurable_snd).prodMk measurable_const))).sub
      (hm.comp (measurable_fst.prodMk (measurable_const (a := (z, (0 : ℝ))))))
  · exact isGaussianProcess_sub_reindexed hG
      (fun p : ℂ × ℝ => (z+p.1, p.2)) (fun _ => (z, 0))
  · intro p
    rw [integral_sub ((hc.2.1 _ _).integrable (by norm_num))
      ((hc.2.1 _ _).integrable (by norm_num)), hmean, hmean, sub_self]
  · intro p q
    rw [unpinned_circle_covariance_global P X Xc hX hc z hz p q,
      covariance_comm (fun ω => Xc ω p.1 p.2) (fun ω => Xc ω q.1 q.2),
      circleAverage_covariance_integral P X Xc hX hc]
  · exact hU


end DOZZ.Proofs
