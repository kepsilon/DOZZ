/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage
public import DOZZ.Statements.Defs.IsEquatorGFF
public import DOZZ.Statements.GMC.GaussianCovariance
public import DOZZ.Statements.GMC.IsAdmissibleLogRegularization
public import DOZZ.GMC.CircleAverageGaussian
public import DOZZ.GMC.CirclePotential
public import DOZZ.GFFStructure.CircleCovariance

/-! Circle-average Gaussianity, covariance, and admissibility for the GMC statements. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The second-moment covariance of two circle averages is their double-circle kernel energy. -/
theorem isCircleAverage_covariance
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (x y : ℂ) (r s : ℝ) :
    gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω y s) =
      ∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r := by
  obtain ⟨_, hMean⟩ := circleAverage_isGaussianProcess P X Xc hX hXc
  have hKernel :
      (∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r) =
        -circleLogPotential ‖x - y‖₊
            ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨Real.exp (-s), Real.exp_pos _⟩ +
          circleLogPotential ‖x‖₊
            ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ +
          circleLogPotential ‖y‖₊
            ⟨Real.exp (-s), Real.exp_pos _⟩ ⟨1, by norm_num⟩ := by
    rw [integral_integral_gffKernel_eq_logmax]
    simp_rw [norm_sub_rev y]
    rw [integral_logmax_circleMeasure_eq_closed x y r (Real.exp_pos _),
      integral_log_normPlus_circleMeasure_eq_closed x r,
      integral_log_normPlus_circleMeasure_eq_closed y s]
  calc
    gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω y s) =
        ∫ ω, Xc ω x r * Xc ω y s ∂P := rfl
    _ = ProbabilityTheory.covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P := by
      symm
      simp only [ProbabilityTheory.covariance]
      rw [hMean x r, hMean y s]
      simp
    _ = -circleLogPotential ‖x - y‖₊
          ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨Real.exp (-s), Real.exp_pos _⟩ +
        circleLogPotential ‖x‖₊
          ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ +
        circleLogPotential ‖y‖₊
          ⟨Real.exp (-s), Real.exp_pos _⟩ ⟨1, by norm_num⟩ :=
      circleAverage_covariance P X Xc hX hXc x y r s
    _ = ∫ u, ∫ v, gffKernel u v ∂circleMeasure y s ∂circleMeasure x r := hKernel.symm

end DOZZ.Proofs

namespace DOZZ.Proofs

theorem log_one_div_exp_neg_eq (t : ℝ) : Real.log (1 / Real.exp (-t)) = t := by
  rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]

theorem exp_neg_log_one_div {ε : ℝ} (hε : 0 < ε) : Real.exp (-Real.log (1 / ε)) = ε := by
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]

theorem log_one_div_nonneg_of_le_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) : 0 ≤ Real.log (1 / ε) := by
  apply Real.log_nonneg
  rw [le_div_iff₀ hε]
  linarith

theorem normPlus_pos (x : ℂ) : 0 < normPlus x :=
  lt_of_lt_of_le one_pos (le_max_left _ _)

theorem continuous_normPlus : Continuous normPlus :=
  continuous_const.max continuous_norm

/-- The circle-average family satisfies every clause of `IsAdmissibleLogRegularization`
on every open chart (bounded or not), given the explicit inputs below. -/
theorem circleAverage_admissible_of_inputs
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (U : Set ℂ) (hU : IsOpen U)
    -- (S1) joint Gaussianity of finitely many circle averages (Gaussian closure applied to
    -- mollified circles)
    (hJG : ∀ (n : ℕ) (p : Fin n → ℂ × ℝ),
      IsCenteredJointlyGaussian P (fun ω i => Xc ω (p i).1 (p i).2))
    -- (S2) the circle covariance (`isCircleAverage_covariance`)
    (hCov : ∀ x y r s, gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω y s) =
      circleKernel x r y s)
    -- (D1) mixed logarithmic bound for radii at most one and centres in the `R`-ball
    (hD1 : ∀ R : ℝ, 0 ≤ R → ∀ x y : ℂ, ‖x‖ ≤ R → ‖y‖ ≤ R → ∀ r s : ℝ, 0 ≤ r → 0 ≤ s →
      |circleKernel x r y s -
          Real.log (1 / max ‖x - y‖ (max (Real.exp (-r)) (Real.exp (-s))))| ≤
        Real.log 3 + 2 * Real.log (1 + R))
    -- (D2) separated circles: exact logarithm, 1-Lipschitz regular part
    (hD2 : ∀ x y : ℂ, ∀ r s : ℝ, Real.exp (-r) + Real.exp (-s) ≤ ‖x - y‖ →
      |circleKernel x r y s - gffKernel x y| ≤ Real.exp (-r) + Real.exp (-s))
    -- (D3) fine circle against a fixed circle: Lipschitz potential of the fixed circle
    (hD3 : ∀ x y : ℂ, ∀ r s : ℝ,
      |circleKernel x r y s - ∫ v, gffKernel x v ∂circleMeasure y s| ≤
        (Real.exp s + 1) * Real.exp (-r)) :
    IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) 1
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) := by
  -- compact sets lie in a centred closed ball of nonnegative radius
  have hball : ∀ K : Set ℂ, IsCompact K → ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ K, ‖x‖ ≤ R := by
    intro K hK
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hK.isBounded
    refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
    have := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have hC0 : ∀ R : ℝ, 0 ≤ R → 0 ≤ Real.log 3 + 2 * Real.log (1 + R) := by
    intro R hR
    have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h1 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
    linarith
  refine
    { measurableAtScale := fun ε => hXc.1 (Real.log (1 / ε))
      openChart := hU
      densityContinuous := ?_
      densityPositive := fun x _ => Real.rpow_pos_of_pos (normPlus_pos x) _
      cutoffPositive := one_pos
      gaussian := fun n q _ => hJG n (fun i => ((q i).2, Real.log (1 / (q i).1)))
      covarianceBound := ?_
      coarseVarianceBound := ?_
      coarseMixedBound := ?_
      offDiagonalLimit := ?_
      fixedCoarseLimit := ?_ }
  · -- density
    exact (continuous_normPlus.rpow_const
      (fun x => Or.inl (normPlus_pos x).ne')).continuousOn
  · -- mixed logarithmic covariance bound
    intro K hK _
    obtain ⟨R, hR0, hR⟩ := hball K hK
    refine ⟨Real.log 3 + 2 * Real.log (1 + R), hC0 R hR0, ?_⟩
    intro ε δ hε hε1 hδ hδ1 x hx y hy
    have h := hD1 R hR0 x y (hR x hx) (hR y hy) (Real.log (1 / ε)) (Real.log (1 / δ))
      (log_one_div_nonneg_of_le_one hε hε1) (log_one_div_nonneg_of_le_one hδ hδ1)
    rw [exp_neg_log_one_div hε, exp_neg_log_one_div hδ] at h
    simpa only [hCov] using h
  · -- coarse variance
    intro K hK _
    obtain ⟨R, hR0, hR⟩ := hball K hK
    refine ⟨Real.log 3 + 2 * Real.log (1 + R), hC0 R hR0, ?_⟩
    intro k _ x hx
    have h := hD1 R hR0 x x (hR x hx) (hR x hx) (k : ℝ) (k : ℝ)
      (Nat.cast_nonneg k) (Nat.cast_nonneg k)
    rw [sub_self, norm_zero, max_self,
      max_eq_right (Real.exp_pos _).le, log_one_div_exp_neg_eq] at h
    simp only [log_one_div_exp_neg_eq]
    unfold gaussianVariance
    rw [hCov]
    exact h
  · -- same-centre mixed coarse covariance
    intro K hK _
    obtain ⟨R, hR0, hR⟩ := hball K hK
    refine ⟨Real.log 3 + 2 * Real.log (1 + R), hC0 R hR0, ?_⟩
    intro k _ ε hε hεk x hx
    have hε1 : ε ≤ 1 := hεk.trans (Real.exp_le_one_iff.2 (by
      have := Nat.cast_nonneg (α := ℝ) k; linarith))
    have h := hD1 R hR0 x x (hR x hx) (hR x hx) (k : ℝ) (Real.log (1 / ε))
      (Nat.cast_nonneg k) (log_one_div_nonneg_of_le_one hε hε1)
    rw [exp_neg_log_one_div hε, sub_self, norm_zero, max_eq_left hεk,
      max_eq_right (Real.exp_pos _).le, log_one_div_exp_neg_eq] at h
    simp only [log_one_div_exp_neg_eq]
    rw [hCov]
    exact h
  · -- separated off-diagonal limit with continuous regular part
    refine ⟨fun x y => Real.log (normPlus x) + Real.log (normPlus y), ?_, ?_⟩
    · have hc : Continuous (fun x : ℂ => Real.log (normPlus x)) :=
        continuous_normPlus.log (fun x => (normPlus_pos x).ne')
      exact ((hc.comp continuous_fst).add (hc.comp continuous_snd)).continuousOn
    · intro K _ _ s hs η hη
      refine ⟨min (s / 2) (η / 3), lt_min (by linarith) (by linarith), ?_⟩
      intro ε ε' hε hεδ hε' hε'δ x _ y _ hxy
      have hεs : ε ≤ s / 2 := hεδ.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hε's : ε' ≤ s / 2 := hε'δ.trans ((min_le_left _ _).trans (min_le_left _ _))
      have hεη : ε ≤ η / 3 := hεδ.trans ((min_le_left _ _).trans (min_le_right _ _))
      have hε'η : ε' ≤ η / 3 := hε'δ.trans ((min_le_left _ _).trans (min_le_right _ _))
      have h := hD2 x y (Real.log (1 / ε)) (Real.log (1 / ε'))
        (by rw [exp_neg_log_one_div hε, exp_neg_log_one_div hε']; linarith)
      rw [exp_neg_log_one_div hε, exp_neg_log_one_div hε'] at h
      have hk : gffKernel x y =
          Real.log (1 / ‖x - y‖) + (Real.log (normPlus x) + Real.log (normPlus y)) := by
        unfold gffKernel
        rw [one_div, Real.log_inv]
        ring
      simp only [hCov]
      rw [← hk]
      linarith
  · -- fixed-coarse-scale limit
    refine ⟨fun k x y => ∫ v, gffKernel x v ∂circleMeasure y k, ?_⟩
    intro K _ _ k _ η hη
    have hpos : 0 < Real.exp k + 1 := by positivity
    refine ⟨η / (2 * (Real.exp k + 1)), by positivity, ?_⟩
    intro ε hε hεδ x _ y _
    have hεη : ε ≤ η / (2 * (Real.exp k + 1)) := hεδ.trans (min_le_left _ _)
    have h := hD3 x y (Real.log (1 / ε)) (k : ℝ)
    rw [exp_neg_log_one_div hε] at h
    simp only [log_one_div_exp_neg_eq]
    rw [hCov]
    have hb : (Real.exp k + 1) * ε ≤ η / 2 := by
      calc (Real.exp k + 1) * ε ≤ (Real.exp k + 1) * (η / (2 * (Real.exp k + 1))) :=
            mul_le_mul_of_nonneg_left hεη hpos.le
        _ = η / 2 := by field_simp
    linarith

/-- Circle averages of an equator GFF are admissible on every open chart. -/
theorem isCircleAverage_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (U : Set ℂ) (hU : IsOpen U) :
    IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) 1
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) := by
  exact circleAverage_admissible_of_inputs P X Xc hXc U hU
    (fun n p => circleAverage_finite_family_jointly_gaussian P X hX Xc hXc p)
    (fun x y r s => by
      simpa only [circleKernel] using
        isCircleAverage_covariance P X hX Xc hXc x y r s)
    abs_circleKernel_sub_log_le abs_circleKernel_sub_gffKernel_le abs_circleKernel_sub_integral_gffKernel_le

end DOZZ.Proofs
