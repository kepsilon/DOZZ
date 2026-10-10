/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.CircleProjection
public import DOZZ.GMC.CircleAverage

/-!
# Local orthogonal circle regularization

A fixed clamping disk gives a global Gaussian regularizer. On the open chart outside
twice that disk, every allowed cutoff is the literal orthogonal lateral circle. The
radial correction is bounded on compact subsets uniformly in cutoff; subtracting it
therefore preserves the logarithmic covariance and both coarse estimates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions InnerProductSpace RealInnerProductSpace

namespace DOZZ.Proofs

/-- Local punctured-plane chart on which every circle of radius at most `ρ` avoids the
clamping disk of radius `ρ`. These charts exhaust the punctured plane as `ρ` decreases. -/
def originLateralChart (ρ : ℝ) : Set ℂ := {x | 2 * ρ < ‖x‖}

/-- The actual orthogonal circle regularizer, parameterized by Euclidean cutoff radius. -/
noncomputable def originLateralCircleRegularization
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) : Ω → ℝ → ℂ → ℝ :=
  fun ω ε x => clampedCircleLateralSample Xc ρ ω x (Real.log (1 / ε))

/-- The local chart is open. -/
theorem isOpen_originLateralChart (ρ : ℝ) : IsOpen (originLateralChart ρ) :=
  isOpen_lt continuous_const continuous_norm

/-- The chart contains no origin when the clamp is positive. -/
theorem originLateralChart_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ)
    (hx : x ∈ originLateralChart ρ) : x ≠ 0 := by
  intro hzero
  rw [hzero, originLateralChart, mem_ofPred_eq, norm_zero] at hx
  exact (mul_pos (by norm_num : (0 : ℝ) < 2) hρ).not_gt hx

/-- Every allowed local cutoff stays outside the clamping disk. -/
theorem originLateralChart_cutoff_lower (ρ ε : ℝ) (x : ℂ)
    (hx : x ∈ originLateralChart ρ) (hε : 0 < ε) (hερ : ε ≤ ρ) :
    ρ ≤ ‖x‖ - Real.exp (-Real.log (1 / ε)) := by
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]
  change 2 * ρ < ‖x‖ at hx
  linarith only [hx, hερ]

/-- The global regularizer is jointly measurable at every cutoff radius, including
radii outside the range used by the local admissibility statement. -/
theorem originLateralCircleRegularization_measurableAtScale
    {Ω : Type*} [MeasurableSpace Ω] (Xc : Ω → ℂ → ℝ → ℝ)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) :
    Measurable (fun p : Ω × ℂ => originLateralCircleRegularization Xc ρ p.1 ε p.2) :=
  (measurable_clampedCircleLateralSample Xc hm ρ hρ).comp
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))

/-- The exact finite Gaussian requirement holds for all centers and all cutoff radii;
it does not require restricting the Gaussian family to the local chart. -/
theorem originLateralCircleRegularization_gaussian
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (q : Fin n → ℝ × ℂ) :
    IsCenteredJointlyGaussian P
      (fun ω i => originLateralCircleRegularization Xc ρ ω (q i).1 (q i).2) :=
  clampedCircleLateralSample_centeredJointlyGaussian P X Xc hX hc hm ρ hρ n
    (fun i => ((q i).2, Real.log (1 / (q i).1)))

/-- A uniform bound on the clamped radial Hilbert map bounds its circle average. -/
theorem norm_originCircleRadialL2_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (ρ R L : ℝ) (x : ℂ) (r : ℝ)
    (hR : ‖x‖ + Real.exp (-r) ≤ R)
    (hL : ∀ z : ℂ, ‖z‖ ≤ R → ‖circleAverageL2 hc (0, clampedLogRadius ρ z)‖ ≤ L) :
    ‖originCircleRadialL2 hc ρ x r‖ ≤ L := by
  let _ := circleMeasure_isProbability x r
  have hb : ∀ᵐ z ∂circleMeasure x r,
      ‖circleAverageL2 hc (0, clampedLogRadius ρ z)‖ ≤ L := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    apply hL z
    calc ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
         _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
         _ = ‖x‖ + Real.exp (-r) := by rw [hz, add_comm]
         _ ≤ R := hR
  have h := norm_integral_le_of_norm_le_const hb
  rw [probReal_univ, mul_one] at h
  exact h

/-- On each compact set, all clamped radial circle averages with radius at most `ρ`
have one deterministic Hilbert norm bound. -/
theorem originCircleRadialL2_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ ε, 0 < ε → ε ≤ ρ → ∀ x ∈ K,
      ‖originCircleRadialL2 hc ρ x (Real.log (1 / ε))‖ ≤ L := by
  obtain ⟨S, hS⟩ := hK.bddAbove_image continuous_norm.continuousOn
  let R := max S 0 + ρ
  have hF := continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ
  obtain ⟨L, hL⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image hF.norm.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun ε hε hερ x hx => ?_⟩
  apply norm_originCircleRadialL2_le P X Xc hc ρ R (max L 0) x (Real.log (1 / ε))
  · rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]
    have hxS := hS (mem_image_of_mem _ hx)
    exact add_le_add (hxS.trans (le_max_left _ _)) hερ
  · intro z hz
    apply (hL (mem_image_of_mem _ ?_)).trans (le_max_left _ _)
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz

/-- Radial mixed covariances inherit the uniform Hilbert norm bound. -/
theorem abs_originCircleRadialL2_covariance_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (L : ℝ) (hL : 0 ≤ L)
    (x y : ℂ) (r t : ℝ)
    (hx : ‖originCircleRadialL2 hc ρ x r‖ ≤ L)
    (hy : ‖originCircleRadialL2 hc ρ y t‖ ≤ L) :
    |covariance (originCircleRadialL2 hc ρ x r) (originCircleRadialL2 hc ρ y t) P| ≤ L ^ 2 := by
  let _ := hX.1
  rw [covariance_L2_eq, originCircleRadialL2_integral_eq_zero P X Xc hX hc ρ hρ x r,
    zero_mul, sub_zero, ← Real.norm_eq_abs]
  exact (norm_inner_le_norm _ _).trans
    ((mul_le_mul hx hy (norm_nonneg _) hL).trans_eq (pow_two L).symm)

/-- The second moment of the scalar regularizer is the covariance of its actual
centered L² representatives. -/
theorem originLateralCircleRegularization_gaussianCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (ε δ : ℝ) (x y : ℂ) :
    gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
      (fun ω => originLateralCircleRegularization Xc ρ ω δ y) =
      covariance (originCircleLateralL2 hc ρ x (Real.log (1 / ε)))
        (originCircleLateralL2 hc ρ y (Real.log (1 / δ))) P := by
  unfold gaussianCovariance
  have hi : (∫ ω, originLateralCircleRegularization Xc ρ ω ε x *
      originLateralCircleRegularization Xc ρ ω δ y ∂P) =
      ∫ ω, originCircleLateralL2 hc ρ x (Real.log (1 / ε)) ω *
        originCircleLateralL2 hc ρ y (Real.log (1 / δ)) ω ∂P := by
    apply integral_congr_ae
    filter_upwards [clampedCircleLateralSample_ae_eq P X Xc hX hc hm ρ hρ x (Real.log (1 / ε)),
      clampedCircleLateralSample_ae_eq P X Xc hX hc hm ρ hρ y (Real.log (1 / δ))]
      with ω hx hy
    change clampedCircleLateralSample Xc ρ ω x (Real.log (1 / ε)) *
      clampedCircleLateralSample Xc ρ ω y (Real.log (1 / δ)) = _
    rw [← hx, ← hy]
  rw [hi]
  simp only [ProbabilityTheory.covariance,
    originCircleLateralL2_integral_eq_zero P X Xc hX hc ρ hρ, sub_zero]

/-- The full circle second moment likewise agrees with its centered Hilbert covariance. -/
theorem gaussianCovariance_circleL2_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x y : ℂ) (r t : ℝ) :
    gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω y t) =
      covariance (circleAverageL2 hc (x, r)) (circleAverageL2 hc (y, t)) P := by
  unfold gaussianCovariance
  have hi : (∫ ω, Xc ω x r * Xc ω y t ∂P) =
      ∫ ω, circleAverageL2 hc (x, r) ω * circleAverageL2 hc (y, t) ω ∂P := by
    apply integral_congr_ae
    filter_upwards [circleAverageL2_ae_eq hc (x, r), circleAverageL2_ae_eq hc (y, t)]
      with ω hx hy
    rw [hx, hy]
  rw [hi]
  simp only [ProbabilityTheory.covariance, circleAverageL2_integral_eq_zero P X Xc hX hc,
    sub_zero]

/-- The actual orthogonal regularizer satisfies the literal mixed logarithmic covariance
bound uniformly on every compact subset of its chart. -/
theorem originLateralCircleRegularization_covarianceBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε δ, 0 < ε → ε ≤ min ρ 1 → 0 < δ → δ ≤ min ρ 1 →
      ∀ x ∈ K, ∀ y ∈ K,
        |gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
          (fun ω => originLateralCircleRegularization Xc ρ ω δ y) -
            Real.log (1 / max ‖x - y‖ (max ε δ))| ≤ C := by
  have hCircle := isCircleAverage_admissible P X hX Xc hc
    (originLateralChart ρ) (isOpen_originLateralChart ρ)
  obtain ⟨C, hC, hcov⟩ := hCircle.covarianceBound K hK hKU
  obtain ⟨L, hL, hbound⟩ := originCircleRadialL2_uniform_bound P X Xc hX hc ρ hρ K hK
  refine ⟨C + L ^ 2, add_nonneg hC (sq_nonneg _), ?_⟩
  intro ε δ hε hερ hδ hδρ x hx y hy
  rw [originLateralCircleRegularization_gaussianCovariance P X Xc hX hc hm ρ hρ,
    originCircleLateralL2_covariance_expansion P X Xc hX hc ρ ρ hρ hρ x y _ _
      (originLateralChart_cutoff_lower ρ ε x (hKU hx) hε (hερ.trans (min_le_left _ _)))
      (originLateralChart_cutoff_lower ρ δ y (hKU hy) hδ (hδρ.trans (min_le_left _ _))),
    ← gaussianCovariance_circleL2_eq P X Xc hX hc]
  have hRad := abs_originCircleRadialL2_covariance_le P X Xc hX hc ρ hρ L hL x y
    (Real.log (1 / ε)) (Real.log (1 / δ))
    (hbound ε hε (hερ.trans (min_le_left _ _)) x hx)
    (hbound δ hδ (hδρ.trans (min_le_left _ _)) y hy)
  have hFull := hcov ε δ hε (hερ.trans (min_le_right _ _)) hδ
    (hδρ.trans (min_le_right _ _)) x hx y hy
  have halg : ∀ a b c : ℝ, a - b - c = (a - c) - b := by intros; ring
  rw [halg]
  exact (abs_sub _ _).trans (add_le_add hFull hRad)

/-- The same-center coarse mixed estimate is a direct specialization of the mixed logarithmic
covariance bound `originLateralCircleRegularization_covarianceBound`, keeping the coarse barrier
scale exactly `exp(-k)`. -/
theorem originLateralCircleRegularization_coarseMixedBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ min ρ 1 →
      ∀ ε, 0 < ε → ε ≤ Real.exp (-(k : ℝ)) → ∀ x ∈ K,
        |gaussianCovariance P
            (fun ω => originLateralCircleRegularization Xc ρ ω (Real.exp (-(k : ℝ))) x)
            (fun ω => originLateralCircleRegularization Xc ρ ω ε x) - (k : ℝ)| ≤ C := by
  obtain ⟨C, hC, hcov⟩ := originLateralCircleRegularization_covarianceBound
    P X Xc hX hc hm ρ hρ K hK hKU
  refine ⟨C, hC, ?_⟩
  intro k hk ε hε hεk x hx
  have h := hcov (Real.exp (-(k : ℝ))) ε (Real.exp_pos _) hk hε (hεk.trans hk) x hx x hx
  simpa only [sub_self, norm_zero, max_eq_left hεk,
    max_eq_right (Real.exp_pos _).le, one_div, Real.log_inv, Real.log_exp, neg_neg] using h

/-- The variance coarse estimate follows from the same-center mixed bound with the two
cutoff radii equal. -/
theorem originLateralCircleRegularization_coarseVarianceBound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ, Real.exp (-(k : ℝ)) ≤ min ρ 1 → ∀ x ∈ K,
      |gaussianVariance P
          (fun ω => originLateralCircleRegularization Xc ρ ω (Real.exp (-(k : ℝ))) x) -
          (k : ℝ)| ≤ C := by
  obtain ⟨C, hC, hcov⟩ := originLateralCircleRegularization_coarseMixedBound
    P X Xc hX hc hm ρ hρ K hK hKU
  exact ⟨C, hC, fun k hk x hx => hcov k hk _ (Real.exp_pos _) le_rfl x hx⟩

/-- Reference density of the plane lateral chaos before logarithmic-radius pushforward. -/
noncomputable def originLateralPlaneDensity (x : ℂ) : ℝ := ‖x‖ ^ (-2 : ℝ)

/-- The lateral reference density is strictly positive on every punctured-plane chart. -/
theorem originLateralPlaneDensity_pos (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ)
    (hx : x ∈ originLateralChart ρ) : 0 < originLateralPlaneDensity x :=
  Real.rpow_pos_of_pos (norm_pos_iff.mpr (originLateralChart_ne_zero ρ hρ x hx)) _

/-- The lateral reference density is continuous on its chart. -/
theorem continuousOn_originLateralPlaneDensity (ρ : ℝ) (hρ : 0 < ρ) :
    ContinuousOn originLateralPlaneDensity (originLateralChart ρ) :=
  continuous_norm.continuousOn.rpow_const
    (fun x hx => Or.inl (norm_ne_zero_iff.mpr (originLateralChart_ne_zero ρ hρ x hx)))

/-- The deterministic radial Wick correction converts the reference density to
exactly the flat cylinder density in plane coordinates. -/
theorem originLateralPlaneDensity_radial_identity (x : ℂ) (hx : x ≠ 0) :
    normPlus x ^ (-4 : ℝ) * Real.exp (2 * |Real.log ‖x‖|) =
      originLateralPlaneDensity x := by
  rw [originLateralPlaneDensity, Real.rpow_def_of_pos (normPlus_pos x),
    Real.rpow_def_of_pos (norm_pos_iff.mpr hx), ← Real.exp_add,
    log_normPlus_eq_max_log hx]
  congr 1
  rcases le_total 0 (Real.log ‖x‖) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]
    ring
  · rw [max_eq_left h, abs_of_nonpos h]
    ring

/-- The same reference identity retains the literal charge normalization `γ Q`. -/
theorem originLateralPlaneDensity_charge_identity (γ : ℝ) (hγ : γ ≠ 0)
    (x : ℂ) (hx : x ≠ 0) :
    normPlus x ^ (-4 : ℝ) *
      Real.exp ((γ * Q γ - γ ^ 2 / 2) * |Real.log ‖x‖|) =
      originLateralPlaneDensity x := by
  rw [gamma_mul_Q_eq γ hγ, add_sub_cancel_right]
  exact originLateralPlaneDensity_radial_identity x hx

/-- Index every allowed cutoff on one local chart. -/
abbrev OriginLateralChartCutoff (ρ : ℝ) := {p : ℝ × ℂ //
  0 < p.1 ∧ p.1 ≤ min ρ 1 ∧ p.2 ∈ originLateralChart ρ}

/-- A local chart cutoff is an actual circle outside the clamping disk. -/
noncomputable def originCircleCutoffOfChart (ρ : ℝ) (hρ : 0 < ρ)
    (p : OriginLateralChartCutoff ρ) : OriginCircleCutoff :=
  ⟨(ρ, (p.val.2, Real.log (1 / p.val.1))), hρ,
    originLateralChart_cutoff_lower ρ p.val.1 p.val.2 p.property.2.2 p.property.1
      (p.property.2.1.trans (min_le_left _ _))⟩

/-- On a local chart the clamped sample equals the literal orthogonal cutoff at every
sample, since the integration measure is supported where the clamp is inactive. -/
theorem originLateralCircleRegularization_eq_cutoff
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (p : OriginLateralChartCutoff ρ) (ω : Ω) :
    originLateralCircleRegularization Xc ρ ω p.val.1 p.val.2 =
      originCircleLateralCutoff Xc (originCircleCutoffOfChart ρ hρ p) ω := by
  unfold originLateralCircleRegularization clampedCircleLateralSample
    clampedCircleRadialSample originCircleLateralCutoff originCircleCutoffOfChart
  congr 1
  apply integral_congr_ae
  filter_upwards [circle_norm_lower_ae p.val.2 (Real.log (1 / p.val.1)) ρ
    (originLateralChart_cutoff_lower ρ p.val.1 p.val.2 p.property.2.2 p.property.1
      (p.property.2.1.trans (min_le_left _ _)))] with z hz
  rw [clampedLogRadius_eq ρ z hz]

/-- The entire local chart cutoff family is independent of the full continuous radial
path. All spatial points and allowed radii occur in the right-hand coordinate family. -/
theorem originRadialPath_lateralChartCutoffs_indepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    IndepFun (originRadialPath Xc)
      (fun ω => fun p : OriginLateralChartCutoff ρ =>
        originLateralCircleRegularization Xc ρ ω p.val.1 p.val.2) P := by
  let restrict : (OriginCircleCutoff → ℝ) → (OriginLateralChartCutoff ρ → ℝ) :=
    fun f p => f (originCircleCutoffOfChart ρ hρ p)
  have hmrestrict : Measurable restrict :=
    Measurable.of_eval (fun p => measurable_pi_apply (originCircleCutoffOfChart ρ hρ p))
  have hi := (originRadialPath_circleLateralCutoff_indepFun P X Xc hX hc hm hcont).comp
    measurable_id hmrestrict
  apply hi.congr EventuallyEq.rfl
  exact ae_of_all P fun ω => funext fun p =>
    (originLateralCircleRegularization_eq_cutoff Xc ρ hρ p ω).symm



/-- The cutoff ceiling in the local chart is strictly positive. -/
theorem originLateralChart_cutoffPositive (ρ : ℝ) (hρ : 0 < ρ) : 0 < min ρ 1 :=
  lt_min hρ zero_lt_one

/-- Enlarging the excluded disk shrinks the corresponding chart. -/
theorem originLateralChart_antitone {ρ σ : ℝ} (h : ρ ≤ σ) :
    originLateralChart σ ⊆ originLateralChart ρ := by
  intro x hx
  exact (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hx


/-- At the exponential cutoff the Euclidean-radius family agrees with the actual
logarithmic-radius projection without a reparameterization error. -/
theorem originLateralCircleRegularization_exp_neg
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ r : ℝ) (ω : Ω) (x : ℂ) :
    originLateralCircleRegularization Xc ρ ω (Real.exp (-r)) x =
      clampedCircleLateralSample Xc ρ ω x r := by
  rw [originLateralCircleRegularization, one_div, Real.log_inv, Real.log_exp, neg_neg]

/-- The radial projection converges in L² uniformly on compact sets of centers. The
limit retains the fixed clamp, so this estimate also holds outside the local chart. -/
theorem originCircleRadialL2_uniform_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ δ → ∀ x ∈ K,
      ‖originCircleRadialL2 hc ρ x (Real.log (1 / ε)) -
        circleAverageL2 hc (0, clampedLogRadius ρ x)‖ < η := by
  obtain ⟨δ, hδ, happrox⟩ := integral_circleMeasure_uniform_approx
    (fun z => circleAverageL2 hc (0, clampedLogRadius ρ z))
    (continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ) K hK η hη
  refine ⟨δ, hδ, fun ε hε hεδ x hx => ?_⟩
  apply happrox (Real.log (1 / ε)) _ x hx
  rw [one_div, Real.log_inv, neg_neg, Real.exp_log hε]
  exact hεδ

/-! ## Uniform covariance limits and admissible chaos construction -/

/-- The covariance kernel of the clamped radial point variables. -/
noncomputable def clampedRadialPointCovariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → Distr} {Xc : Ω → ℂ → ℝ → ℝ}
    (hc : IsCircleAverage P X Xc) (ρ : ℝ) (x y : ℂ) : ℝ :=
  covariance (circleAverageL2 hc (0, clampedLogRadius ρ x))
    (circleAverageL2 hc (0, clampedLogRadius ρ y)) P

/-- The point covariance is globally continuous after clamping. -/
theorem continuous_clampedRadialPointCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (ρ : ℝ) (hρ : 0 < ρ) :
    Continuous (Function.uncurry (clampedRadialPointCovariance hc ρ)) := by
  let _ := hX.1
  have heq : Function.uncurry (clampedRadialPointCovariance hc ρ) =
      fun p : ℂ × ℂ => ⟪circleAverageL2 hc (0, clampedLogRadius ρ p.1),
        circleAverageL2 hc (0, clampedLogRadius ρ p.2)⟫_ℝ := by
    funext p
    rw [Function.uncurry, clampedRadialPointCovariance, covariance_L2_eq,
      circleAverageL2_integral_eq_zero P X Xc hX hc, zero_mul, sub_zero]
  rw [heq]
  have hF := continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ
  exact (hF.comp continuous_fst).inner (hF.comp continuous_snd)

/-- Pairing a radial cutoff error with any L² variable is controlled by its Hilbert norm.
The radial variables are centered, so no error in their means remains. -/
theorem originCircleRadialL2_covariance_error_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) (r : ℝ) (V : Lp ℝ 2 P) :
    |covariance (originCircleRadialL2 hc ρ x r) V P -
      covariance (circleAverageL2 hc (0, clampedLogRadius ρ x)) V P| ≤
      ‖originCircleRadialL2 hc ρ x r - circleAverageL2 hc (0, clampedLogRadius ρ x)‖ * ‖V‖ := by
  let _ := hX.1
  rw [covariance_L2_eq, covariance_L2_eq,
    originCircleRadialL2_integral_eq_zero P X Xc hX hc ρ hρ x r,
    circleAverageL2_integral_eq_zero P X Xc hX hc, zero_mul, sub_zero, sub_zero,
    ← inner_sub_left, ← Real.norm_eq_abs]
  exact norm_inner_le_norm _ _

/-- Point radial variables and radial circle averages share one positive bound on a
compact set, uniformly in all circle radii at most `ρ`. -/
theorem originCircleRadialL2_point_uniform_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ L : ℝ, 0 < L ∧
      (∀ x ∈ K, ‖circleAverageL2 hc (0, clampedLogRadius ρ x)‖ ≤ L) ∧
      ∀ ε, 0 < ε → ε ≤ ρ → ∀ x ∈ K,
        ‖originCircleRadialL2 hc ρ x (Real.log (1 / ε))‖ ≤ L := by
  obtain ⟨R, hR, hb⟩ := originCircleRadialL2_uniform_bound P X Xc hX hc ρ hρ K hK
  obtain ⟨S, hS⟩ := hK.bddAbove_image
    (continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ).norm.continuousOn
  refine ⟨max R S + 1, ?_, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (hR.trans (le_max_left _ _)) zero_lt_one
  · intro x hx
    exact (hS (mem_image_of_mem _ hx)).trans
      ((le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one))
  · intro ε hε hερ x hx
    exact (hb ε hε hερ x hx).trans
      ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))

/-- The radial covariance converges uniformly when one cutoff goes to zero, against
every variable in a fixed bounded L² ball. This includes every fixed coarse circle. -/
theorem originCircleRadialL2_uniform_covariance_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (L : ℝ) (hL : 0 < L) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ δ → ∀ x ∈ K,
      ∀ V : Lp ℝ 2 P, ‖V‖ ≤ L →
        |covariance (originCircleRadialL2 hc ρ x (Real.log (1 / ε))) V P -
          covariance (circleAverageL2 hc (0, clampedLogRadius ρ x)) V P| < η := by
  obtain ⟨δ, hδ, happrox⟩ := originCircleRadialL2_uniform_approx
    P X Xc hX hc ρ hρ K hK (η / L) (div_pos hη hL)
  refine ⟨δ, hδ, fun ε hε hεδ x hx V hV => ?_⟩
  have hb := originCircleRadialL2_covariance_error_le P X Xc hX hc ρ hρ x
    (Real.log (1 / ε)) V
  have hmul := mul_lt_mul_of_pos_right (happrox ε hε hεδ x hx) hL
  rw [div_mul_cancel₀ _ hL.ne'] at hmul
  exact (hb.trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))).trans_lt hmul

/-- Both radial cutoff covariances converge to the continuous point kernel uniformly on
compact sets, without requiring the two cutoff radii to be equal. -/
theorem originCircleRadialL2_uniform_mixed_covariance_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε', 0 < ε → ε ≤ min δ ρ → 0 < ε' → ε' ≤ min δ ρ →
      ∀ x ∈ K, ∀ y ∈ K,
        |covariance (originCircleRadialL2 hc ρ x (Real.log (1 / ε)))
            (originCircleRadialL2 hc ρ y (Real.log (1 / ε'))) P -
          clampedRadialPointCovariance hc ρ x y| < η := by
  obtain ⟨L, hL, hpoint, hcircle⟩ := originCircleRadialL2_point_uniform_bound P X Xc hX hc ρ hρ K hK
  obtain ⟨δ, hδ, happrox⟩ := originCircleRadialL2_uniform_covariance_approx
    P X Xc hX hc ρ hρ K hK L hL (η / 2) (half_pos hη)
  refine ⟨δ, hδ, ?_⟩
  intro ε ε' hε hεδ hε' hε'δ x hx y hy
  have h1 := happrox ε hε (hεδ.trans (min_le_left _ _)) x hx
    (originCircleRadialL2 hc ρ y (Real.log (1 / ε')))
    (hcircle ε' hε' (hε'δ.trans (min_le_right _ _)) y hy)
  have h2 := happrox ε' hε' (hε'δ.trans (min_le_left _ _)) y hy
    (circleAverageL2 hc (0, clampedLogRadius ρ x)) (hpoint x hx)
  rw [covariance_comm (originCircleRadialL2 hc ρ y _),
    covariance_comm (circleAverageL2 hc (0, clampedLogRadius ρ y))] at h2
  exact (abs_sub_le _ _ _).trans_lt ((add_lt_add h1 h2).trans_eq (add_halves η))

/-- The separated off-diagonal covariance limit for the actual orthogonal regularizer
subtracts the continuous radial point kernel from the equator field's regular part. -/
theorem originLateralCircleRegularization_offDiagonalLimit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ H : ℂ → ℂ → ℝ, ContinuousOn (Function.uncurry H)
      (originLateralChart ρ ×ˢ originLateralChart ρ) ∧
      ∀ K, IsCompact K → K ⊆ originLateralChart ρ → ∀ s : ℝ, 0 < s → ∀ η : ℝ, 0 < η →
        ∃ δ : ℝ, 0 < δ ∧ ∀ ε ε', 0 < ε → ε ≤ min δ (min ρ 1) →
          0 < ε' → ε' ≤ min δ (min ρ 1) → ∀ x ∈ K, ∀ y ∈ K, s ≤ ‖x - y‖ →
            |gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
                (fun ω => originLateralCircleRegularization Xc ρ ω ε' y) -
              (Real.log (1 / ‖x - y‖) + H x y)| < η := by
  have hCircle := isCircleAverage_admissible P X hX Xc hc
    (originLateralChart ρ) (isOpen_originLateralChart ρ)
  obtain ⟨H, hH, hlim⟩ := hCircle.offDiagonalLimit
  refine ⟨fun x y => H x y - clampedRadialPointCovariance hc ρ x y,
    hH.sub (continuous_clampedRadialPointCovariance P X Xc hX hc ρ hρ).continuousOn, ?_⟩
  intro K hK hKU s hs η hη
  obtain ⟨δC, hδC, hC⟩ := hlim K hK hKU s hs (η / 2) (half_pos hη)
  obtain ⟨δR, hδR, hR⟩ := originCircleRadialL2_uniform_mixed_covariance_approx
    P X Xc hX hc ρ hρ K hK (η / 2) (half_pos hη)
  refine ⟨min δC δR, lt_min hδC hδR, ?_⟩
  intro ε ε' hε hεδ hε' hε'δ x hx y hy hxy
  have hεC : ε ≤ min δC 1 := le_min
    (hεδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (hεδ.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hε'C : ε' ≤ min δC 1 := le_min
    (hε'δ.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (hε'δ.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεR : ε ≤ min δR ρ := le_min
    (hεδ.trans ((min_le_left _ _).trans (min_le_right _ _)))
    (hεδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hε'R : ε' ≤ min δR ρ := le_min
    (hε'δ.trans ((min_le_left _ _).trans (min_le_right _ _)))
    (hε'δ.trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h1 := hC ε ε' hε hεC hε' hε'C x hx y hy hxy
  have h2 := hR ε ε' hε hεR hε' hε'R x hx y hy
  rw [originLateralCircleRegularization_gaussianCovariance P X Xc hX hc hm ρ hρ,
    originCircleLateralL2_covariance_expansion P X Xc hX hc ρ ρ hρ hρ x y _ _
      (originLateralChart_cutoff_lower ρ ε x (hKU hx) hε (hεR.trans (min_le_right _ _)))
      (originLateralChart_cutoff_lower ρ ε' y (hKU hy) hε' (hε'R.trans (min_le_right _ _))),
    ← gaussianCovariance_circleL2_eq P X Xc hX hc]
  have halg : ∀ a b c d e : ℝ, (a - b) - (c + (d - e)) = (a - (c + d)) - (b - e) :=
    by intros; ring
  rw [halg]
  exact (abs_sub _ _).trans_lt ((add_lt_add h1 h2).trans_eq (add_halves η))

/-- The mixed fixed-coarse covariance limit of the lateral regularizer subtracts the
radial point/coarse covariance from the equator field's fixed-coarse kernel. -/
theorem originLateralCircleRegularization_fixedCoarseLimit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ coarseKernel : ℕ → ℂ → ℂ → ℝ,
      ∀ K, IsCompact K → K ⊆ originLateralChart ρ → ∀ k : ℕ,
        Real.exp (-(k : ℝ)) ≤ min ρ 1 → ∀ η : ℝ, 0 < η →
          ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ min δ (min ρ 1) →
            ∀ x ∈ K, ∀ y ∈ K,
              |gaussianCovariance P (fun ω => originLateralCircleRegularization Xc ρ ω ε x)
                  (fun ω => originLateralCircleRegularization Xc ρ ω (Real.exp (-(k : ℝ))) y) -
                coarseKernel k x y| < η := by
  have hCircle := isCircleAverage_admissible P X hX Xc hc
    (originLateralChart ρ) (isOpen_originLateralChart ρ)
  obtain ⟨C, hlim⟩ := hCircle.fixedCoarseLimit
  refine ⟨fun k x y => C k x y -
    covariance (circleAverageL2 hc (0, clampedLogRadius ρ x)) (originCircleRadialL2 hc ρ y k) P, ?_⟩
  intro K hK hKU k hk η hη
  obtain ⟨δC, hδC, hC⟩ := hlim K hK hKU k (hk.trans (min_le_right _ _))
    (η / 2) (half_pos hη)
  obtain ⟨L, hL, _, hcircle⟩ := originCircleRadialL2_point_uniform_bound P X Xc hX hc ρ hρ K hK
  obtain ⟨δR, hδR, hR⟩ := originCircleRadialL2_uniform_covariance_approx
    P X Xc hX hc ρ hρ K hK L hL (η / 2) (half_pos hη)
  refine ⟨min δC δR, lt_min hδC hδR, ?_⟩
  intro ε hε hεδ x hx y hy
  have hεC : ε ≤ min δC 1 := le_min
    (hεδ.trans ((min_le_left _ _).trans (min_le_left _ _)))
    (hεδ.trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hεR : ε ≤ δR := hεδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hερ : ε ≤ ρ := hεδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h1 := hC ε hε hεC x hx y hy
  have hybound : ‖originCircleRadialL2 hc ρ y (k : ℝ)‖ ≤ L := by
    have h := hcircle (Real.exp (-(k : ℝ))) (Real.exp_pos _)
      (hk.trans (min_le_left _ _)) y hy
    simpa only [one_div, Real.log_inv, Real.log_exp, neg_neg] using h
  have h2 := hR ε hε hεR x hx (originCircleRadialL2 hc ρ y k) hybound
  rw [originLateralCircleRegularization_gaussianCovariance P X Xc hX hc hm ρ hρ,
    originCircleLateralL2_covariance_expansion P X Xc hX hc ρ ρ hρ hρ x y _ _
      (originLateralChart_cutoff_lower ρ ε x (hKU hx) hε hερ)
      (originLateralChart_cutoff_lower ρ (Real.exp (-(k : ℝ))) y (hKU hy)
        (Real.exp_pos _) (hk.trans (min_le_left _ _))),
    ← gaussianCovariance_circleL2_eq P X Xc hX hc]
  simp only [one_div, Real.log_inv, Real.log_exp, neg_neg] at h1 h2 ⊢
  have halg : ∀ a b c d : ℝ, (a - b) - (c - d) = (a - c) - (b - d) := by intros; ring
  rw [halg]
  exact (abs_sub _ _).trans_lt ((add_lt_add h1 h2).trans_eq (add_halves η))

/-- The actual clamped orthogonal circle regularizer is admissible on each local chart,
with the flat cylinder reference density in plane coordinates. -/
theorem originLateralCircleRegularization_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    IsAdmissibleLogRegularization P (originLateralChart ρ) originLateralPlaneDensity
      (min ρ 1) (originLateralCircleRegularization Xc ρ) := by
  exact {
    measurableAtScale := originLateralCircleRegularization_measurableAtScale Xc hm ρ hρ
    openChart := isOpen_originLateralChart ρ
    densityContinuous := continuousOn_originLateralPlaneDensity ρ hρ
    densityPositive := originLateralPlaneDensity_pos ρ hρ
    cutoffPositive := originLateralChart_cutoffPositive ρ hρ
    gaussian := fun n q _ => originLateralCircleRegularization_gaussian P X Xc hX hc hm ρ hρ n q
    covarianceBound := originLateralCircleRegularization_covarianceBound P X Xc hX hc hm ρ hρ
    coarseVarianceBound := originLateralCircleRegularization_coarseVarianceBound P X Xc hX hc hm ρ hρ
    coarseMixedBound := originLateralCircleRegularization_coarseMixedBound P X Xc hX hc hm ρ hρ
    offDiagonalLimit := originLateralCircleRegularization_offDiagonalLimit P X Xc hX hc hm ρ hρ
    fixedCoarseLimit := originLateralCircleRegularization_fixedCoarseLimit P X Xc hX hc hm ρ hρ }


/-- The clamped point kernel agrees with the actual radial covariance on the local chart,
and its diagonal is the Brownian radial variance `|log |x||`. -/
theorem clampedRadialPointCovariance_self
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (x : ℂ) (hx : ρ ≤ ‖x‖) :
    clampedRadialPointCovariance hc ρ x x = |Real.log ‖x‖| := by
  rw [clampedRadialPointCovariance, clampedLogRadius_eq ρ x hx,
    covariance_congr_ae (circleAverageL2_ae_eq hc _) (circleAverageL2_ae_eq hc _),
    origin_circle_radial_covariance X Xc hX hc, originRadialCovariance, min_self, neg_neg]
  rcases le_total 0 (Real.log ‖x‖) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]
    ring
  · rw [max_eq_left h, abs_of_nonpos h]
    ring

/-- The radial cutoff variance converges uniformly on the local chart to the literal
Brownian variance. This is the deterministic correction in the polar Wick limit. -/
theorem originCircleRadialL2_uniform_variance_approx
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε, 0 < ε → ε ≤ min δ ρ → ∀ x ∈ K,
      |gaussianVariance P (originCircleRadialL2 hc ρ x (Real.log (1 / ε))) -
        (|Real.log ‖x‖|)| < η := by
  obtain ⟨δ, hδ, happrox⟩ := originCircleRadialL2_uniform_mixed_covariance_approx
    P X Xc hX hc ρ hρ K hK η hη
  refine ⟨δ, hδ, fun ε hε hεδ x hx => ?_⟩
  have h := happrox ε ε hε hεδ hε hεδ x hx x hx
  have hxρ : ρ ≤ ‖x‖ := by
    have hxU : 2 * ρ < ‖x‖ := hKU hx
    linarith only [hxU, hρ]
  rw [clampedRadialPointCovariance_self P X Xc hX hc ρ x hxρ] at h
  simpa only [gaussianVariance, gaussianCovariance, ProbabilityTheory.covariance,
    originCircleRadialL2_integral_eq_zero P X Xc hX hc ρ hρ, sub_zero] using h


/-- Start the local path at a scale whose Euclidean circle radius is below both the
clamping radius and one. -/
noncomputable def originLateralCutoffBaseTime (ρ : ℝ) : ℝ := |Real.log ρ| + 1

/-- The base cutoff and every subsequent cutoff are in the allowed chart range. -/
theorem originLateralCutoffBaseTime_radius_le (ρ : ℝ) (hρ : 0 < ρ) (t : ℝ≥0) :
    Real.exp (-(originLateralCutoffBaseTime ρ + (t : ℝ))) ≤ min ρ 1 := by
  apply le_min
  · calc Real.exp (-(originLateralCutoffBaseTime ρ + (t : ℝ))) ≤ Real.exp (Real.log ρ) := by
           apply Real.exp_le_exp.mpr
           have h := neg_abs_le (Real.log ρ)
           dsimp [originLateralCutoffBaseTime]
           linarith only [h, t.coe_nonneg]
         _ = ρ := Real.exp_log hρ
  · apply Real.exp_le_one_iff.mpr
    dsimp [originLateralCutoffBaseTime]
    linarith only [abs_nonneg (Real.log ρ), t.coe_nonneg]

/-- The local cutoff path uses every chart center and all subsequent nonnegative times. -/
abbrev OriginLateralCutoffDomain (ρ : ℝ) := originLateralChart ρ × ℝ≥0

instance originLateralChart_locallyCompactSpace (ρ : ℝ) :
    LocallyCompactSpace (originLateralChart ρ) :=
  (isOpen_originLateralChart ρ).locallyCompactSpace

/-- Pack the whole local cutoff field as a continuous function on its locally compact
domain. On the common continuity event this agrees at every coordinate. -/
noncomputable def originLateralCutoffPath
    {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ) (ρ : ℝ) (ω : Ω) :
    C(OriginLateralCutoffDomain ρ, ℝ) :=
  ContinuousMap.mkD (fun p => clampedCircleLateralSample Xc ρ ω p.1.val
    (originLateralCutoffBaseTime ρ + (p.2 : ℝ))) 0

/-- One probability-one event identifies every coordinate of the packed cutoff path. -/
theorem originLateralCutoffPath_eval_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᵐ ω ∂P, ∀ p : OriginLateralCutoffDomain ρ,
      originLateralCutoffPath Xc ρ ω p = clampedCircleLateralSample Xc ρ ω p.1.val
        (originLateralCutoffBaseTime ρ + (p.2 : ℝ)) := by
  filter_upwards [hcont] with ω hω p
  apply ContinuousMap.mkD_apply_of_continuous
  exact (continuous_clampedCircleLateralSample Xc ρ hρ ω hω).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_const.add (NNReal.continuous_coe.comp continuous_snd)))

/-- Dense coordinate evaluations give almost-everywhere measurability of the full local
cutoff path as a continuous-function-valued random variable. -/
theorem originLateralCutoffPath_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) : AEMeasurable (originLateralCutoffPath Xc ρ) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (OriginLateralCutoffDomain ρ)
  let _ := hDc.to_subtype
  let E : C(OriginLateralCutoffDomain ρ, ℝ) → (D → ℝ) := fun f p => f p.val
  have hmE : Measurable E := Measurable.of_eval (fun p => ContinuousMap.measurable_eval p.val)
  have hinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.ext
    exact congrFun (hDd.denseRange_val.equalizer f.continuous g.continuous hfg)
  apply (hmE.measurableEmbedding hinj).aemeasurable_comp_iff.mp
  apply AEMeasurable.of_eval
  intro p
  have hEval : Measurable (fun ω => clampedCircleLateralSample Xc ρ ω p.val.1.val
      (originLateralCutoffBaseTime ρ + (p.val.2 : ℝ))) := by
    change Measurable ((fun q : Ω × (ℂ × ℝ) => clampedCircleLateralSample Xc ρ q.1 q.2.1 q.2.2) ∘
      fun ω : Ω => (ω, (p.val.1.val, originLateralCutoffBaseTime ρ + (p.val.2 : ℝ))))
    exact (measurable_clampedCircleLateralSample Xc hm ρ hρ).comp
      (measurable_id.prodMk measurable_const)
  exact hEval.aemeasurable.congr ((originLateralCutoffPath_eval_ae P Xc hcont ρ hρ).mono
    (fun ω hω => (hω p.val).symm))

/-- Every path coordinate is a valid local chart cutoff. -/
noncomputable def originLateralChartCutoffOfDomain (ρ : ℝ) (hρ : 0 < ρ)
    (p : OriginLateralCutoffDomain ρ) : OriginLateralChartCutoff ρ :=
  ⟨(Real.exp (-(originLateralCutoffBaseTime ρ + (p.2 : ℝ))), p.1.val),
    Real.exp_pos _, originLateralCutoffBaseTime_radius_le ρ hρ p.2, p.1.property⟩

/-- The entire continuous cutoff path is independent of the full radial Brownian path.
This makes continuous spatial integrals measurable functionals of independent carriers. -/
theorem originRadialPath_lateralCutoffPath_indepFun
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) :
    IndepFun (originRadialPath Xc) (originLateralCutoffPath Xc ρ) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (OriginLateralCutoffDomain ρ)
  let _ := hDc.to_subtype
  let E : C(OriginLateralCutoffDomain ρ, ℝ) → (D → ℝ) := fun f p => f p.val
  have hmE : Measurable E := Measurable.of_eval (fun p => ContinuousMap.measurable_eval p.val)
  have hinj : Function.Injective E := by
    intro f g hfg
    apply ContinuousMap.ext
    exact congrFun (hDd.denseRange_val.equalizer f.continuous g.continuous hfg)
  have hEmb := hmE.measurableEmbedding hinj
  let restrict : (OriginLateralChartCutoff ρ → ℝ) → (D → ℝ) :=
    fun f p => f (originLateralChartCutoffOfDomain ρ hρ p.val)
  have hmrestrict : Measurable restrict :=
    Measurable.of_eval (fun p => measurable_pi_apply (originLateralChartCutoffOfDomain ρ hρ p.val))
  have hi := (originRadialPath_lateralChartCutoffs_indepFun P X Xc hX hc hm hcont ρ hρ).comp
    measurable_id hmrestrict
  have heq : (fun ω => restrict (fun p : OriginLateralChartCutoff ρ =>
      originLateralCircleRegularization Xc ρ ω p.val.1 p.val.2)) =ᵐ[P]
      E ∘ originLateralCutoffPath Xc ρ := by
    filter_upwards [originLateralCutoffPath_eval_ae P Xc hcont ρ hρ] with ω hω
    funext p
    change originLateralCircleRegularization Xc ρ ω
      (Real.exp (-(originLateralCutoffBaseTime ρ + (p.val.2 : ℝ)))) p.val.1.val =
        originLateralCutoffPath Xc ρ ω p.val
    rw [hω p.val]
    exact originLateralCircleRegularization_exp_neg Xc ρ _ ω p.val.1.val
  have hi' := hi.congr EventuallyEq.rfl heq
  change IndepFun (originRadialPath Xc) (E ∘ originLateralCutoffPath Xc ρ) P at hi'
  rw [IndepFun_iff_Indep, ← MeasurableSpace.comap_comp, hEmb.comap_eq] at hi'
  exact (IndepFun_iff_Indep _ _ P).2 hi'

end DOZZ.Proofs
