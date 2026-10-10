/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.CutoffLaw

/-!
# Radial weights in the local lateral chaos limit

Compact continuous tests remain compact after multiplication by the continuous radial
Wick weight. Independence of the whole lateral cutoff carrier permits inserting the
random radial path into the local chaos convergence, on the original probability space.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- The continuous, globally clamped radial reinsertion weight. On the local chart its
logarithmic radius is the actual logarithmic radius. -/
noncomputable def originRadialReinsertionWeight
    (ρ γ : ℝ) (A : TwoSidedPath) (x : ℂ) : ℝ :=
  Real.exp (γ * A (clampedLogRadius ρ x) -
    γ * Q γ * |clampedLogRadius ρ x|)

/-- Radial reinsertion is jointly continuous in the path and the spatial point. -/
theorem continuous_originRadialReinsertionWeight (ρ γ : ℝ) (hρ : 0 < ρ) :
    Continuous (fun p : TwoSidedPath × ℂ => originRadialReinsertionWeight ρ γ p.1 p.2) := by
  have hr : Continuous (fun p : TwoSidedPath × ℂ => clampedLogRadius ρ p.2) :=
    (continuous_clampedLogRadius ρ hρ).comp continuous_snd
  exact ((continuous_const.mul (continuous_eval.comp (continuous_fst.prodMk hr))).sub
    (continuous_const.mul hr.abs)).rexp

/-- Multiplication by the radial weight preserves the compact support of a test. -/
theorem hasCompactSupport_originRadialWeightedTest
    (ρ γ : ℝ) (A : TwoSidedPath) (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    HasCompactSupport (fun x => f x * originRadialReinsertionWeight ρ γ A x) :=
  hfc.mul_right

/-- A compact test multiplied by a radial path is a bounded continuous test. -/
noncomputable def originRadialWeightedTest
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) : BoundedContinuousFunction ℂ ℝ := by
  let F : ℂ → ℝ := fun x => f x * originRadialReinsertionWeight ρ γ A x
  have hc : Continuous F := f.continuous.mul
    ((continuous_originRadialReinsertionWeight ρ γ hρ).comp
      (continuous_const.prodMk continuous_id))
  have hb := hc.bounded_above_of_compact_support
    (hasCompactSupport_originRadialWeightedTest ρ γ A f hfc)
  exact BoundedContinuousFunction.ofNormedAddCommGroup F hc hb.choose hb.choose_spec

/-- The underlying weighted test is the literal product, independently of its chosen bound. -/
theorem originRadialWeightedTest_apply
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (x : ℂ) :
    originRadialWeightedTest ρ γ hρ A f hfc x =
      f x * originRadialReinsertionWeight ρ γ A x := rfl

/-- Weighted tests have no new support points. -/
theorem tsupport_originRadialWeightedTest_subset
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    tsupport (originRadialWeightedTest ρ γ hρ A f hfc : ℂ → ℝ) ⊆ tsupport (f : ℂ → ℝ) :=
  tsupport_mul_subset_left

/-- Joint integration of real tests against a measurable finite measure parameter. -/
theorem measurable_integral_finiteMeasure_parameter
    {V β : Type*} [MeasurableSpace V] [MeasurableSpace β]
    (F : V → β → ℝ) (hF : Measurable (Function.uncurry F))
    (hI : ∀ v (μ : FiniteMeasure β), Integrable (F v) (μ : Measure β)) :
    Measurable (fun p : V × FiniteMeasure β => ∫ x, F p.1 x ∂(p.2 : Measure β)) := by
  have hp := measurable_lintegral_finiteMeasure_parameter (ENNReal.measurable_ofReal.comp hF)
  have hn := measurable_lintegral_finiteMeasure_parameter (ENNReal.measurable_ofReal.comp hF.neg)
  have heq : (fun p : V × FiniteMeasure β => ∫ x, F p.1 x ∂(p.2 : Measure β)) =
      fun p => (∫⁻ x, ENNReal.ofReal (F p.1 x) ∂(p.2 : Measure β)).toReal -
        (∫⁻ x, ENNReal.ofReal (-F p.1 x) ∂(p.2 : Measure β)).toReal := by
    funext p
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hI p.1 p.2)
  rw [heq]
  exact hp.ennreal_toReal.sub hn.ennreal_toReal

/-- A jointly measurable bounded test with fixed compact support integrates jointly
measurably against a random measure finite on that support. -/
theorem measurable_compact_parameter_integral
    {V E : Type*} [MeasurableSpace V] [MeasurableSpace E]
    (F : V → BoundedContinuousFunction ℂ ℝ)
    (hF : Measurable (fun p : V × ℂ => F p.1 p.2))
    (K : Set ℂ) (hK : IsCompact K) (hFK : ∀ v, tsupport (F v : ℂ → ℝ) ⊆ K)
    (N : E → Measure ℂ) (hN : Measurable N) (hNfin : ∀ ξ, N ξ K < ⊤) :
    Measurable (fun p : V × E => ∫ x, F p.1 x ∂N p.2) := by
  let T : E → FiniteMeasure ℂ := fun ξ =>
    ⟨(N ξ).restrict K, ⟨by simpa only [Measure.restrict_apply_univ] using hNfin ξ⟩⟩
  have hT : Measurable T := by
    apply Measurable.subtype_mk
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have h := (Measure.measurable_coe (hs.inter hK.measurableSet)).comp hN
    change Measurable (fun ξ => N ξ (s ∩ K)) at h
    simpa only [Measure.restrict_apply hs] using h
  have hi := measurable_integral_finiteMeasure_parameter
    (fun v x => F v x) hF (fun v μ => (F v).integrable (μ := (μ : Measure ℂ)))
  have hm := hi.comp (measurable_fst.prodMk (hT.comp measurable_snd))
  have heq (v : V) (ξ : E) : (∫ x, F v x ∂(T ξ : Measure ℂ)) = ∫ x, F v x ∂N ξ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hFK v h))
  change Measurable (fun p : V × E => ∫ x, F p.1 x ∂(T p.2 : Measure ℂ)) at hm
  simpa only [heq] using hm

/-- The limiting chaos integral with the radial weighted test is jointly measurable. -/
theorem originRadialWeightedTest_integral_measurable
    {E : Type*} [MeasurableSpace E]
    (ρ γ : ℝ) (hρ : 0 < ρ) (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ))
    (N : E → Measure ℂ) (hN : Measurable N)
    (hNfin : ∀ ξ, N ξ (tsupport (f : ℂ → ℝ)) < ⊤) :
    Measurable (fun p : TwoSidedPath × E =>
      ∫ x, originRadialWeightedTest ρ γ hρ p.1 f hfc x ∂N p.2) := by
  apply measurable_compact_parameter_integral _ _ _ hfc
    (fun A => tsupport_originRadialWeightedTest_subset ρ γ hρ A f hfc) N hN hNfin
  exact (f.continuous.measurable.comp measurable_snd).mul
    (continuous_originRadialReinsertionWeight ρ γ hρ).measurable

/-- The finite Wick integral with a radial weighted test is jointly measurable, without
requiring integrability of every cutoff section. -/
theorem originRadialWeightedTest_cutoff_measurable
    {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : E → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (ρ γ : ℝ) (hρ : 0 < ρ) (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (r : ℝ) :
    Measurable (fun p : TwoSidedPath × E =>
      regularizedLogChaosTestMass P U dens Y γ r p.2
        (originRadialWeightedTest ρ γ hρ p.1 f hfc)) := by
  have hv : Measurable (fun x : ℂ => ∫ ξ, Y ξ (Real.exp (-r)) x ^ 2 ∂P) := by
    exact ((hY.measurableAtScale _).comp measurable_swap).pow_const 2
      |>.stronglyMeasurable.integral_prod_right.measurable
  have hweight : Measurable (fun p : (TwoSidedPath × E) × ℂ =>
      f p.2 * originRadialReinsertionWeight ρ γ p.1.1 p.2) :=
    (f.continuous.measurable.comp measurable_snd).mul
      ((continuous_originRadialReinsertionWeight ρ γ hρ).measurable.comp
        (measurable_fst.fst.prodMk measurable_snd))
  have hfield : Measurable (fun p : (TwoSidedPath × E) × ℂ => Y p.1.2 (Real.exp (-r)) p.2) :=
    (hY.measurableAtScale _).comp (measurable_fst.snd.prodMk measurable_snd)
  have hq := hweight.mul ((hfield.const_mul γ).sub
    ((hv.comp measurable_snd).const_mul (γ ^ 2 / 2))).exp
  exact hq.stronglyMeasurable.integral_prod_right.measurable

/-- Independence inserts an actual random radial path into the compact-test convergence
of an admissible lateral chaos on its cutoff carrier. -/
theorem originRadialWeightedTest_tendstoInMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Ω → TwoSidedPath) (π : Ω → E) (hA : Measurable A) (hπ : Measurable π)
    (hi : IndepFun A π P)
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : E → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization (P.map π) U dens ε₀ Y)
    (ρ γ : ℝ) (hρ : 0 < ρ) (N : E → Measure ℂ)
    (hN : IsAdmissibleGMCVersion (P.map π) U dens Y γ N)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ U) :
    TendstoInMeasure P
      (fun r ω => regularizedLogChaosTestMass (P.map π) U dens Y γ r (π ω)
        (originRadialWeightedTest ρ γ hρ (A ω) f hfc)) atTop
      (fun ω => ∫ x, originRadialWeightedTest ρ γ hρ (A ω) f hfc x ∂N (π ω)) := by
  let F : ℝ → TwoSidedPath → E → ℝ := fun r v ξ =>
    regularizedLogChaosTestMass (P.map π) U dens Y γ r ξ
      (originRadialWeightedTest ρ γ hρ v f hfc)
  let G : TwoSidedPath → E → ℝ := fun v ξ =>
    ∫ x, originRadialWeightedTest ρ γ hρ v f hfc x ∂N ξ
  have hmF : ∀ r, Measurable (Function.uncurry (F r)) :=
    originRadialWeightedTest_cutoff_measurable (P.map π) U dens ε₀ Y hY ρ γ hρ f hfc
  have hmG : Measurable (Function.uncurry G) :=
    originRadialWeightedTest_integral_measurable ρ γ hρ f hfc N hN.1
      (fun ξ => hN.2.2.1 ξ _ hfc hfU)
  have ht : ∀ v, TendstoInMeasure (P.map π) (fun r ξ => F r v ξ) atTop (G v) := by
    intro v
    exact hN.2.2.2 (originRadialWeightedTest ρ γ hρ v f hfc)
      (hasCompactSupport_originRadialWeightedTest ρ γ v f hfc)
      ((tsupport_originRadialWeightedTest_subset ρ γ hρ v f hfc).trans hfU)
  exact tendstoInMeasure_independent_parameters P A π hA hπ hi F G hmF hmG ht

/-- Transport of one cutoff integral holds simultaneously for arbitrary random tests:
the common chart equality concerns the field, not a preselected deterministic test. -/
theorem regularizedLogChaosTestMass_randomTest_map_comp
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (π : Ω → E) (hπ : Measurable π)
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (F : E → ℝ → ℂ → ℝ)
    (hF : ∀ ε, Measurable (fun q : E × ℂ => F q.1 ε q.2))
    (γ r : ℝ) (f : Ω → BoundedContinuousFunction ℂ ℝ)
    (heq : ∀ᵐ ω ∂P, ∀ x ∈ U, F (π ω) (Real.exp (-r)) x = Y ω (Real.exp (-r)) x) :
    (fun ω => regularizedLogChaosTestMass (P.map π) U dens F γ r (π ω) (f ω)) =ᵐ[P]
      fun ω => regularizedLogChaosTestMass P U dens Y γ r ω (f ω) := by
  have hRef : ∀ᵐ x ∂logRegularizationReference U dens, x ∈ U :=
    (withDensity_absolutelyContinuous (volume.restrict U) _).ae_le
      (ae_restrict_mem hU.measurableSet)
  have hv (x : ℂ) (hx : x ∈ U) :
      (∫ ξ, F ξ (Real.exp (-r)) x ^ 2 ∂P.map π) =
        ∫ ω, Y ω (Real.exp (-r)) x ^ 2 ∂P := by
    have hm : Measurable (fun ξ => F ξ (Real.exp (-r)) x ^ 2) :=
      ((hF _).comp (measurable_id.prodMk measurable_const)).pow_const _
    rw [integral_map hπ.aemeasurable hm.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    rw [hω x hx]
  filter_upwards [heq] with ω hω
  unfold regularizedLogChaosTestMass
  apply integral_congr_ae
  filter_upwards [hRef] with x hx
  rw [hv x hx, hω x hx]



/-- The finite radial factor used when reinserting the circle cutoff into the lateral
cutoff. Its deterministic reference correction is the literal `-2 |log |x||`. -/
noncomputable def originRadialCutoffReinsertionWeight
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Distr}
    {Xc : Ω → ℂ → ℝ → ℝ} (hc : IsCircleAverage P X Xc)
    (ρ γ r : ℝ) (A : TwoSidedPath) (x : ℂ) : ℝ :=
  Real.exp (γ * (∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) -
    γ ^ 2 / 2 * gaussianVariance P (originCircleRadialL2 hc ρ x r) -
    2 * |clampedLogRadius ρ x|)

/-- The finite reference correction is the quotient of the circle reference density by
the flat-cylinder density. The identity keeps the finite radial variance unchanged. -/
theorem originRadialCutoffReinsertionWeight_density_identity
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Distr}
    {Xc : Ω → ℂ → ℝ → ℝ} (hc : IsCircleAverage P X Xc)
    (ρ γ r : ℝ) (A : TwoSidedPath) (x : ℂ) (hx : x ≠ 0) (hρx : ρ ≤ ‖x‖) :
    normPlus x ^ (-4 : ℝ) *
        Real.exp (γ * (∫ z, A (clampedLogRadius ρ z) ∂circleMeasure x r) -
          γ ^ 2 / 2 * gaussianVariance P (originCircleRadialL2 hc ρ x r)) =
      originLateralPlaneDensity x * originRadialCutoffReinsertionWeight hc ρ γ r A x := by
  rw [originRadialCutoffReinsertionWeight, clampedLogRadius_eq ρ x hρx, abs_neg,
    ← originLateralPlaneDensity_radial_identity x hx, mul_assoc, ← Real.exp_add]
  congr 2
  ring


/-- The reinsertion factor is strictly positive at every point. -/
theorem originRadialReinsertionWeight_pos (ρ γ : ℝ) (A : TwoSidedPath) (x : ℂ) :
    0 < originRadialReinsertionWeight ρ γ A x := Real.exp_pos _

/-- The clamped reinsertion weight equals the literal polar weight on its local chart. -/
theorem originRadialReinsertionWeight_chart_eq
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (x : ℂ) (hx : x ∈ originLateralChart ρ) :
    originRadialReinsertionWeight ρ γ A x =
      Real.exp (γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖|) := by
  have hxρ : ρ ≤ ‖x‖ := by
    have h : 2 * ρ < ‖x‖ := hx
    linarith only [h, hρ]
  rw [originRadialReinsertionWeight, clampedLogRadius_eq ρ x hxρ, abs_neg]


/-- The literal removal density in the projection `DOZZ.lateralProjectedGMC`
cancels the reinsertion density on every local chart, including in extended-real
measure products. -/
theorem originRadialReinsertionWeight_removal_mul
    (ρ γ : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath) (x : ℂ) (hx : x ∈ originLateralChart ρ) :
    ENNReal.ofReal (originRadialReinsertionWeight ρ γ A x) *
      ENNReal.ofReal (if ‖x‖ = 0 then 0 else
        Real.exp (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|)) = 1 := by
  have hx0 : ‖x‖ ≠ 0 := by
    have h : 2 * ρ < ‖x‖ := hx
    exact ne_of_gt (lt_trans (by linarith only [hρ] : 0 < 2 * ρ) h)
  rw [ite_eq_right hx0, originRadialReinsertionWeight_chart_eq ρ γ hρ A x hx,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have he : γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖| +
      (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|) = 0 := by ring
  rw [he, Real.exp_zero, ENNReal.ofReal_one]

end DOZZ.Proofs
