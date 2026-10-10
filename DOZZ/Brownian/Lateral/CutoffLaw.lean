/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.CircleRegularization

/-!
# Transporting the local lateral cutoff law

The continuous cutoff carrier permits constructing its chaos as a measurable functional
of the independent lateral path. Gaussian finite families and admissibility pass through
the cutoff-path law without changing any local covariance or normalization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Multiplying each coordinate by a deterministic scalar preserves finite centered
joint Gaussianity, including zeroed coordinates outside a local chart. -/
theorem centeredJointlyGaussian_coordinate_mul
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z) (b : ι → ℝ) :
    IsCenteredJointlyGaussian P (fun ω i => b i * Z ω i) := by
  refine ⟨hZ.1, fun i => (hZ.2.1 i).const_mul (b i), ?_⟩
  intro a
  have heq : (fun ω => ∑ i, a i * (b i * Z ω i)) =
      fun ω => ∑ i, (a i * b i) * Z ω i := by
    funext ω
    simp only [mul_assoc]
  rw [heq]
  exact hZ.2.2 (fun i => a i * b i)

/-- A finite centered Gaussian family can be read on the image probability space when
its coordinates agree almost everywhere with measurable image coordinates. -/
theorem centeredJointlyGaussian_map_of_ae_eq
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Fintype ι]
    (P : Measure Ω) (π : Ω → E) (hπ : Measurable π)
    (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (W : E → ι → ℝ) (hW : ∀ i, Measurable (fun ξ => W ξ i))
    (heq : ∀ i, (fun ω => Z ω i) =ᵐ[P] fun ω => W (π ω) i) :
    IsCenteredJointlyGaussian (P.map π) W := by
  let _ := hZ.1
  refine ⟨(Measure.isProbabilityMeasure_map_iff hπ.aemeasurable).2 inferInstance, fun i => (hW i).aemeasurable, ?_⟩
  intro a
  have hm : Measurable (fun ξ => ∑ i, a i * W ξ i) :=
    Finset.measurable_sum Finset.univ (fun i _ => (hW i).const_mul (a i))
  have hsum : (fun ω => ∑ i, a i * Z ω i) =ᵐ[P] fun ω => ∑ i, a i * W (π ω) i := by
    filter_upwards [ae_all_iff.2 heq] with ω hω
    simp only [hω]
  obtain ⟨hmem, v, hlaw⟩ := hZ.2.2 a
  refine ⟨(memLp_map_measure_iff hm.aestronglyMeasurable hπ.aemeasurable).2
    (MemLp.ae_eq hsum hmem), v, ?_⟩
  rw [Measure.map_map hm hπ]
  change P.map (fun ω => ∑ i, a i * W (π ω) i) = gaussianReal 0 v
  rw [← Measure.map_congr hsum]
  exact hlaw

/-- Restricting the cutoff ceiling preserves every admissibility clause. -/
theorem isAdmissibleLogRegularization_smaller_cutoff
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ ε₁ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₀) :
    IsAdmissibleLogRegularization P U dens ε₁ Y := by
  refine {
    measurableAtScale := hY.measurableAtScale
    openChart := hY.openChart
    densityContinuous := hY.densityContinuous
    densityPositive := hY.densityPositive
    cutoffPositive := hε₁
    gaussian := ?_
    covarianceBound := ?_
    coarseVarianceBound := ?_
    coarseMixedBound := ?_
    offDiagonalLimit := ?_
    fixedCoarseLimit := ?_ }
  · intro n q hq
    exact hY.gaussian n q (fun i => ⟨(hq i).1, (hq i).2.trans hε⟩)
  · intro K hK hKU
    obtain ⟨C, hC, hb⟩ := hY.covarianceBound K hK hKU
    exact ⟨C, hC, fun ε δ hεp hεb hδp hδb => hb ε δ hεp (hεb.trans hε) hδp (hδb.trans hε)⟩
  · intro K hK hKU
    obtain ⟨C, hC, hb⟩ := hY.coarseVarianceBound K hK hKU
    exact ⟨C, hC, fun k hk => hb k (hk.trans hε)⟩
  · intro K hK hKU
    obtain ⟨C, hC, hb⟩ := hY.coarseMixedBound K hK hKU
    exact ⟨C, hC, fun k hk => hb k (hk.trans hε)⟩
  · obtain ⟨H, hH, hb⟩ := hY.offDiagonalLimit
    refine ⟨H, hH, fun K hK hKU s hs η hη => ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := hb K hK hKU s hs η hη
    exact ⟨δ, hδ, fun ε ε' hεp hεb hε'p hε'b => hδb ε ε' hεp
      (hεb.trans (min_le_min_left δ hε)) hε'p (hε'b.trans (min_le_min_left δ hε))⟩
  · obtain ⟨C, hb⟩ := hY.fixedCoarseLimit
    refine ⟨C, fun K hK hKU k hk η hη => ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := hb K hK hKU k (hk.trans hε) η hη
    exact ⟨δ, hδ, fun ε hεp hεb => hδb ε hεp (hεb.trans (min_le_min_left δ hε))⟩

/-- Local mixed second moments are unchanged by reading the field through its image law. -/
theorem gaussianCovariance_map_of_ae_eq
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (π : Ω → E) (hπ : Measurable π)
    (Y Z : Ω → ℝ) (F G : E → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hY : Y =ᵐ[P] F ∘ π) (hZ : Z =ᵐ[P] G ∘ π) :
    gaussianCovariance (P.map π) F G = gaussianCovariance P Y Z := by
  unfold gaussianCovariance
  have hm : Measurable (fun ξ => F ξ * G ξ) := hF.mul hG
  rw [integral_map hπ.aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hY, hZ] with ω hy hz
  rw [hy, hz]
  rfl

/-- Admissibility passes to an image law when the image field agrees with the original
field on the local chart and is extended by zero off that chart. -/
theorem isAdmissibleLogRegularization_map_of_chart_ae_eq
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (π : Ω → E) (hπ : Measurable π)
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (F : E → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (hF : ∀ ε, Measurable (fun q : E × ℂ => F q.1 ε q.2))
    (hzero : ∀ ξ ε x, x ∉ U → F ξ ε x = 0)
    (heq : ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ x ∈ U,
      (fun ω => Y ω ε x) =ᵐ[P] fun ω => F (π ω) ε x) :
    IsAdmissibleLogRegularization (P.map π) U dens ε₀ F := by
  have hm (ε : ℝ) (x : ℂ) : Measurable (fun ξ => F ξ ε x) :=
    (hF ε).comp (measurable_id.prodMk measurable_const)
  have hcov (ε δ : ℝ) (hεp : 0 < ε) (hεb : ε ≤ ε₀) (hδp : 0 < δ) (hδb : δ ≤ ε₀)
      (x y : ℂ) (hx : x ∈ U) (hy : y ∈ U) :
      gaussianCovariance (P.map π) (fun ξ => F ξ ε x) (fun ξ => F ξ δ y) =
        gaussianCovariance P (fun ω => Y ω ε x) (fun ω => Y ω δ y) :=
    gaussianCovariance_map_of_ae_eq P π hπ _ _ _ _ (hm ε x) (hm δ y)
      (heq ε hεp hεb x hx) (heq δ hδp hδb y hy)
  refine {
    measurableAtScale := hF
    openChart := hY.openChart
    densityContinuous := hY.densityContinuous
    densityPositive := hY.densityPositive
    cutoffPositive := hY.cutoffPositive
    gaussian := ?_
    covarianceBound := ?_
    coarseVarianceBound := ?_
    coarseMixedBound := ?_
    offDiagonalLimit := ?_
    fixedCoarseLimit := ?_ }
  · intro n q hq
    classical
    let b : Fin n → ℝ := fun i => if (q i).2 ∈ U then 1 else 0
    have hG := centeredJointlyGaussian_coordinate_mul P _ (hY.gaussian n q hq) b
    apply centeredJointlyGaussian_map_of_ae_eq P π hπ _ hG
      (fun ξ i => F ξ (q i).1 (q i).2) (fun i => hm (q i).1 (q i).2)
    intro i
    by_cases hi : (q i).2 ∈ U
    · simpa only [b, hi, ite_true, one_mul] using heq (q i).1 (hq i).1 (hq i).2 (q i).2 hi
    · exact ae_of_all P fun ω => by
        simp only [b, hi, ite_false, zero_mul, hzero _ _ _ hi]
  · intro K hK hKU
    obtain ⟨C, hC, hb⟩ := hY.covarianceBound K hK hKU
    refine ⟨C, hC, ?_⟩
    intro ε δ hεp hεb hδp hδb x hx y hy
    rw [hcov ε δ hεp hεb hδp hδb x y (hKU hx) (hKU hy)]
    exact hb ε δ hεp hεb hδp hδb x hx y hy
  · intro K hK hKU
    obtain ⟨C, hC, hb⟩ := hY.coarseVarianceBound K hK hKU
    refine ⟨C, hC, ?_⟩
    intro k hk x hx
    rw [gaussianVariance, hcov _ _ (Real.exp_pos _) hk (Real.exp_pos _) hk x x (hKU hx) (hKU hx)]
    exact hb k hk x hx
  · intro K hK hKU
    obtain ⟨C, hC, hb⟩ := hY.coarseMixedBound K hK hKU
    refine ⟨C, hC, ?_⟩
    intro k hk ε hεp hεb x hx
    rw [hcov _ ε (Real.exp_pos _) hk hεp (hεb.trans hk) x x (hKU hx) (hKU hx)]
    exact hb k hk ε hεp hεb x hx
  · obtain ⟨H, hH, hb⟩ := hY.offDiagonalLimit
    refine ⟨H, hH, fun K hK hKU s hs η hη => ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := hb K hK hKU s hs η hη
    refine ⟨δ, hδ, ?_⟩
    intro ε ε' hεp hεb hε'p hε'b x hx y hy hxy
    rw [hcov ε ε' hεp (hεb.trans (min_le_right _ _)) hε'p
      (hε'b.trans (min_le_right _ _)) x y (hKU hx) (hKU hy)]
    exact hδb ε ε' hεp hεb hε'p hε'b x hx y hy hxy
  · obtain ⟨C, hb⟩ := hY.fixedCoarseLimit
    refine ⟨C, fun K hK hKU k hk η hη => ?_⟩
    obtain ⟨δ, hδ, hδb⟩ := hb K hK hKU k hk η hη
    refine ⟨δ, hδ, ?_⟩
    intro ε hεp hεb x hx y hy
    rw [hcov ε _ hεp (hεb.trans (min_le_right _ _)) (Real.exp_pos _) hk x y (hKU hx) (hKU hy)]
    exact hδb ε hεp hεb x hx y hy

/-- A fixed default center is needed only to extend local evaluation to the whole plane;
the universal regularizer is zero outside the chart. -/
noncomputable def originLateralChartDefault (ρ : ℝ) (hρ : 0 < ρ) : originLateralChart ρ :=
  ⟨((3 * ρ : ℝ) : ℂ), by
    change 2 * ρ < ‖((3 * ρ : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hρ.le)]
    linarith only [hρ]⟩

/-- A measurable center selector agrees with the actual center throughout the chart. -/
noncomputable def originLateralChartCenter (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ) : originLateralChart ρ := by
  classical
  exact if hx : x ∈ originLateralChart ρ then ⟨x, hx⟩ else originLateralChartDefault ρ hρ

/-- The center selector is measurable as a map to the chart subtype. -/
theorem measurable_originLateralChartCenter (ρ : ℝ) (hρ : 0 < ρ) :
    Measurable (originLateralChartCenter ρ hρ) := by
  classical
  have heq : (fun x : ℂ => (originLateralChartCenter ρ hρ x).val) =
      fun x => if x ∈ originLateralChart ρ then x else (originLateralChartDefault ρ hρ).val := by
    funext x
    by_cases hx : x ∈ originLateralChart ρ <;> simp only [originLateralChartCenter, hx,
      dite_true, dite_false, ite_true, ite_false]
  have hm : Measurable (fun x : ℂ => (originLateralChartCenter ρ hρ x).val) := by
    rw [heq]
    exact measurable_id.ite (isOpen_originLateralChart ρ).measurableSet measurable_const
  exact hm.subtype_mk

/-- The universal local regularizer evaluates a continuous lateral cutoff path at its
center and logarithmic cutoff time, with zero extension off the chart. -/
noncomputable def originLateralUniversalRegularization (ρ : ℝ) (hρ : 0 < ρ) :
    C(OriginLateralCutoffDomain ρ, ℝ) → ℝ → ℂ → ℝ := by
  classical
  exact fun f ε x => if x ∈ originLateralChart ρ then
    f (originLateralChartCenter ρ hρ x,
      (Real.log (1 / ε) - originLateralCutoffBaseTime ρ).toNNReal) else 0

/-- Universal evaluation is jointly measurable at every radius. -/
theorem originLateralUniversalRegularization_measurableAtScale (ρ : ℝ) (hρ : 0 < ρ) (ε : ℝ) :
    Measurable (fun q : C(OriginLateralCutoffDomain ρ, ℝ) × ℂ =>
      originLateralUniversalRegularization ρ hρ q.1 ε q.2) := by
  classical
  have hm : Measurable (fun q : C(OriginLateralCutoffDomain ρ, ℝ) × ℂ =>
      q.1 (originLateralChartCenter ρ hρ q.2,
        (Real.log (1 / ε) - originLateralCutoffBaseTime ρ).toNNReal)) :=
    continuous_eval.measurable.comp
      (measurable_fst.prodMk ((measurable_originLateralChartCenter ρ hρ).comp
        measurable_snd |>.prodMk measurable_const))
  exact hm.ite ((isOpen_originLateralChart ρ).measurableSet.preimage measurable_snd)
    measurable_const

/-- Off-chart evaluation is exactly zero. -/
theorem originLateralUniversalRegularization_zero (ρ : ℝ) (hρ : 0 < ρ)
    (f : C(OriginLateralCutoffDomain ρ, ℝ)) (ε : ℝ) (x : ℂ)
    (hx : x ∉ originLateralChart ρ) : originLateralUniversalRegularization ρ hρ f ε x = 0 := by
  classical
  simp only [originLateralUniversalRegularization, hx, ite_false]

/-- Below the base cutoff the logarithmic time used by universal evaluation is
nonnegative, and hence is not altered by the `toNNReal` coordinate. -/
theorem originLateralUniversal_time_nonneg (ρ ε : ℝ) (hε : 0 < ε)
    (hεb : ε ≤ Real.exp (-originLateralCutoffBaseTime ρ)) :
    0 ≤ Real.log (1 / ε) - originLateralCutoffBaseTime ρ := by
  have h := Real.log_le_log hε hεb
  rw [Real.log_exp] at h
  rw [one_div, Real.log_inv]
  linarith only [h]

/-- On the common continuity event the universal path evaluation reproduces every
local circle cutoff below its base ceiling. -/
theorem originLateralUniversalRegularization_comp_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (π : Ω → C(OriginLateralCutoffDomain ρ, ℝ))
    (hπ : π =ᵐ[P] originLateralCutoffPath Xc ρ) :
    ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ε ≤ Real.exp (-originLateralCutoffBaseTime ρ) →
      ∀ x ∈ originLateralChart ρ,
        originLateralUniversalRegularization ρ hρ (π ω) ε x =
          originLateralCircleRegularization Xc ρ ω ε x := by
  classical
  filter_upwards [hπ, originLateralCutoffPath_eval_ae P Xc hcont ρ hρ] with ω hπω hω ε hε hεb x hx
  rw [hπω]
  simp only [originLateralUniversalRegularization, hx, ite_true]
  rw [hω]
  simp only [originLateralChartCenter, hx, dite_true]
  rw [Real.coe_toNNReal _ (originLateralUniversal_time_nonneg ρ ε hε hεb), add_sub_cancel]
  rfl

/-- The law of the packed local cutoff field carries the same admissible logarithmic
regularizer. Its chaos can therefore be constructed as a measurable cutoff-path functional. -/
theorem originLateralUniversalRegularization_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ)
    (π : Ω → C(OriginLateralCutoffDomain ρ, ℝ)) (hπm : Measurable π)
    (hπ : π =ᵐ[P] originLateralCutoffPath Xc ρ) :
    IsAdmissibleLogRegularization (P.map π) (originLateralChart ρ) originLateralPlaneDensity
      (Real.exp (-originLateralCutoffBaseTime ρ)) (originLateralUniversalRegularization ρ hρ) := by
  have hceil := originLateralCutoffBaseTime_radius_le ρ hρ 0
  simp only [NNReal.coe_zero, add_zero] at hceil
  have hY := isAdmissibleLogRegularization_smaller_cutoff P (originLateralChart ρ)
    originLateralPlaneDensity (min ρ 1) (Real.exp (-originLateralCutoffBaseTime ρ))
    (originLateralCircleRegularization Xc ρ)
    (originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ) (Real.exp_pos _) hceil
  apply isAdmissibleLogRegularization_map_of_chart_ae_eq P π hπm
    (originLateralChart ρ) originLateralPlaneDensity _ _ _ hY
    (originLateralUniversalRegularization_measurableAtScale ρ hρ)
    (originLateralUniversalRegularization_zero ρ hρ)
  intro ε hε hεb x hx
  exact (originLateralUniversalRegularization_comp_ae P Xc hcont ρ hρ π hπ).mono
    (fun ω hω => (hω ε hε hεb x hx).symm)

/-- Convergence in probability on an image space pulls back to the original space. The
outer-measure bound works even before measurable versions of the scalar limit are chosen. -/
theorem tendstoInMeasure_map_comp
    {Ω E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (π : Ω → E) (hπ : Measurable π)
    (l : Filter ι) (f : ι → E → ℝ) (g : E → ℝ)
    (hfg : TendstoInMeasure (P.map π) f l g) :
    TendstoInMeasure P (fun i ω => f i (π ω)) l (fun ω => g (π ω)) := by
  intro ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hfg ε hε)
  · intro i
    exact zero_le
  · intro i
    exact Measure.le_map_apply hπ.aemeasurable {ξ | ε ≤ edist (f i ξ) (g ξ)}

/-- A local admissible chaos on an image probability space pulls back to an admissible
chaos for the original field when all sufficiently fine chart cutoffs agree on one event. -/
theorem isAdmissibleGMCVersion_map_pullback
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (π : Ω → E) (hπ : Measurable π)
    (U : Set ℂ) (hU : IsOpen U) (dens : ℂ → ℝ) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (Y : Ω → ℝ → ℂ → ℝ) (F : E → ℝ → ℂ → ℝ)
    (hF : ∀ ε, Measurable (fun q : E × ℂ => F q.1 ε q.2))
    (heq : ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ε ≤ ε₀ → ∀ x ∈ U, F (π ω) ε x = Y ω ε x)
    (γ : ℝ) (N : E → Measure ℂ) (hN : IsAdmissibleGMCVersion (P.map π) U dens F γ N) :
    IsAdmissibleGMCVersion P U dens Y γ (fun ω => N (π ω)) := by
  refine ⟨hN.1.comp hπ, fun ω => hN.2.1 (π ω),
    fun ω K hK hKU => hN.2.2.1 (π ω) K hK hKU, ?_⟩
  intro f hfc hfU
  have hconv := tendstoInMeasure_map_comp P π hπ atTop
    (fun r ξ => regularizedLogChaosTestMass (P.map π) U dens F γ r ξ f)
    (fun ξ => ∫ x, f x ∂N ξ) (hN.2.2.2 f hfc hfU)
  have hRef : ∀ᵐ x ∂logRegularizationReference U dens, x ∈ U :=
    (withDensity_absolutelyContinuous (volume.restrict U) _).ae_le (ae_restrict_mem hU.measurableSet)
  have hcoarse : ∀ᶠ r : ℝ in atTop,
      (fun ω => regularizedLogChaosTestMass (P.map π) U dens F γ r (π ω) f) =ᵐ[P]
        fun ω => regularizedLogChaosTestMass P U dens Y γ r ω f := by
    filter_upwards [eventually_ge_atTop (-Real.log ε₀)] with r hr
    have hcut : Real.exp (-r) ≤ ε₀ := by
      calc Real.exp (-r) ≤ Real.exp (Real.log ε₀) :=
             Real.exp_le_exp.mpr (by linarith only [hr])
           _ = ε₀ := Real.exp_log hε₀
    have hv (x : ℂ) (hx : x ∈ U) :
        (∫ ξ, F ξ (Real.exp (-r)) x ^ 2 ∂P.map π) =
          ∫ ω, Y ω (Real.exp (-r)) x ^ 2 ∂P := by
      have hm : Measurable (fun ξ => F ξ (Real.exp (-r)) x ^ 2) :=
        ((hF _).comp (measurable_id.prodMk measurable_const)).pow_const _
      rw [integral_map hπ.aemeasurable hm.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω _ (Real.exp_pos _) hcut x hx]
    filter_upwards [heq] with ω hω
    unfold regularizedLogChaosTestMass
    apply integral_congr_ae
    filter_upwards [hRef] with x hx
    rw [hv x hx, hω _ (Real.exp_pos _) hcut x hx]
  exact TendstoInMeasure.congr' hcoarse EventuallyEq.rfl hconv


/-- Convergence in probability for every fixed parameter integrates to convergence on a
product probability space. This is the random continuous-test step in Wick reinsertion. -/
theorem tendstoInMeasure_prod_of_sections
    {A E : Type*} [MeasurableSpace A] [MeasurableSpace E]
    (μ : Measure A) (ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : ℝ → A → E → ℝ) (g : A → E → ℝ)
    (hf : ∀ r, Measurable (Function.uncurry (f r))) (hg : Measurable (Function.uncurry g))
    (hconv : ∀ a, TendstoInMeasure ν (fun r ξ => f r a ξ) atTop (g a)) :
    TendstoInMeasure (μ.prod ν) (fun r p => f r p.1 p.2) atTop (fun p => g p.1 p.2) := by
  intro ε hε
  let B : ℝ → Set (A × E) := fun r => {p | ε ≤ edist (f r p.1 p.2) (g p.1 p.2)}
  have hB (r : ℝ) : MeasurableSet (B r) :=
    measurableSet_le measurable_const ((hf r).edist hg)
  let H : ℝ → A → ℝ≥0∞ := fun r a => ν (Prod.mk a ⁻¹' B r)
  have hHm (r : ℝ) : Measurable (H r) := measurable_measure_prodMk_left (hB r)
  have hlim : ∀ᵐ a ∂μ, Tendsto (fun r => H r a) atTop (𝓝 0) :=
    ae_of_all μ (fun a => hconv a ε hε)
  have hbound : ∀ᶠ r : ℝ in atTop, ∀ᵐ a ∂μ, H r a ≤ 1 := by
    exact Eventually.of_forall (fun r => ae_of_all μ (fun a =>
      (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : ν univ = 1)))
  have ht := tendsto_lintegral_filter_of_dominated_convergence (fun _ : A => (1 : ℝ≥0∞))
    (Eventually.of_forall hHm) hbound (by simp) hlim
  have heq : (fun r => (μ.prod ν) (B r)) = fun r => ∫⁻ a, H r a ∂μ := by
    funext r
    exact Measure.prod_apply (hB r)
  change Tendsto (fun r => (μ.prod ν) (B r)) atTop (𝓝 0)
  rw [heq]
  simpa only [lintegral_zero] using ht

/-- Independent random parameters can be inserted into the preceding product-space
limit. The whole independent lateral carrier is retained in this statement. -/
theorem tendstoInMeasure_independent_parameters
    {Ω A E : Type*} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (a : Ω → A) (π : Ω → E)
    (ha : Measurable a) (hπ : Measurable π) (hi : IndepFun a π P)
    (f : ℝ → A → E → ℝ) (g : A → E → ℝ)
    (hf : ∀ r, Measurable (Function.uncurry (f r))) (hg : Measurable (Function.uncurry g))
    (hconv : ∀ v, TendstoInMeasure (P.map π) (fun r ξ => f r v ξ) atTop (g v)) :
    TendstoInMeasure P (fun r ω => f r (a ω) (π ω)) atTop (fun ω => g (a ω) (π ω)) := by
  have ht := tendstoInMeasure_prod_of_sections (P.map a) (P.map π) f g hf hg hconv
  rw [← hi.map_prod_eq_prod_map_map ha.aemeasurable hπ.aemeasurable] at ht
  exact tendstoInMeasure_map_comp P (fun ω => (a ω, π ω)) (ha.prodMk hπ) atTop
    (fun r p => f r p.1 p.2) (fun p => g p.1 p.2) ht

end DOZZ.Proofs
