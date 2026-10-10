/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.AnnularComparison
public import DOZZ.Brownian.Barrier.ZeroDrift

/-!
# Charge-uniform radial comparison factors

The two continuous Brownian half-paths and their independence determine the full radial path
law. Consequently the positive compact-window attenuation has one reference expectation across
all source witnesses. A deterministic charge bound and a bounded exponent range give a uniform
positive lower factor without changing any GMC cutoff or assuming a moment of lateral chaos.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The inward half of a full radial path on the continuous Brownian carrier `BrownianPath`. -/
noncomputable def radialPositiveHalf (A : TwoSidedPath) : BrownianPath :=
  A.comp ⟨fun t : ℝ≥0 => (t : ℝ), continuous_subtype_val⟩

/-- The outward half, parameterized by positive elapsed time. -/
noncomputable def radialNegativeHalf (A : TwoSidedPath) : BrownianPath :=
  A.comp ⟨fun t : ℝ≥0 => -(t : ℝ), continuous_subtype_val.neg⟩

/-- Restricting a full path to its positive half is continuous. -/
theorem continuous_radialPositiveHalf : Continuous radialPositiveHalf :=
  ContinuousMap.continuous_precomp _

/-- Restricting a full path to its negative half is continuous. -/
theorem continuous_radialNegativeHalf : Continuous radialNegativeHalf :=
  ContinuousMap.continuous_precomp _

/-- Both halves together are a measurable embedding of the full radial path. -/
theorem measurableEmbedding_radialHalves :
    MeasurableEmbedding (fun A => (radialPositiveHalf A, radialNegativeHalf A)) := by
  have hm : Measurable (fun A => (radialPositiveHalf A, radialNegativeHalf A)) :=
    continuous_radialPositiveHalf.measurable.prodMk continuous_radialNegativeHalf.measurable
  apply hm.measurableEmbedding
  intro A A' h
  apply ContinuousMap.ext
  intro s
  by_cases hs : 0 ≤ s
  · exact congrArg (fun b : BrownianPath × BrownianPath => b.1 ⟨s, hs⟩) h
  · have hns : 0 ≤ -s := by linarith
    have he := congrArg (fun b : BrownianPath × BrownianPath => b.2 ⟨-s, hns⟩) h
    change A (-(-s)) = A' (-(-s)) at he
    simpa only [neg_neg] using he

/-- Process-coordinate independence is independence of the actual continuous half-paths. -/
theorem radialHalves_indepFun {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → TwoSidedPath)
    (hi : IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P) :
    IndepFun (fun ω => radialPositiveHalf (A ω))
      (fun ω => radialNegativeHalf (A ω)) P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (ℝ≥0)
  let _ := hDc.to_subtype
  let E : BrownianPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := Measurable.of_eval
    (fun t => ContinuousMap.measurable_eval t.1)
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    exact congrFun (hDd.denseRange_val.equalizer p.continuous q.continuous hpq)
  have hEmb := hmE.measurableEmbedding hinj
  let r : (ℝ≥0 → ℝ) → (D → ℝ) := fun p t => p t.1
  have hr : Measurable r := Measurable.of_eval (fun t => measurable_pi_apply t.1)
  have hd := hi.comp hr hr
  change IndepFun (E ∘ (fun ω => radialPositiveHalf (A ω)))
    (E ∘ (fun ω => radialNegativeHalf (A ω))) P at hd
  rw [IndepFun_iff_Indep, ← MeasurableSpace.comap_comp,
    ← MeasurableSpace.comap_comp, hEmb.comap_eq] at hd
  exact (IndepFun_iff_Indep _ _ P).mpr hd

/-- A measurable actual path half inherits the given Brownian finite laws. -/
theorem radialPositiveHalf_map_isBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (hB : IsBrownianReal (fun t ω => A ω (t : ℝ)) P) :
    IsBrownianReal (fun t p => p t) (P.map (fun ω => radialPositiveHalf (A ω))) := by
  have hm := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  refine ⟨⟨?_⟩, ae_of_all _ (fun p => p.continuous)⟩
  intro I
  have he : Measurable (fun p : BrownianPath => I.restrict (fun t => p t)) :=
    (Finset.measurable_restrict I).comp
      (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t))
  refine ⟨he.comp_aemeasurable (by exact measurable_id.aemeasurable), ?_⟩
  have hmap := AEMeasurable.map_map_of_aemeasurable he.aemeasurable hm
  exact hmap.trans (hB.hasLaw I).map_eq

/-- The outward actual half likewise inherits its Brownian finite laws. -/
theorem radialNegativeHalf_map_isBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (hB : IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P) :
    IsBrownianReal (fun t p => p t) (P.map (fun ω => radialNegativeHalf (A ω))) := by
  have hm := continuous_radialNegativeHalf.measurable.comp_aemeasurable hA
  refine ⟨⟨?_⟩, ae_of_all _ (fun p => p.continuous)⟩
  intro I
  have he : Measurable (fun p : BrownianPath => I.restrict (fun t => p t)) :=
    (Finset.measurable_restrict I).comp
      (Measurable.of_eval (fun t => ContinuousMap.measurable_eval t))
  refine ⟨he.comp_aemeasurable (by exact measurable_id.aemeasurable), ?_⟩
  have hmap := AEMeasurable.map_map_of_aemeasurable he.aemeasurable hm
  exact hmap.trans (hB.hasLaw I).map_eq

/-- The Brownian finite laws determine the entire continuous Brownian path measure. -/
theorem brownianPath_measure_unique (μ μ' : Measure BrownianPath)
    (hμ : IsBrownianReal (fun t p => p t) μ)
    (hμ' : IsBrownianReal (fun t p => p t) μ') : μ = μ' := by
  apply brownianPath_measure_eq_of_process_map_eq
  let _ := (hμ.hasLaw_eval 0).isProbabilityMeasure
  let _ := (hμ'.hasLaw_eval 0).isProbabilityMeasure
  have hm : Measurable (fun p : BrownianPath => fun t => p t) :=
    Measurable.of_eval (fun t => ContinuousMap.measurable_eval t)
  have hp := isProjectiveLimit_map (P := μ) hm.aemeasurable
  have hp' := isProjectiveLimit_map (P := μ') hm.aemeasurable
  have he : ∀ I : Finset ℝ≥0,
      μ.map (fun p => I.restrict (fun t => p t)) =
        μ'.map (fun p => I.restrict (fun t => p t)) :=
    fun I => (hμ.hasLaw I).map_eq.trans (hμ'.hasLaw I).map_eq.symm
  simp_rw [he] at hp
  exact hp.unique hp'

/-- Independent Brownian halves determine the full two-sided radial law, on any given
probability space. The independence asserted here is precisely the source radial independence. -/
theorem twoSidedRadial_map_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A A' : Ω → TwoSidedPath)
    (hA : AEMeasurable A P) (hA' : AEMeasurable A' P)
    (hBp : IsBrownianReal (fun t ω => A ω (t : ℝ)) P)
    (hBn : IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P)
    (hBp' : IsBrownianReal (fun t ω => A' ω (t : ℝ)) P)
    (hBn' : IsBrownianReal (fun t ω => A' ω (-(t : ℝ))) P)
    (hi : IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P)
    (hi' : IndepFun (fun ω => fun t : ℝ≥0 => A' ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => A' ω (-(t : ℝ))) P) : P.map A = P.map A' := by
  let _ := (hBp.hasLaw_eval 0).isProbabilityMeasure
  have hp := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA
  have hn := continuous_radialNegativeHalf.measurable.comp_aemeasurable hA
  have hp' := continuous_radialPositiveHalf.measurable.comp_aemeasurable hA'
  have hn' := continuous_radialNegativeHalf.measurable.comp_aemeasurable hA'
  have heP := brownianPath_measure_unique _ _
    (radialPositiveHalf_map_isBrownian P A hA hBp)
    (radialPositiveHalf_map_isBrownian P A' hA' hBp')
  have heN := brownianPath_measure_unique _ _
    (radialNegativeHalf_map_isBrownian P A hA hBn)
    (radialNegativeHalf_map_isBrownian P A' hA' hBn')
  apply measurableEmbedding_radialHalves.map_injective
  rw [AEMeasurable.map_map_of_aemeasurable
    measurableEmbedding_radialHalves.measurable.aemeasurable hA,
    AEMeasurable.map_map_of_aemeasurable
      measurableEmbedding_radialHalves.measurable.aemeasurable hA']
  change P.map (fun ω => (radialPositiveHalf (A ω), radialNegativeHalf (A ω))) =
    P.map (fun ω => (radialPositiveHalf (A' ω), radialNegativeHalf (A' ω)))
  have hpair := (radialHalves_indepFun P A hi).map_prod_eq_prod_map_map hp hn
  have hpair' := (radialHalves_indepFun P A' hi').map_prod_eq_prod_map_map hp' hn'
  change P.map (fun ω => (radialPositiveHalf (A ω), radialNegativeHalf (A ω))) =
    (P.map (fun ω => radialPositiveHalf (A ω))).prod
      (P.map (fun ω => radialNegativeHalf (A ω))) at hpair
  change P.map (fun ω => (radialPositiveHalf (A' ω), radialNegativeHalf (A' ω))) =
    (P.map (fun ω => radialPositiveHalf (A' ω))).prod
      (P.map (fun ω => radialNegativeHalf (A' ω))) at hpair'
  rw [hpair, hpair', heP, heN]

/-- The subcritical charge range bounds every source radial exponent by its charge-two
comparison exponent. The charge-two path weight is only a deterministic comparison function. -/
theorem lateralWindowBound_le_charge_two (γ a b : ℝ) (A : TwoSidedPath)
    (hγ : 0 < γ) (hγ2 : γ ≤ 2) :
    lateralWindowBound γ a b A ≤ lateralWindowBound 2 a b A := by
  have hcoef : |γ * Q γ| ≤ 4 := by
    rw [gamma_mul_Q_eq γ hγ.ne', abs_of_nonneg (by positivity)]
    nlinarith
  have h2 : |(2 : ℝ) * Q 2| = 4 := by norm_num [Q]
  unfold lateralWindowBound
  rw [h2, abs_of_pos hγ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact add_le_add (mul_le_mul_of_nonneg_right hγ2 (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hcoef (le_trans (abs_nonneg _) (le_max_left _ _)))

/-- One charge-two attenuation controls any smaller charge and any bounded real moment order. -/
theorem lateralMomentAttenuation_charge_two_lower (γ a b q R : ℝ) (A : TwoSidedPath)
    (hγ : 0 < γ) (hγ2 : γ ≤ 2) (hR : 0 ≤ R) (hq : |q| ≤ R) :
    lateralMomentAttenuation 2 a b R A ≤ lateralMomentAttenuation γ a b q A := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  rw [abs_of_nonneg hR, neg_mul, neg_mul]
  apply neg_le_neg
  exact mul_le_mul hq (lateralWindowBound_le_charge_two γ a b A hγ hγ2)
    (lateralWindowBound_nonneg γ a b A) hR

/-- Equal full radial laws give equal attenuation means at every fixed comparison order. -/
theorem lateralMomentAttenuation_mean_eq_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ a b q : ℝ)
    (A A' : Ω → TwoSidedPath) (hA : AEMeasurable A P) (hA' : AEMeasurable A' P)
    (hLaw : P.map A = P.map A') :
    (∫⁻ ω, lateralMomentAttenuation γ a b q (A ω) ∂P) =
      ∫⁻ ω, lateralMomentAttenuation γ a b q (A' ω) ∂P := by
  have hm := measurable_lateralMomentAttenuation γ a b q
  have he := lintegral_map' hm.aemeasurable hA
  have he' := lintegral_map' hm.aemeasurable hA'
  change (∫⁻ x, lateralMomentAttenuation γ a b q x ∂P.map A) =
    (∫⁻ ω, lateralMomentAttenuation γ a b q (A ω) ∂P) at he
  change (∫⁻ x, lateralMomentAttenuation γ a b q x ∂P.map A') =
    (∫⁻ ω, lateralMomentAttenuation γ a b q (A' ω) ∂P) at he'
  exact he.symm.trans ((congrArg (fun μ => ∫⁻ x,
    lateralMomentAttenuation γ a b q x ∂μ) hLaw).trans he')

/-- For a family of source radial witnesses with bounded charges and moment orders, the
comparison factor has a single strictly positive lower mean. This closes the radial uniformity
input in annular moment transfer without any estimate on the chaos itself. -/
theorem lateralMomentAttenuation_uniform_lower
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kq : Set ℝ)
    (hKγ : Kγ.Nonempty) (A : ℝ → Ω → TwoSidedPath)
    (hA : ∀ γ ∈ Kγ, AEMeasurable (A γ) P)
    (hBp : ∀ γ ∈ Kγ, IsBrownianReal (fun t ω => A γ ω (t : ℝ)) P)
    (hBn : ∀ γ ∈ Kγ, IsBrownianReal (fun t ω => A γ ω (-(t : ℝ))) P)
    (hi : ∀ γ ∈ Kγ, IndepFun (fun ω => fun t : ℝ≥0 => A γ ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => A γ ω (-(t : ℝ))) P)
    (hγ : ∀ γ ∈ Kγ, 0 < γ ∧ γ ≤ 2)
    (a b R : ℝ) (hR : 0 ≤ R) (hq : ∀ q ∈ Kq, |q| ≤ R) :
    ∃ η : ℝ, 0 < η ∧ ∀ γ ∈ Kγ, ∀ q ∈ Kq,
      ENNReal.ofReal η ≤ ∫⁻ ω, lateralMomentAttenuation γ a b q (A γ ω) ∂P := by
  obtain ⟨γ₀, hγ₀⟩ := hKγ
  let _ := ((hBp γ₀ hγ₀).hasLaw_eval 0).isProbabilityMeasure
  let m : ℝ≥0∞ := ∫⁻ ω, lateralMomentAttenuation 2 a b R (A γ₀ ω) ∂P
  have hm := lateralMomentAttenuation_mean_bounds P 2 a b R (A γ₀) (hA γ₀ hγ₀)
  have hmt : m ≠ ⊤ := (lt_of_le_of_lt hm.2 (by simp : (1 : ℝ≥0∞) < ⊤)).ne
  refine ⟨m.toReal, ENNReal.toReal_pos hm.1.ne' hmt, ?_⟩
  intro γ hγm q hqm
  rw [ENNReal.ofReal_toReal hmt]
  have hlaw := twoSidedRadial_map_unique P (A γ₀) (A γ)
    (hA γ₀ hγ₀) (hA γ hγm) (hBp γ₀ hγ₀) (hBn γ₀ hγ₀)
    (hBp γ hγm) (hBn γ hγm) (hi γ₀ hγ₀) (hi γ hγm)
  have he := lateralMomentAttenuation_mean_eq_of_map_eq P 2 a b R
    (A γ₀) (A γ) (hA γ₀ hγ₀) (hA γ hγm) hlaw
  change (∫⁻ ω, lateralMomentAttenuation 2 a b R (A γ₀ ω) ∂P) ≤ _
  rw [he]
  exact lintegral_mono (fun ω => lateralMomentAttenuation_charge_two_lower
    γ a b q R (A γ ω) (hγ γ hγm).1 (hγ γ hγm).2 hR (hq q hqm))

/-- The full source witness includes precisely the Brownian and independence facts used for
uniform annular comparison. They are extracted from the existing given chaos. -/
theorem sourceLateral_radial_comparison_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (γ : ℝ)
    (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ) (hS : IsSourceLateralProjection P X γ M Z) :
    ∃ A : Ω → TwoSidedPath, AEMeasurable A P ∧
      IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
      IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
      IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
        (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
      IndepFun A Z P ∧
      (∀ᵐ ω ∂P, Z ω = lateralProjectedGMC γ (A ω) (M ω)) := by
  obtain ⟨_, _, A, _, hA, _, hBp, hBn, hi, _, hInd, he⟩ := hS
  exact ⟨A, hA, hBp, hBn, hi,
    hInd.congr (Eventually.of_forall (fun _ => rfl))
      (he.mono (fun _ h => h.symm)), he⟩

/-- A compact nonempty real exponent set admits a nonnegative absolute bound. -/
theorem compact_moment_absolute_bound (Kq : Set ℝ) (hKq : IsCompact Kq)
    (hne : Kq.Nonempty) : ∃ R : ℝ, 0 ≤ R ∧ ∀ q ∈ Kq, |q| ≤ R := by
  obtain ⟨q₀, hq₀, hmax⟩ := hKq.exists_isMaxOn hne continuous_abs.continuousOn
  exact ⟨|q₀|, abs_nonneg _, fun q hq => hmax hq⟩

/-- For arbitrary given lateral chaos, compact exponent uniformity transfers from its source
annulus with no additional radial estimate. This is the complete independent assembly for the
interval moment layer; the sole analytic input is the uniform source-annulus GMC moment bound. -/
theorem lateralGMC_uniform_interval_moments_of_source_annular
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kq : Set ℝ)
    (hKq : IsCompact Kq) (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (X : ℝ → Ω → Distr) (M : ℝ → Ω → Measure ℂ)
    (hS : ∀ γ ∈ Kγ, IsSourceLateralProjection P (X γ) γ (M γ) (Z γ))
    (a b : ℝ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hAnnular : ∀ γ ∈ Kγ, ∀ q ∈ Kq,
      (∫⁻ ω, (M γ ω (lateralLogAnnulus a b)) ^ q ∂P) ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
      (∫⁻ ω, (Z γ ω (Ioc (a + t) (b + t))) ^ q ∂P) ≤ C' := by
  classical
  by_cases hneγ : Kγ.Nonempty
  · by_cases hneq : Kq.Nonempty
    · have hex : ∀ γ : ℝ, ∃ A : Ω → TwoSidedPath, γ ∈ Kγ →
          AEMeasurable A P ∧
          IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
          IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
          IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
            (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
          IndepFun A (Z γ) P ∧
          (∀ᵐ ω ∂P, Z γ ω = lateralProjectedGMC γ (A ω) (M γ ω)) := by
        intro γ
        by_cases hγ : γ ∈ Kγ
        · obtain ⟨A, hA⟩ := sourceLateral_radial_comparison_witness
            P (X γ) γ (M γ) (Z γ) (hS γ hγ)
          exact ⟨A, fun _ => hA⟩
        · exact ⟨fun _ => 0, fun hm => False.elim (hγ hm)⟩
      choose A hA using hex
      obtain ⟨R, hR, hq⟩ := compact_moment_absolute_bound Kq hKq hneq
      obtain ⟨η, hη, hRadial⟩ := lateralMomentAttenuation_uniform_lower
        P Kγ Kq hneγ A (fun γ hγ => (hA γ hγ).1)
        (fun γ hγ => (hA γ hγ).2.1) (fun γ hγ => (hA γ hγ).2.2.1)
        (fun γ hγ => (hA γ hγ).2.2.2.1)
        (fun γ hγ => ⟨(hZ γ hγ).1, (hZ γ hγ).2.1.le⟩) a b R hR hq
      exact lateralGMC_uniform_interval_moments_of_annular_comparison
        P Kγ Kq Z hZ A M (fun γ hγ => (hA γ hγ).1)
        (fun γ hγ => (hA γ hγ).2.2.2.2.1)
        (fun γ hγ => (hA γ hγ).2.2.2.2.2) a b η hη C hC hRadial hAnnular
    · refine ⟨0, by simp, ?_⟩
      intro γ hγ q hq
      exact False.elim (hneq ⟨q, hq⟩)
  · refine ⟨0, by simp, ?_⟩
    intro γ hγ
    exact False.elim (hneγ ⟨γ, hγ⟩)

/-- The source witnesses can be chosen from arbitrary given lateral chaos. A uniform annular
GMC estimate, stated for every source witness, is sufficient for the entire translated interval
conclusion. No decomposition theorem is consumed. -/
theorem lateralGMC_uniform_interval_moments_of_all_source_annular
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kq : Set ℝ)
    (hKq : IsCompact Kq) (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (a b : ℝ) (C : ℝ≥0∞) (hC : C < ⊤)
    (hAnnular : ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ X M,
      IsSourceLateralProjection P X γ M (Z γ) →
      (∫⁻ ω, (M ω (lateralLogAnnulus a b)) ^ q ∂P) ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ q ∈ Kq, ∀ t : ℝ,
      (∫⁻ ω, (Z γ ω (Ioc (a + t) (b + t))) ^ q ∂P) ≤ C' := by
  classical
  have hex : ∀ γ : ℝ, ∃ X : Ω → Distr, ∃ M : Ω → Measure ℂ,
      γ ∈ Kγ → IsSourceLateralProjection P X γ M (Z γ) := by
    intro γ
    by_cases hγ : γ ∈ Kγ
    · obtain ⟨X, M, hs⟩ := (hZ γ hγ).2.2.2.2.2.2.2.2
      exact ⟨X, M, fun _ => hs⟩
    · exact ⟨fun _ => 0, fun _ => 0, fun hm => False.elim (hγ hm)⟩
  choose X M hS using hex
  exact lateralGMC_uniform_interval_moments_of_source_annular P Kγ Kq hKq Z hZ
    X M hS a b C hC (fun γ hγ q hq => hAnnular γ hγ q hq (X γ) (M γ) (hS γ hγ))




/-- No attenuation is present at exponent zero. -/
theorem lateralMomentAttenuation_zero_order (γ a b : ℝ) (A : TwoSidedPath) :
    lateralMomentAttenuation γ a b 0 A = 1 := by
  simp [lateralMomentAttenuation]


end DOZZ.Proofs
