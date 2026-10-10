/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonMixture

/-!
# Actual Poisson collar L² limits in the given realization

The probability mixture transports the integrable singular physical log energy. Actual
collar covariances converge uniformly on inner disks, with independent collar indices.
Centering and the three-term variance identity prove L² Cauchy convergence. Completeness
and measurable representatives give the literal raw eLpNorm limits; Gaussian closure
constructs a jointly Gaussian Poisson family in the original probability space. Its
covariance is the genuine double Poisson boundary integral. The explicit numerator-log
formula, harmonic sample modification and Dirichlet/Markov assemblies remain separate steps.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal Distributions
namespace DOZZ.Proofs

/-- The literal two-collar density on the physical plane product. -/
theorem canonicalPoissonCollarMeasure_pair_eq_withDensity (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) :
    (canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k).prod
      (canonicalPoissonCollarMeasure c w ρ ε hρ hε hw l) =
      ((volume : Measure ℂ).prod volume).withDensity (fun p =>
        ENNReal.ofReal (canonicalPoissonCollarTest c z ρ ε hρ hε hz k p.1*
          canonicalPoissonCollarTest c w ρ ε hρ hε hw l p.2)) := by
  rw [canonicalPoissonCollarMeasure, canonicalPoissonCollarMeasure, prod_withDensity
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k).continuous.measurable.ennreal_ofReal
    (canonicalPoissonCollarTest c w ρ ε hρ hε hw l).continuous.measurable.ennreal_ofReal]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (canonicalPoissonCollarTest_nonneg c z ρ ε hρ hε hz k p.1)).symm

/-- Physical product-law integration is the actual product of the two collar tests. -/
theorem integral_canonicalPoissonCollarMeasure_pair (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) (F : ℂ × ℂ → ℝ) :
    (∫ p : ℂ × ℂ, F p ∂(canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k).prod
      (canonicalPoissonCollarMeasure c w ρ ε hρ hε hw l)) =
    ∫ p : ℂ × ℂ, canonicalPoissonCollarTest c z ρ ε hρ hε hz k p.1*
      canonicalPoissonCollarTest c w ρ ε hρ hε hw l p.2*F p ∂((volume : Measure ℂ).prod volume) := by
  rw [canonicalPoissonCollarMeasure_pair_eq_withDensity, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (mul_nonneg (canonicalPoissonCollarTest_nonneg c z ρ ε hρ hε hz k _)
      (canonicalPoissonCollarTest_nonneg c w ρ ε hρ hε hw l _)), smul_eq_mul]
  · exact (((canonicalPoissonCollarTest c z ρ ε hρ hε hz k).continuous.measurable.comp measurable_fst).mul
      ((canonicalPoissonCollarTest c w ρ ε hρ hε hw l).continuous.measurable.comp measurable_snd)).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

/-- The singular logarithm is integrable for the actual two-collar probability law. -/
theorem integrable_log_canonicalPoissonCollarMeasure_pair (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖)
      ((canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k).prod
        (canonicalPoissonCollarMeasure c w ρ ε hρ hε hw l)) := by
  rw [canonicalPoissonCollarMeasure_pair_eq_withDensity]
  have hm : Measurable (fun p : ℂ × ℂ =>
      ENNReal.ofReal (canonicalPoissonCollarTest c z ρ ε hρ hε hz k p.1*
        canonicalPoissonCollarTest c w ρ ε hρ hε hw l p.2)) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (mul_nonneg (canonicalPoissonCollarTest_nonneg c z ρ ε hρ hε hz k _)
    (canonicalPoissonCollarTest_nonneg c w ρ ε hρ hε hw l _)), smul_eq_mul]
  have h := (DOZZ.integral_complexLogKernelPair_eq_vec
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k) (canonicalPoissonCollarTest c w ρ ε hρ hε hw l)
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k).continuous
    (canonicalPoissonCollarTest c w ρ ε hρ hε hw l).continuous
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k).hasCompactSupport
    (canonicalPoissonCollarTest c w ρ ε hρ hε hw l).hasCompactSupport).1.neg
  simpa only [Pi.neg_def, mul_neg, neg_neg] using h

/-- Fubini transports the genuine singular two-collar log energy to its radial/angular mixture. -/
theorem integral_canonicalPoissonCollar_log_eq_mixture (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) :
    (∫ p : ℂ × ℂ, canonicalPoissonCollarTest c z ρ ε hρ hε hz k p.1*
      canonicalPoissonCollarTest c w ρ ε hρ hε hw l p.2*Real.log ‖p.1-p.2‖
      ∂((volume : Measure ℂ).prod volume)) =
    ∫ t : ℝ × ℝ, (∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
      Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
      ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l) := by
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  let _ := unitPoissonMeasure_isProbability c z ρ hρ hz
  let _ := unitPoissonMeasure_isProbability c w ρ hρ hw
  let ν := ((poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)).prod
    ((unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w))
  let Φ (a : (ℝ × ℝ) × (ℂ × ℂ)) := (c+(ρ+a.1.1) • a.2.1,c+(ρ+a.1.2) • a.2.2)
  have hΦ : Measurable Φ := by fun_prop
  have hf : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) := by fun_prop
  have hi : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (ν.map Φ) := by
    rw [← canonicalPoissonCollarMeasure_pair_eq_map c z w ρ ε hρ hε hz hw k l]
    exact integrable_log_canonicalPoissonCollarMeasure_pair c z w ρ ε hρ hε hz hw k l
  have hcomp := (integrable_map_measure hf.aestronglyMeasurable hΦ.aemeasurable).mp hi
  simp only [Function.comp_def] at hcomp
  calc
    _ = ∫ p : ℂ × ℂ, Real.log ‖p.1-p.2‖ ∂(canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k).prod
        (canonicalPoissonCollarMeasure c w ρ ε hρ hε hw l) :=
      (integral_canonicalPoissonCollarMeasure_pair c z w ρ ε hρ hε hz hw k l _).symm
    _ = ∫ a, Real.log ‖(Φ a).1-(Φ a).2‖ ∂ν := by
      rw [canonicalPoissonCollarMeasure_pair_eq_map, integral_map_of_stronglyMeasurable hΦ hf.stronglyMeasurable]
    _ = ∫ t, ∫ p, Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖
        ∂(unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w)
        ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l) := by
      rw [integral_prod _ hcomp]
      congr 1
      funext t
      congr 1
      funext p
      congr 2
      dsimp only [Φ]
      abel
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with t
      exact integral_unitPoissonMeasure_pair c z w ρ hρ hz hw _

/-- The genuine log energy remains integrable after the radial/angular measure transport. -/
theorem integrable_canonicalPoissonCollar_log_product (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) :
    Integrable (fun a : (ℝ × ℝ) × (ℂ × ℂ) =>
      Real.log ‖(ρ+a.1.1) • a.2.1-(ρ+a.1.2) • a.2.2‖)
      (((poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)).prod
        ((unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w))) := by
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  let _ := unitPoissonMeasure_isProbability c z ρ hρ hz
  let _ := unitPoissonMeasure_isProbability c w ρ hρ hw
  let ν := ((poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)).prod
    ((unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w))
  let Φ (a : (ℝ × ℝ) × (ℂ × ℂ)) := (c+(ρ+a.1.1) • a.2.1,c+(ρ+a.1.2) • a.2.2)
  have hΦ : Measurable Φ := by fun_prop
  have hf : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) := by fun_prop
  have hi : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1-p.2‖) (ν.map Φ) := by
    rw [← canonicalPoissonCollarMeasure_pair_eq_map c z w ρ ε hρ hε hz hw k l]
    exact integrable_log_canonicalPoissonCollarMeasure_pair c z w ρ ε hρ hε hz hw k l
  apply ((integrable_map_measure hf.aestronglyMeasurable hΦ.aemeasurable).mp hi).congr
  apply ae_of_all
  intro a
  dsimp only [Function.comp_def, Φ]
  congr 2
  abel

/-- The actual Poisson-weighted angular energy is integrable in both radial collar variables. -/
theorem integrable_canonicalPoissonCollar_angularLog (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) :
    Integrable (fun t : ℝ × ℝ => ∫ p : ℂ × ℂ,
      unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
        Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
      ((poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)) := by
  let _ := unitPoissonMeasure_isProbability c z ρ hρ hz
  let _ := unitPoissonMeasure_isProbability c w ρ hρ hw
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  apply (integrable_canonicalPoissonCollar_log_product c z w ρ ε hρ hε hz hw k l).integral_prod_left.congr
  apply ae_of_all
  intro t
  exact integral_unitPoissonMeasure_pair c z w ρ hρ hz hw _

/-- Actual two-collar energy error is bounded by the integrated absolute angular error. -/
theorem abs_canonicalPoissonCollar_log_sub_boundary_le (c z w : ℂ) (ρ ε a : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (haρ : a < ρ) (hz : ‖z-c‖ ≤ a) (hw : ‖w-c‖ ≤ a) (k l : ℕ) :
    |(∫ p : ℂ × ℂ, canonicalPoissonCollarTest c z ρ ε hρ hε (mem_ball_iff_norm.mpr (hz.trans_lt haρ)) k p.1*
      canonicalPoissonCollarTest c w ρ ε hρ hε (mem_ball_iff_norm.mpr (hw.trans_lt haρ)) l p.2*
        Real.log ‖p.1-p.2‖ ∂((volume : Measure ℂ).prod volume))-
      (∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
        Real.log ‖ρ • p.1-ρ • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0))| ≤
      (ρ^2/(ρ-a)^2)^2*(∫ t : ℝ × ℝ, (∫ p : ℂ × ℂ,
        |Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
        ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)) := by
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  have hzD := mem_ball_iff_norm.mpr (hz.trans_lt haρ)
  have hwD := mem_ball_iff_norm.mpr (hw.trans_lt haρ)
  have hi := integrable_canonicalPoissonCollar_angularLog c z w ρ ε hρ hε hzD hwD k l
  have he := integrable_poissonCollar_angularLog_error ρ ε hρ hε k l
  rw [integral_canonicalPoissonCollar_log_eq_mixture]
  have hconst : (∫ _t : ℝ × ℝ, (∫ p : ℂ × ℂ,
      unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*Real.log ‖ρ • p.1-ρ • p.2‖
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
        ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)) =
      (∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
        Real.log ‖ρ • p.1-ρ • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) := by
    simp only [integral_const, probReal_univ, one_smul]
  rw [← hconst, ← integral_sub hi (integrable_const _), ← integral_const_mul]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono_ae (hi.sub (integrable_const _)).norm (he.const_mul _)
  filter_upwards [ae_poissonCollarRadiusMeasure_pair_mem ε hε k l] with t ht
  have hbound (m : ℕ) : ε/((m : ℝ)+1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_poisson_radial_circleLog_sub_le c z w ρ a (ρ+ε) (ρ+t.1) (ρ+t.2) hρ haρ hz hw
    (le_add_of_nonneg_right ht.1.1.le) (le_add_of_nonneg_right ht.2.1.le)
    (add_le_add le_rfl (ht.1.2.le.trans (hbound k))) (add_le_add le_rfl (ht.2.2.le.trans (hbound l)))

/-- The genuine two-collar log energies converge uniformly in both inner-disk parameters,
with both collar indices independently large. -/
theorem eventually_canonicalPoissonCollar_log_uniform (c : ℂ) (ρ ε a : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (haρ : a < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
      ∀ z w : ℂ, ∀ (hz : ‖z-c‖ ≤ a) (hw : ‖w-c‖ ≤ a),
        |(∫ p : ℂ × ℂ,
          canonicalPoissonCollarTest c z ρ ε hρ hε (mem_ball_iff_norm.mpr (hz.trans_lt haρ)) k p.1*
          canonicalPoissonCollarTest c w ρ ε hρ hε (mem_ball_iff_norm.mpr (hw.trans_lt haρ)) l p.2*
          Real.log ‖p.1-p.2‖ ∂((volume : Measure ℂ).prod volume))-
        (∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
          Real.log ‖ρ • p.1-ρ • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0))| < η := by
  let M := (ρ^2/(ρ-a)^2)^2
  have hM : 0 ≤ M := sq_nonneg _
  have hη' : 0 < η/(M+1) := div_pos hη (by linarith)
  obtain ⟨N,hN⟩ := eventually_poissonCollar_angularLog_error_le ρ ε hρ hε (η/(M+1)) hη'
  refine ⟨N, fun k l hk hl z w hz hw => ?_⟩
  have he := hN k l hk hl
  rw [← integral_poissonCollarRadiusMeasure_pair] at he
  have hsmall : (∫ t : ℝ × ℝ, (∫ p : ℂ × ℂ,
        |Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
          ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
          ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)) ≤ η/(M+1) :=
    (le_abs_self _).trans he
  apply (abs_canonicalPoissonCollar_log_sub_boundary_le c z w ρ ε a hρ hε haρ hz hw k l).trans_lt
  apply (mul_le_mul_of_nonneg_left hsmall hM).trans_lt
  have heq : M*(η/(M+1)) = η-η/(M+1) := by
    field_simp
    ring
  rw [heq]
  exact sub_lt_self η hη'

/-- The original pinning terms cancel exactly for every test supported inside the exterior pin. -/
theorem circleCross_exterior_origin_of_support (R : ℝ) (hR : 1 < R) (f : TestFn)
    (hf : tsupport f ⊆ ball (0 : ℂ) R) :
    circleCross 0 (-Real.log R) f = ∫ z, f z*Real.log (normPlus z) := by
  unfold circleCross
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : f z = 0
  · simp only [hz, zero_mul]
  · have hn : ‖z‖ ≤ R := by
      have hs := hf (subset_tsupport f (by simpa only [Function.mem_support] using hz))
      exact (by simpa only [mem_ball, dist_zero_right] using hs : ‖z‖ < R).le
    rw [integral_gffKernel_exterior_origin R hR, max_eq_left hn]
    ring

/-- The actual exterior-pinned covariance on the pin disk is constant minus raw log energy. -/
theorem exteriorPinned_covariance_of_support {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 1 < R)
    (f g : TestFn) (hf : tsupport f ⊆ ball (0 : ℂ) R) (hg : tsupport g ⊆ ball (0 : ℂ) R) :
    covariance (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f)
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω g) P =
      (∫ z, f z)*(∫ z, g z)*Real.log R-
        (∫ p : ℂ × ℂ, f p.1*g p.2*Real.log ‖p.1-p.2‖ ∂((volume : Measure ℂ).prod volume)) := by
  let _ := hX.1
  have hfc : covariance (fun ω => X ω f) (fun ω => Xc ω 0 (-Real.log R)) P =
      ∫ z, f z*Real.log (normPlus z) := by
    rw [covariance_comm, circleAverage_test_covariance P X Xc hX hc,
      circleCross_exterior_origin_of_support R hR f hf]
  have hgc : covariance (fun ω => Xc ω 0 (-Real.log R)) (fun ω => X ω g) P =
      ∫ z, g z*Real.log (normPlus z) := by
    rw [circleAverage_test_covariance P X Xc hX hc, circleCross_exterior_origin_of_support R hR g hg]
  have hv : variance (fun ω => Xc ω 0 (-Real.log R)) P = Real.log R := by
    rw [← covariance_self (hc.2.1 0 (-Real.log R)).aemeasurable,
      circleAverage_covariance_self X Xc hX hc, circleSelfEnergy_exterior_origin R hR]
  rw [exteriorPinnedEvaluation_covariance_expansion X Xc hX hc R, hfc, hgc, hv,
    ← densityEnergy_testFn, densityEnergy_eq_raw f.continuous g.continuous f.hasCompactSupport g.hasCompactSupport]
  have hraw : rawDensityEnergy f g =
      -(∫ p : ℂ × ℂ, f p.1*g p.2*Real.log ‖p.1-p.2‖ ∂((volume : Measure ℂ).prod volume)) := by
    unfold rawDensityEnergy
    rw [Measure.volume_eq_prod, ← integral_neg]
    congr 1
    funext p
    ring
  rw [hraw]
  ring

/-- Canonical collars stay inside the pin whenever their fixed width is below its margin. -/
theorem tsupport_canonicalPoissonCollarTest_inside_pin (c z : ℂ) (ρ ε δ R : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hεδ : ε < δ) (hc : ‖c‖+ρ+δ ≤ R) (hz : z ∈ ball c ρ) (k : ℕ) :
    tsupport (canonicalPoissonCollarTest c z ρ ε hρ hε hz k) ⊆ ball (0 : ℂ) R := by
  have hwidth : ε/((k : ℝ)+1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < (k : ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact tsupport_poissonCollarTest_inside_pin c z ρ (ε/((k : ℝ)+1)) δ R hρ (hwidth.trans_lt hεδ)
    hc hz _ _ _


/-- The actual collar covariance approaches its boundary value uniformly in both inner points. -/
theorem eventually_exteriorPinned_canonicalPoissonCollar_covariance_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε δ a : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (haρ : a < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l → ∀ z w : ℂ,
      ∀ (hz : ‖z-c‖ ≤ a) (hw : ‖w-c‖ ≤ a),
        |covariance (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
            (canonicalPoissonCollarTest c z ρ ε hρ hε (mem_ball_iff_norm.mpr (hz.trans_lt haρ)) k))
          (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
            (canonicalPoissonCollarTest c w ρ ε hρ hε (mem_ball_iff_norm.mpr (hw.trans_lt haρ)) l)) P-
          (Real.log R-(∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*
            Real.log ‖ρ • p.1-ρ • p.2‖ ∂(circleMeasure 0 0).prod (circleMeasure 0 0)))| < η := by
  obtain ⟨N,hN⟩ := eventually_canonicalPoissonCollar_log_uniform c ρ ε a hρ hε haρ η hη
  refine ⟨N, fun k l hk hl z w hz hw => ?_⟩
  rw [exteriorPinned_covariance_of_support P X Xc hX hc R hR _ _
    (tsupport_canonicalPoissonCollarTest_inside_pin c z ρ ε δ R hρ hε hεδ hpin _ k)
    (tsupport_canonicalPoissonCollarTest_inside_pin c w ρ ε δ R hρ hε hεδ hpin _ l),
    integral_canonicalPoissonCollarTest, integral_canonicalPoissonCollarTest, one_mul, one_mul]
  have he := hN k l hk hl z w hz hw
  rw [abs_sub_comm] at he
  convert he using 1
  congr 1
  ring

/-- Exterior-pinned test evaluations remain centered in the original probability space. -/
theorem exteriorPinnedEvaluation_integral_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) (f : TestFn) :
    (∫ ω, exteriorPinnedEvaluation X Xc R hR ω f ∂P) = 0 := by
  let _ := hX.1
  unfold exteriorPinnedEvaluation
  rw [integral_sub ((equatorGFF_test_memLp X hX f).integrable (by norm_num))
    (((hc.2.1 0 (-Real.log R)).mul_const (∫ z : ℂ, f z)).integrable (by norm_num)), integral_mul_const,
    equatorGFF_test_integral X hX f, (circleAverage_isGaussianProcess P X Xc hX hc).2, zero_mul, sub_self]

/-- The genuine exterior-pinned test coordinate as an element of the original L² space. -/
noncomputable def exteriorPinnedTestL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) (f : TestFn) : Lp ℝ 2 P :=
  (exteriorPinnedEvaluation_memLp X Xc hX hc R hR f).toLp
    (fun ω => exteriorPinnedEvaluation X Xc R hR ω f)

/-- The L² representative agrees almost surely with the literal test evaluation. -/
theorem exteriorPinnedTestL2_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) (f : TestFn) :
    exteriorPinnedTestL2 P X Xc hX hc R hR f =ᵐ[P]
      fun ω => exteriorPinnedEvaluation X Xc R hR ω f := MemLp.coeFn_toLp _

/-- Centering identifies the genuine L² distance with the collar increment variance. -/
theorem exteriorPinnedTestL2_norm_sub_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) (f g : TestFn) :
    ‖exteriorPinnedTestL2 P X Xc hX hc R hR f-exteriorPinnedTestL2 P X Xc hX hc R hR g‖^2 =
      variance (fun ω => exteriorPinnedEvaluation X Xc R hR ω f-
        exteriorPinnedEvaluation X Xc R hR ω g) P := by
  let _ := hX.1
  let D := exteriorPinnedTestL2 P X Xc hX hc R hR f-exteriorPinnedTestL2 P X Xc hX hc R hR g
  have hae : D =ᵐ[P] fun ω => exteriorPinnedEvaluation X Xc R hR ω f-
      exteriorPinnedEvaluation X Xc R hR ω g := by
    filter_upwards [Lp.coeFn_sub (exteriorPinnedTestL2 P X Xc hX hc R hR f)
      (exteriorPinnedTestL2 P X Xc hX hc R hR g), exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR f,
      exteriorPinnedTestL2_ae_eq P X Xc hX hc R hR g] with ω hD hf hg
    rw [hD, Pi.sub_apply, hf, hg]
  have hm : MemLp (fun ω => exteriorPinnedEvaluation X Xc R hR ω f-
      exteriorPinnedEvaluation X Xc R hR ω g) 2 P := (exteriorPinnedEvaluation_memLp X Xc hX hc R hR f).sub
    (exteriorPinnedEvaluation_memLp X Xc hX hc R hR g)
  have hmean : (∫ ω, D ω ∂P) = 0 := by
    rw [integral_congr_ae hae, integral_sub
      ((exteriorPinnedEvaluation_memLp X Xc hX hc R hR f).integrable (by norm_num))
      ((exteriorPinnedEvaluation_memLp X Xc hX hc R hR g).integrable (by norm_num)),
      exteriorPinnedEvaluation_integral_zero P X Xc hX hc,
      exteriorPinnedEvaluation_integral_zero P X Xc hX hc, sub_self]
  have hcov := covariance_L2_eq D D
  rw [hmean, zero_mul, sub_zero, real_inner_self_eq_norm_sq] at hcov
  rw [← covariance_self hm.aemeasurable, ← covariance_congr_ae hae hae, hcov]

/-- The three-term variance expansion makes actual collar evaluations uniformly L² Cauchy. -/
theorem eventually_exteriorPinned_canonicalPoissonCollar_variance_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε δ a : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (haρ : a < ρ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l → ∀ z : ℂ, ∀ (hz : ‖z-c‖ ≤ a),
      variance (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε (mem_ball_iff_norm.mpr (hz.trans_lt haρ)) k)-
        exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε (mem_ball_iff_norm.mpr (hz.trans_lt haρ)) l)) P ≤ η := by
  let _ := hX.1
  obtain ⟨N,hN⟩ := eventually_exteriorPinned_canonicalPoissonCollar_covariance_uniform
    P X Xc hX hc c R ρ ε δ a hR hρ hε hεδ hpin haρ (η/4) (by positivity)
  refine ⟨N, fun k l hk hl z hz => ?_⟩
  let F (m : ℕ) := fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
    (canonicalPoissonCollarTest c z ρ ε hρ hε (mem_ball_iff_norm.mpr (hz.trans_lt haρ)) m)
  have hkL : MemLp (F k) 2 P := exteriorPinnedEvaluation_memLp X Xc hX hc R _ _
  have hlL : MemLp (F l) 2 P := exteriorPinnedEvaluation_memLp X Xc hX hc R _ _
  have hkk := abs_lt.mp (hN k k hk hk z z hz hz)
  have hll := abs_lt.mp (hN l l hl hl z z hz hz)
  have hkl := abs_lt.mp (hN k l hk hl z z hz hz)
  have hm : AEMeasurable (fun ω => F k ω-F l ω) P := (hkL.sub hlL).aemeasurable
  change variance (fun ω => F k ω-F l ω) P ≤ η
  rw [← covariance_self hm,
    covariance_fun_sub_fun_sub hkL hlL hkL hlL, covariance_comm (F l) (F k)]
  dsimp only [F] at hkk hll hkl ⊢
  linarith

/-- At every interior point the literal Poisson collar test evaluations form a Cauchy
sequence in the original probability space's L². -/
theorem cauchySeq_exteriorPinned_canonicalPoissonCollar_L2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (hz : z ∈ ball c ρ) :
    CauchySeq (fun k => exteriorPinnedTestL2 P X Xc hX hc R (by linarith)
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)) := by
  have hz' : ‖z-c‖ < ρ := mem_ball_iff_norm.mp hz
  let a := (‖z-c‖+ρ)/2
  have haρ : a < ρ := by dsimp only [a]; linarith
  have hza : ‖z-c‖ ≤ a := by dsimp only [a]; linarith
  apply Metric.cauchySeq_iff.mpr
  intro η hη
  obtain ⟨N,hN⟩ := eventually_exteriorPinned_canonicalPoissonCollar_variance_le
    P X Xc hX hc c R ρ ε δ a hR hρ hε hεδ hpin haρ (η^2/2) (by positivity)
  refine ⟨N, fun k hk l hl => ?_⟩
  rw [dist_eq_norm]
  have he := hN k l hk hl z hza
  rw [← exteriorPinnedTestL2_norm_sub_sq P X Xc hX hc] at he
  nlinarith [norm_nonneg (exteriorPinnedTestL2 P X Xc hX hc R (by linarith)
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-exteriorPinnedTestL2 P X Xc hX hc R (by linarith)
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz l))]

/-- Completeness gives an actual Poisson functional in the original L² space. -/
theorem exists_exteriorPinned_canonicalPoissonCollar_L2limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (hz : z ∈ ball c ρ) :
    ∃ H : Lp ℝ 2 P, Tendsto (fun k => exteriorPinnedTestL2 P X Xc hX hc R (by linarith)
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)) atTop (𝓝 H) :=
  cauchySeq_tendsto_of_complete (cauchySeq_exteriorPinned_canonicalPoissonCollar_L2
    P X Xc hX hc c z R ρ ε δ hR hρ hε hεδ hpin hz)

/-- A literal collar limit has a raw measurable centered representative with the exact `eLpNorm`
error convergence required by `DOZZ.exists_exteriorPinned_markov_uniform`. -/
theorem exists_exteriorPinned_canonicalPoissonCollar_rawLimit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (hz : z ∈ ball c ρ) :
    ∃ H : Ω → ℝ, Measurable H ∧ MemLp H 2 P ∧ (∫ ω, H ω ∂P) = 0 ∧
      Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-H ω) 2 P) atTop (𝓝 0) := by
  let _ := hX.1
  obtain ⟨H,hH⟩ := exists_exteriorPinned_canonicalPoissonCollar_L2limit
    P X Xc hX hc c z R ρ ε δ hR hρ hε hεδ hpin hz
  let f := (Lp.memLp H).aestronglyMeasurable.mk (fun ω => H ω)
  have hf : Measurable f := (Lp.memLp H).aestronglyMeasurable.measurable_mk
  have heq : (fun ω => H ω) =ᵐ[P] f := (Lp.memLp H).aestronglyMeasurable.ae_eq_mk
  have hfL : MemLp f 2 P := MemLp.ae_eq heq (Lp.memLp H)
  have hto : hfL.toLp f = H := by
    apply Lp.ext
    exact hfL.coeFn_toLp.trans heq.symm
  let Z (k : ℕ) := fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)
  have hZ (k : ℕ) : MemLp (Z k) 2 P := exteriorPinnedEvaluation_memLp X Xc hX hc R _ _
  have hraw : Tendsto (fun k => eLpNorm (fun ω => Z k ω-f ω) 2 P) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Z hZ f hfL).1 (by simpa only [hto, exteriorPinnedTestL2, Z] using hH)
  refine ⟨f,hf,hfL,?_,hraw⟩
  have hm := tendsto_integral_of_eLpNorm_sub hZ hfL hraw
  have hzero : (fun k => ∫ ω, Z k ω ∂P) = fun _ => (0 : ℝ) := by
    funext k
    exact exteriorPinnedEvaluation_integral_zero P X Xc hX hc R _ _
  rw [hzero] at hm
  exact tendsto_nhds_unique hm tendsto_const_nhds

/-- Exterior pinning is a linear operation on the jointly Gaussian original test/circle family. -/
theorem exteriorPinnedEvaluation_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (R : ℝ) (hR : 0 < R) :
    IsGaussianProcess (fun f : TestFn => fun ω => exteriorPinnedEvaluation X Xc R hR ω f) P := by
  classical
  have hG := circleAverage_tests_isGaussianProcess X Xc hX hc
  apply hG.of_isGaussianProcess
  intro f
  let pin : (ℂ × ℝ) ⊕ TestFn := Sum.inl (0,-Real.log R)
  let test : (ℂ × ℝ) ⊕ TestFn := Sum.inr f
  let I : Finset ((ℂ × ℝ) ⊕ TestFn) := {test,pin}
  let a : I := ⟨test,by simp [I]⟩
  let b : I := ⟨pin,by simp [I]⟩
  let L : (I → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj a : (I → ℝ) →L[ℝ] ℝ)-
      (∫ z : ℂ, f z) • ContinuousLinearMap.proj b
  refine ⟨I,L,fun ω => ?_⟩
  simp only [L, exteriorPinnedEvaluation, sub_apply,
    smul_apply, ContinuousLinearMap.proj_apply, Finset.restrict_def,
    a, b, test, pin, Sum.elim_inr, Sum.elim_inl, smul_eq_mul, mul_comm]

/-- The literal collar limits form an actual jointly Gaussian Poisson family in the given
probability space, with measurable centered coordinates and the exact raw L² limit. -/
theorem exists_exteriorPinned_poisson_gaussian_family
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) :
    ∃ H : {z : ℂ // z ∈ ball c ρ} → Ω → ℝ, IsGaussianProcess H P ∧
      ∀ z, Measurable (H z) ∧ MemLp (H z) 2 P ∧ (∫ ω, H z ω ∂P) = 0 ∧
        Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
          (canonicalPoissonCollarTest c z.1 ρ ε hρ hε z.2 k)-H z ω) 2 P) atTop (𝓝 0) := by
  let _ := hX.1
  have hex (z : {z : ℂ // z ∈ ball c ρ}) := exists_exteriorPinned_canonicalPoissonCollar_rawLimit
    P X Xc hX hc c z.1 R ρ ε δ hR hρ hε hεδ hpin z.2
  choose H hmeas hmem hmean hlim using hex
  refine ⟨H,?_,fun z => ⟨hmeas z,hmem z,hmean z,hlim z⟩⟩
  apply isGaussianProcess_of_eLpNorm_sub
    (fun k z ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
      (canonicalPoissonCollarTest c z.1 ρ ε hρ hε z.2 k)) H
  · intro k
    simpa only [Function.comp_def] using
      (exteriorPinnedEvaluation_isGaussianProcess P X Xc hX hc R (by linarith)).comp_right
        (fun z : {z : ℂ // z ∈ ball c ρ} => canonicalPoissonCollarTest c z.1 ρ ε hρ hε z.2 k)
  · exact hmem
  · exact hlim

/-- Every raw Poisson collar limit has the genuine double-boundary covariance. -/
theorem exteriorPinned_poisson_rawLimit_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c z w : ℂ) (R ρ ε δ : ℝ) (hR : 1 < R) (hρ : 0 < ρ) (hε : 0 < ε)
    (hεδ : ε < δ) (hpin : ‖c‖+ρ+δ ≤ R) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ)
    (H J : Ω → ℝ) (hH : MemLp H 2 P) (hJ : MemLp J 2 P)
    (hHl : Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k)-H ω) 2 P) atTop (𝓝 0))
    (hJl : Tendsto (fun k => eLpNorm (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω
      (canonicalPoissonCollarTest c w ρ ε hρ hε hw k)-J ω) 2 P) atTop (𝓝 0)) :
    covariance H J P = Real.log R-(∫ p : ℂ × ℂ,
      unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*Real.log ‖ρ • p.1-ρ • p.2‖
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  let _ := hX.1
  have hcov := tendsto_covariance_of_eLpNorm_sub
    (fun k => exteriorPinnedEvaluation_memLp X Xc hX hc R _
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k))
    (fun k => exteriorPinnedEvaluation_memLp X Xc hX hc R _
      (canonicalPoissonCollarTest c w ρ ε hρ hε hw k)) hH hJ hHl hJl
  have hzw : max ‖z-c‖ ‖w-c‖ < ρ := max_lt (mem_ball_iff_norm.mp hz) (mem_ball_iff_norm.mp hw)
  let a := (max ‖z-c‖ ‖w-c‖+ρ)/2
  have haρ : a < ρ := by dsimp only [a]; linarith
  have hza : ‖z-c‖ ≤ a := by dsimp only [a]; linarith [le_max_left ‖z-c‖ ‖w-c‖]
  have hwa : ‖w-c‖ ≤ a := by dsimp only [a]; linarith [le_max_right ‖z-c‖ ‖w-c‖]
  apply tendsto_nhds_unique hcov
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨N,hN⟩ := eventually_exteriorPinned_canonicalPoissonCollar_covariance_uniform
    P X Xc hX hc c R ρ ε δ a hR hρ hε hεδ hpin haρ η hη
  refine ⟨N,fun k hk => ?_⟩
  rw [Real.dist_eq]
  exact hN k k hk hk z w hza hwa

end DOZZ.Proofs
