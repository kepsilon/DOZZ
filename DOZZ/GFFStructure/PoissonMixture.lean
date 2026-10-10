/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.PoissonEnergy
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Literal collar mass, radial probability laws and mixtures

Polar integration identifies actual collar test integrals with radial mixtures of normalized
Poisson-weighted circles. Every normalized radial density gives a literal mass-one test.
The constructed smooth bump laws are probabilities with the prescribed shrinking support.
Both independently shrinking collar indices preserve the angular log-error limit, and the
corresponding radial product errors are genuine integrable observables. This prepares the
energy Fubini calculation; it does not yet construct random Poisson functionals.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal Distributions BoundedContinuousFunction
namespace DOZZ.Proofs

/-- The literal collar Jacobian cancels the polar radius at every positive radius. -/
theorem poissonCollarTest_polar_jacobian (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) (u θ : ℝ) (hu : 0 < u) :
    u*poissonCollarTest c z ρ ε hρ hz q hq hqs (c+circleMap 0 u θ) =
      q (u-ρ)/(2*Real.pi)*unitPoissonWeight c ρ z (circleMap 0 1 θ) := by
  rw [poissonCollarTest_apply]
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul]
  unfold poissonCollarValue unitPoissonWeight
  rw [poissonBoundaryDirection_polar c ρ u θ hu,
    norm_poissonPolarPoint_sub c u θ hu.le]
  simp only [Complex.real_smul]
  field_simp

/-- Polar coordinates identify the actual collar integral with its weighted circle mixture. -/
theorem integral_poissonCollarTest_mul_polar (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) (h : ℂ → ℝ) (hh : Measurable h)
    (hi : Integrable (fun w => poissonCollarTest c z ρ ε hρ hz q hq hqs w*h w)) :
    (∫ w, poissonCollarTest c z ρ ε hρ hz q hq hqs w*h w) =
      ∫ u in Ioi (0 : ℝ), q (u-ρ)*
        (∫ v, unitPoissonWeight c ρ z v*h (c+u • v) ∂circleMeasure 0 0) := by
  let p := poissonCollarTest c z ρ ε hρ hz q hq hqs
  let F (w : ℂ) := p (c+w)*h (c+w)
  have hFm : Measurable F := (p.continuous.measurable.mul hh).comp (by fun_prop)
  have hFi : Integrable F := hi.comp_add_left c
  have hp := integrable_polarJacobian hFm hFi
  have ht : (volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Complex.polarCoord_target, Measure.prod_restrict, Measure.volume_eq_prod]
  calc
    _ = ∫ w, F w := (integral_add_left_eq_self (fun w => p w*h w) c).symm
    _ = ∫ a in Complex.polarCoord.target, a.1*F (Complex.polarCoord.symm a) := by
      simpa only [smul_eq_mul, polarCoord_target, Complex.polarCoord_target] using (Complex.integral_comp_polarCoord_symm F).symm
    _ = ∫ u in Ioi (0 : ℝ), ∫ θ in Ioo (-Real.pi) Real.pi,
        u*F (Complex.polarCoord.symm (u,θ)) := by
      rw [ht] at hp ⊢
      exact integral_prod _ hp
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hpolar (θ : ℝ) : Complex.polarCoord.symm (u,θ) = circleMap 0 u θ := by
        simp only [Complex.polarCoord_symm_apply, circleMap, zero_add]
        rw [Complex.exp_mul_I]
        push_cast
        ring
      have hscale (θ : ℝ) : circleMap 0 u θ = u • circleMap 0 1 θ := by
        simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
      calc
        _ = ∫ θ in Ioo (-Real.pi) Real.pi, (q (u-ρ)/(2*Real.pi))*
            (unitPoissonWeight c ρ z (circleMap 0 1 θ)*h (c+u • circleMap 0 1 θ)) := by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro θ _
          dsimp only [F]
          rw [hpolar, ← mul_assoc, poissonCollarTest_polar_jacobian c z ρ ε hρ hz q hq hqs u θ hu,
            hscale]
          ring
        _ = (q (u-ρ)/(2*Real.pi))*(2*Real.pi*Real.circleAverage
            (fun v => unitPoissonWeight c ρ z v*h (c+u • v)) 0 1) := by
          rw [integral_const_mul, DOZZ.integral_circleAngle_eq_twoPi_mul_circleAverage
            (fun v => unitPoissonWeight c ρ z v*h (c+u • v)) 1]
        _ = q (u-ρ)*(∫ v, unitPoissonWeight c ρ z v*h (c+u • v) ∂circleMeasure 0 0) := by
          rw [integral_circleMeasure_eq_circleAverage 0 0
            (fun v => unitPoissonWeight c ρ z v*h (c+u • v))
            ((measurable_unitPoissonWeight c z ρ).mul (hh.comp (by fun_prop)))]
          simp only [neg_zero, Real.exp_zero]
          field_simp

/-- Positive radial support removes the lower polar cutoff and translates to the collar variable. -/
theorem integral_shifted_poissonDensity_mul (ρ ε : ℝ) (hρ : 0 < ρ)
    (q : ℝ → ℝ) (hqs : tsupport q ⊆ Ioo 0 ε) (A : ℝ → ℝ) :
    (∫ u in Ioi (0 : ℝ), q (u-ρ)*A u) = ∫ t, q t*A (ρ+t) := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · have h := integral_add_left_eq_self (μ := volume) (fun u : ℝ => q (u-ρ)*A u) ρ
    simpa only [add_sub_cancel_left] using h.symm
  · intro u hu
    have hq : q (u-ρ) = 0 := by
      by_contra hn
      have ht := hqs (subset_tsupport q (by simpa only [Function.mem_support] using hn))
      have hu' : u ≤ 0 := le_of_not_gt hu
      linarith [ht.1]
    rw [hq, zero_mul]

/-- Actual collars are probability mixtures of normalized Poisson-weighted circles. -/
theorem integral_poissonCollarTest_mul_eq_mixture (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) (h : ℂ → ℝ) (hh : Measurable h)
    (hi : Integrable (fun w => poissonCollarTest c z ρ ε hρ hz q hq hqs w*h w)) :
    (∫ w, poissonCollarTest c z ρ ε hρ hz q hq hqs w*h w) =
      ∫ t, q t*(∫ v, unitPoissonWeight c ρ z v*h (c+(ρ+t) • v) ∂circleMeasure 0 0) := by
  rw [integral_poissonCollarTest_mul_polar c z ρ ε hρ hz q hq hqs h hh hi]
  exact integral_shifted_poissonDensity_mul ρ ε hρ q hqs _

/-- Every normalized smooth radial collar gives an actual test of total mass one. -/
theorem integral_poissonCollarTest (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (q : ℝ → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqs : tsupport q ⊆ Ioo 0 ε) (hqone : (∫ t : ℝ, q t) = 1) :
    (∫ w, poissonCollarTest c z ρ ε hρ hz q hq hqs w) = 1 := by
  have hi : Integrable (poissonCollarTest c z ρ ε hρ hz q hq hqs) := (poissonCollarTest c z ρ ε hρ hz q hq hqs).continuous.integrable_of_hasCompactSupport
    (poissonCollarTest c z ρ ε hρ hz q hq hqs).hasCompactSupport
  have hm := integral_poissonCollarTest_mul_eq_mixture c z ρ ε hρ hz q hq hqs
    (fun _ => (1 : ℝ)) measurable_const (by simpa only [mul_one] using hi)
  simpa only [mul_one, integral_unitPoissonWeight c z ρ hρ hz, hqone] using hm

/-- A bounded continuous potential has Poisson-weighted circle means continuous in radius. -/
theorem continuous_poissonCircleMean_radius (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (h : ℂ → ℝ) (hh : Continuous h)
    (M : ℝ) (hb : ∀ w, ‖h w‖ ≤ M) :
    Continuous (fun r : ℝ => ∫ v, unitPoissonWeight c ρ z v*h (c+r • v) ∂circleMeasure 0 0) := by
  apply continuous_of_dominated
    (fun r => ((measurable_unitPoissonWeight c z ρ).mul (hh.measurable.comp (by fun_prop))).aestronglyMeasurable)
    (fun r => ?_)
    ((integrable_unitPoissonWeight c z ρ hρ hz).const_mul M)
  · filter_upwards with v
    simp only [Pi.mul_apply, Function.comp_apply]
    apply Continuous.mul continuous_const
    exact hh.comp (by fun_prop)
  · filter_upwards with v
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (unitPoissonWeight_nonneg c z v ρ hρ hz)]
    exact (mul_le_mul_of_nonneg_left (hb (c+r • v))
      (unitPoissonWeight_nonneg c z v ρ hρ hz)).trans_eq (mul_comm _ _)

/-- Normalized smooth collar densities are integrable. -/
theorem integrable_poissonCollarDensity (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    Integrable (poissonCollarDensity ε hε k) :=
  (poissonCollarDensity_contDiff ε hε k).continuous.integrable_of_hasCompactSupport
    (poissonCollarDensity_hasCompactSupport ε hε k)

/-- A continuous radial observable converges under the actual normalized shrinking bumps. -/
theorem tendsto_integral_poissonCollarDensity_mul (ε ρ : ℝ) (hε : 0 < ε)
    (A : ℝ → ℝ) (hA : Continuous A) :
    Tendsto (fun k => ∫ t, poissonCollarDensity ε hε k t*A (ρ+t)) atTop (𝓝 (A ρ)) := by
  have hwidth := tendsto_poissonCollarWidth ε
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨d, hd, hAd⟩ := Metric.continuousAt_iff.mp (hA.continuousAt (x := ρ)) (η/2) (half_pos hη)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hwidth.eventually (gt_mem_nhds hd))
  refine ⟨N, fun k hk => ?_⟩
  have hq := integrable_poissonCollarDensity ε hε k
  have hi : Integrable (fun t => poissonCollarDensity ε hε k t*A (ρ+t)) :=
    ((poissonCollarDensity_contDiff ε hε k).continuous.mul (hA.comp (by fun_prop))).integrable_of_hasCompactSupport
      (poissonCollarDensity_hasCompactSupport ε hε k).mul_right
  have hc : (∫ t, poissonCollarDensity ε hε k t*A ρ) = A ρ := by
    rw [integral_mul_const, integral_poissonCollarDensity, one_mul]
  have herror : |(∫ t, poissonCollarDensity ε hε k t*A (ρ+t))-A ρ| ≤ η/2 := by
    rw [← hc, ← integral_sub hi (hq.mul_const (A ρ))]
    apply abs_integral_le_integral_abs.trans
    have hb : ∀ t, |poissonCollarDensity ε hε k t*A (ρ+t)-poissonCollarDensity ε hε k t*A ρ| ≤
        (η/2)*poissonCollarDensity ε hε k t := by
      intro t
      by_cases ht : poissonCollarDensity ε hε k t = 0
      · simp only [ht, zero_mul, sub_self, abs_zero, mul_zero, le_refl]
      · have hs := tsupport_poissonCollarDensity_subset ε hε k
          (subset_tsupport _ (by simpa only [Function.mem_support] using ht))
        have hdist : dist (ρ+t) ρ < d := by
          rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hs.1]
          exact hs.2.trans (hN k hk)
        have ha : |A (ρ+t)-A ρ| ≤ η/2 := by
          simpa only [Real.dist_eq] using (hAd hdist).le
        rw [← mul_sub, abs_mul, abs_of_nonneg (poissonCollarDensity_nonneg ε hε k t)]
        exact (mul_le_mul_of_nonneg_left ha (poissonCollarDensity_nonneg ε hε k t)).trans_eq (mul_comm _ _)
    calc
      _ ≤ ∫ t, (η/2)*poissonCollarDensity ε hε k t :=
        integral_mono_ae (hi.sub (hq.mul_const (A ρ))).norm (hq.const_mul (η/2))
          (ae_of_all _ (fun t => by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hb t))
      _ = η/2 := by rw [integral_const_mul, integral_poissonCollarDensity, mul_one]
  rw [Real.dist_eq]
  exact herror.trans_lt (half_lt_self hη)

/-- Actual smooth collars converge weakly to the normalized Poisson boundary functional. -/
theorem tendsto_integral_poissonCollarTest_mul_bounded (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (h : ℂ → ℝ) (hh : Continuous h)
    (M : ℝ) (hb : ∀ w, ‖h w‖ ≤ M) :
    Tendsto (fun k : ℕ => ∫ w, poissonCollarTest c z ρ (ε/((k : ℝ)+1)) hρ hz
      (poissonCollarDensity ε hε k) (poissonCollarDensity_contDiff ε hε k)
      (tsupport_poissonCollarDensity_subset ε hε k) w*h w)
      atTop (𝓝 (∫ v, unitPoissonWeight c ρ z v*h (c+ρ • v) ∂circleMeasure 0 0)) := by
  have he (k : ℕ) := integral_poissonCollarTest_mul_eq_mixture c z ρ (ε/((k : ℝ)+1)) hρ hz
    (poissonCollarDensity ε hε k) (poissonCollarDensity_contDiff ε hε k)
    (tsupport_poissonCollarDensity_subset ε hε k) h hh.measurable
    (((poissonCollarTest c z ρ (ε/((k : ℝ)+1)) hρ hz
      (poissonCollarDensity ε hε k) (poissonCollarDensity_contDiff ε hε k)
      (tsupport_poissonCollarDensity_subset ε hε k)).continuous.mul hh).integrable_of_hasCompactSupport
        (poissonCollarTest c z ρ (ε/((k : ℝ)+1)) hρ hz
          (poissonCollarDensity ε hε k) (poissonCollarDensity_contDiff ε hε k)
          (tsupport_poissonCollarDensity_subset ε hε k)).hasCompactSupport.mul_right)
  simp_rw [he]
  exact tendsto_integral_poissonCollarDensity_mul ε ρ hε _
    (continuous_poissonCircleMean_radius c z ρ hρ hz h hh M hb)

/-- The literal radial bump defines a probability measure on the collar displacement. -/
noncomputable def poissonCollarRadiusMeasure (ε : ℝ) (hε : 0 < ε) (k : ℕ) : Measure ℝ :=
  volume.withDensity (fun t => ENNReal.ofReal (poissonCollarDensity ε hε k t))

/-- The normalized radial collar measure is a probability measure. -/
theorem poissonCollarRadiusMeasure_isProbability (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    IsProbabilityMeasure (poissonCollarRadiusMeasure ε hε k) := by
  constructor
  rw [poissonCollarRadiusMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_poissonCollarDensity ε hε k)
      (ae_of_all _ (poissonCollarDensity_nonneg ε hε k)), integral_poissonCollarDensity,
    ENNReal.ofReal_one]

/-- The radial probability is concentrated in its literal shrinking support interval. -/
theorem ae_poissonCollarRadiusMeasure_mem (ε : ℝ) (hε : 0 < ε) (k : ℕ) :
    ∀ᵐ t ∂poissonCollarRadiusMeasure ε hε k, t ∈ Ioo 0 (ε/((k : ℝ)+1)) := by
  rw [poissonCollarRadiusMeasure, ae_withDensity_iff
    ((poissonCollarDensity_contDiff ε hε k).continuous.measurable.ennreal_ofReal)]
  apply ae_of_all
  intro t ht
  apply tsupport_poissonCollarDensity_subset ε hε k
  apply subset_tsupport
  intro hz
  apply ht
  rw [hz, ENNReal.ofReal_zero]

/-- Bochner integration against the radial law is the actual weighted radial integral. -/
theorem integral_poissonCollarRadiusMeasure (ε : ℝ) (hε : 0 < ε) (k : ℕ) (A : ℝ → ℝ) :
    (∫ t, A t ∂poissonCollarRadiusMeasure ε hε k) =
      ∫ t, poissonCollarDensity ε hε k t*A t := by
  rw [poissonCollarRadiusMeasure, integral_withDensity_eq_integral_toReal_smul
    ((poissonCollarDensity_contDiff ε hε k).continuous.measurable.ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (poissonCollarDensity_nonneg ε hε k _), smul_eq_mul]

/-- Two independent radial collar variables satisfy both literal support bounds. -/
theorem ae_poissonCollarRadiusMeasure_pair_mem (ε : ℝ) (hε : 0 < ε) (k l : ℕ) :
    ∀ᵐ t : ℝ × ℝ ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l),
      t ∈ Ioo 0 (ε/((k : ℝ)+1)) ×ˢ Ioo 0 (ε/((l : ℝ)+1)) := by
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ioo.prod measurableSet_Ioo)).mpr
  filter_upwards [ae_poissonCollarRadiusMeasure_mem ε hε k] with t ht
  filter_upwards [ae_poissonCollarRadiusMeasure_mem ε hε l] with s hs
  exact ⟨ht, hs⟩

/-- Every continuous zero-valued observable has uniformly small double-collar integrals.
The two indices may approach infinity independently. -/
theorem eventually_abs_integral_poissonCollarRadiusMeasure_pair_le (ε : ℝ) (hε : 0 < ε)
    (A : ℝ × ℝ → ℝ) (hA : ContinuousWithinAt A (Icc 0 ε ×ˢ Icc 0 ε) (0,0))
    (hAzero : A (0,0) = 0) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
      |∫ t : ℝ × ℝ, A t
        ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)| ≤ η := by
  obtain ⟨d, hd, hAd⟩ := Metric.continuousWithinAt_iff.mp hA η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_poissonCollarWidth ε).eventually (gt_mem_nhds hd))
  refine ⟨N, fun k l hk hl => ?_⟩
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  have hsmall : ∀ᵐ t : ℝ × ℝ ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l),
      ‖A t‖ ≤ η := by
    filter_upwards [ae_poissonCollarRadiusMeasure_pair_mem ε hε k l] with t ht
    have hbound (m : ℕ) : ε/((m : ℝ)+1) ≤ ε := by
      apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+1)).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have htbox : t ∈ Icc 0 ε ×ˢ Icc 0 ε :=
      ⟨⟨ht.1.1.le, ht.1.2.le.trans (hbound k)⟩, ⟨ht.2.1.le, ht.2.2.le.trans (hbound l)⟩⟩
    have hdist : dist t (0,0) < d := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero,
        abs_of_pos ht.1.1, abs_of_pos ht.2.1, max_lt_iff]
      exact ⟨ht.1.2.trans (hN k hk), ht.2.2.trans (hN l hl)⟩
    simpa only [hAzero, dist_zero_right] using (hAd htbox hdist).le
  have he := norm_integral_le_of_norm_le_const hsmall
  simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using he

/-- The radial product law is exactly the density tensor on the plane of displacements. -/
theorem poissonCollarRadiusMeasure_pair_eq_withDensity (ε : ℝ) (hε : 0 < ε) (k l : ℕ) :
    (poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l) =
      (volume : Measure (ℝ × ℝ)).withDensity (fun t =>
        ENNReal.ofReal (poissonCollarDensity ε hε k t.1*poissonCollarDensity ε hε l t.2)) := by
  rw [poissonCollarRadiusMeasure, poissonCollarRadiusMeasure, prod_withDensity
    ((poissonCollarDensity_contDiff ε hε k).continuous.measurable.ennreal_ofReal)
    ((poissonCollarDensity_contDiff ε hε l).continuous.measurable.ennreal_ofReal),
    Measure.volume_eq_prod]
  congr 1
  funext t
  exact (ENNReal.ofReal_mul (poissonCollarDensity_nonneg ε hε k t.1)).symm

/-- Radial product integration is the literal density tensor integral. -/
theorem integral_poissonCollarRadiusMeasure_pair (ε : ℝ) (hε : 0 < ε) (k l : ℕ)
    (A : ℝ × ℝ → ℝ) :
    (∫ t : ℝ × ℝ, A t
      ∂(poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)) =
      ∫ t : ℝ × ℝ, poissonCollarDensity ε hε k t.1*poissonCollarDensity ε hε l t.2*A t := by
  rw [poissonCollarRadiusMeasure_pair_eq_withDensity, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (mul_nonneg (poissonCollarDensity_nonneg ε hε k _)
      (poissonCollarDensity_nonneg ε hε l _)), smul_eq_mul]
  · exact (((poissonCollarDensity_contDiff ε hε k).continuous.measurable.comp measurable_fst).mul
      ((poissonCollarDensity_contDiff ε hε l).continuous.measurable.comp measurable_snd)).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

/-- Translating collar displacements transfers the angular error continuity to zero. -/
theorem continuousWithinAt_poisson_radial_circleLog_error (ρ ε : ℝ) (hρ : 0 < ρ) :
    ContinuousWithinAt (fun t : ℝ × ℝ => ∫ p : ℂ × ℂ,
      |Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) (Icc 0 ε ×ˢ Icc 0 ε) (0,0) := by
  have hshift : Tendsto (fun t : ℝ × ℝ => (ρ+t.1,ρ+t.2))
      (𝓝[Icc 0 ε ×ˢ Icc 0 ε] (0,0)) (𝓝[Icc ρ (ρ+ε) ×ˢ Icc ρ (ρ+ε)] (ρ,ρ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero] using
        (by fun_prop : Continuous (fun t : ℝ × ℝ => (ρ+t.1,ρ+t.2))).continuousAt.tendsto.mono_left
          (nhdsWithin_le_nhds (s := Icc 0 ε ×ˢ Icc 0 ε) (a := (0,0)))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨⟨le_add_of_nonneg_right ht.1.1, add_le_add le_rfl ht.1.2⟩,
        ⟨le_add_of_nonneg_right ht.2.1, add_le_add le_rfl ht.2.2⟩⟩
  have he := (tendsto_radial_circleLog_error ρ (ρ+ε) hρ).comp hshift
  simpa only [ContinuousWithinAt, Function.comp_def, add_zero, sub_self, abs_zero, integral_zero] using he

/-- Integrating the absolute angular error against two independently shrinking bump laws
still tends to zero, uniformly once both indices are sufficiently large. -/
theorem eventually_poissonCollar_angularLog_error_le (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ k l : ℕ, N ≤ k → N ≤ l →
      |∫ t : ℝ × ℝ, poissonCollarDensity ε hε k t.1*poissonCollarDensity ε hε l t.2*
        (∫ p : ℂ × ℂ,
          |Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
          ∂(circleMeasure 0 0).prod (circleMeasure 0 0))| ≤ η := by
  obtain ⟨N,hN⟩ := eventually_abs_integral_poissonCollarRadiusMeasure_pair_le ε hε _
    (continuousWithinAt_poisson_radial_circleLog_error ρ ε hρ)
    (by simp only [add_zero, sub_self, abs_zero, integral_zero]) η hη
  refine ⟨N, fun k l hk hl => ?_⟩
  simpa only [integral_poissonCollarRadiusMeasure_pair] using hN k l hk hl


/-- The common angular log majorant gives a finite deterministic error bound on every collar square. -/
theorem integral_radial_circleLog_error_le (ρ B r s : ℝ) (hρ : 0 < ρ)
    (hr : ρ ≤ r) (hs : ρ ≤ s) (hrB : r ≤ B) (hsB : s ≤ B) :
    (∫ p : ℂ × ℂ, |Real.log ‖r • p.1-s • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) ≤
      2*(|Real.log (2*B)|+|Real.log ρ|+
        ∫ p : ℂ × ℂ, |Real.log ‖p.1-p.2‖| ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) := by
  let _ := circleMeasure_isProbability (0 : ℂ) 0
  have he := integrable_radial_circleLog_error ρ B r s hρ hr hs hrB hsB
  have hb : Integrable (fun p : ℂ × ℂ =>
      2*(|Real.log (2*B)|+|Real.log ρ|+|Real.log ‖p.1-p.2‖|))
      ((circleMeasure 0 0).prod (circleMeasure 0 0)) :=
    ((integrable_const _).add integrable_unitCircle_log_distance.norm).const_mul 2
  have hmono : (∫ p : ℂ × ℂ, |Real.log ‖r • p.1-s • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) ≤
      (∫ p : ℂ × ℂ, 2*(|Real.log (2*B)|+|Real.log ρ|+|Real.log ‖p.1-p.2‖|)
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0)) := by
    apply integral_mono_ae he hb
    filter_upwards [ae_unitCircle_pair_spec] with p hp
    have h1 := abs_log_norm_smul_sub_le p.1 p.2 hp.1 hp.2.1 hp.2.2 ρ B r s hρ hr hs hrB hsB
    have h2 := abs_log_norm_smul_sub_le p.1 p.2 hp.1 hp.2.1 hp.2.2 ρ B ρ ρ hρ le_rfl le_rfl
      (hr.trans hrB) (hs.trans hsB)
    exact (abs_sub _ _).trans (by linarith)
  convert hmono using 1
  have habs : Integrable (fun p : ℂ × ℂ => |Real.log ‖p.1-p.2‖|)
      ((circleMeasure 0 0).prod (circleMeasure 0 0)) := by
    simpa only [Real.norm_eq_abs] using integrable_unitCircle_log_distance.norm
  rw [integral_const_mul, integral_add (integrable_const (|Real.log (2*B)|+|Real.log ρ|)) habs]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

/-- Actual radial collar mixtures of the angular error are integrable, including their diagonal. -/
theorem integrable_poissonCollar_angularLog_error (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (k l : ℕ) :
    Integrable (fun t : ℝ × ℝ => ∫ p : ℂ × ℂ,
      |Real.log ‖(ρ+t.1) • p.1-(ρ+t.2) • p.2‖-Real.log ‖ρ • p.1-ρ • p.2‖|
      ∂(circleMeasure 0 0).prod (circleMeasure 0 0))
      ((poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)) := by
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  have hm : StronglyMeasurable (fun a : (ℝ × ℝ) × (ℂ × ℂ) =>
      |Real.log ‖(ρ+a.1.1) • a.2.1-(ρ+a.1.2) • a.2.2‖-Real.log ‖ρ • a.2.1-ρ • a.2.2‖|) :=
    (by fun_prop : Measurable _).stronglyMeasurable
  apply (integrable_const (2*(|Real.log (2*(ρ+ε))|+|Real.log ρ|+
    ∫ p : ℂ × ℂ, |Real.log ‖p.1-p.2‖| ∂(circleMeasure 0 0).prod (circleMeasure 0 0)))).mono'
      hm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [ae_poissonCollarRadiusMeasure_pair_mem ε hε k l] with t ht
  have hbound (m : ℕ) : ε/((m : ℝ)+1) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < (m : ℝ)+1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => abs_nonneg _))]
  exact integral_radial_circleLog_error_le ρ (ρ+ε) (ρ+t.1) (ρ+t.2) hρ
    (le_add_of_nonneg_right ht.1.1.le) (le_add_of_nonneg_right ht.2.1.le)
    (add_le_add le_rfl (ht.1.2.le.trans (hbound k)))
    (add_le_add le_rfl (ht.2.2.le.trans (hbound l)))



/-- The canonical literal collar test with its normalized smooth bump. -/
noncomputable def canonicalPoissonCollarTest (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) : TestFn :=
  poissonCollarTest c z ρ (ε/((k : ℝ)+1)) hρ hz
    (poissonCollarDensity ε hε k) (poissonCollarDensity_contDiff ε hε k)
    (tsupport_poissonCollarDensity_subset ε hε k)

/-- The canonical literal collar density is nonnegative. -/
theorem canonicalPoissonCollarTest_nonneg (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) (w : ℂ) :
    0 ≤ canonicalPoissonCollarTest c z ρ ε hρ hε hz k w :=
  poissonCollarValue_nonneg c z ρ hρ hz (poissonCollarDensity ε hε k)
    (poissonCollarDensity_nonneg ε hε k) w

/-- Canonical collar tests have literal total mass one. -/
theorem integral_canonicalPoissonCollarTest (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) :
    (∫ w, canonicalPoissonCollarTest c z ρ ε hρ hε hz k w) = 1 :=
  integral_poissonCollarTest c z ρ _ hρ hz _ _ _ (integral_poissonCollarDensity ε hε k)

/-- The literal collar density as a planar probability law. -/
noncomputable def canonicalPoissonCollarMeasure (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) : Measure ℂ :=
  volume.withDensity (fun w => ENNReal.ofReal (canonicalPoissonCollarTest c z ρ ε hρ hε hz k w))

/-- The literal collar law is a probability measure. -/
theorem canonicalPoissonCollarMeasure_isProbability (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) :
    IsProbabilityMeasure (canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k) := by
  constructor
  rw [canonicalPoissonCollarMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((canonicalPoissonCollarTest c z ρ ε hρ hε hz k).continuous.integrable_of_hasCompactSupport
        (canonicalPoissonCollarTest c z ρ ε hρ hε hz k).hasCompactSupport)]
  · rw [integral_canonicalPoissonCollarTest, ENNReal.ofReal_one]
  · exact ae_of_all _ (canonicalPoissonCollarTest_nonneg c z ρ ε hρ hε hz k)

/-- Integration against the collar law is actual integration of its test density. -/
theorem integral_canonicalPoissonCollarMeasure (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) (f : ℂ → ℝ) :
    (∫ w, f w ∂canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k) =
      ∫ w, canonicalPoissonCollarTest c z ρ ε hρ hε hz k w*f w := by
  rw [canonicalPoissonCollarMeasure, integral_withDensity_eq_integral_toReal_smul
    (canonicalPoissonCollarTest c z ρ ε hρ hε hz k).continuous.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (canonicalPoissonCollarTest_nonneg c z ρ ε hρ hε hz k _),
    smul_eq_mul]

/-- The unit-angle Poisson probability measure. -/
noncomputable def unitPoissonMeasure (c : ℂ) (ρ : ℝ) (z : ℂ) : Measure ℂ :=
  (circleMeasure 0 0).withDensity (fun u => ENNReal.ofReal (unitPoissonWeight c ρ z u))

/-- The angular Poisson law is a probability at every interior parameter. -/
theorem unitPoissonMeasure_isProbability (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) : IsProbabilityMeasure (unitPoissonMeasure c ρ z) := by
  constructor
  rw [unitPoissonMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_unitPoissonWeight c z ρ hρ hz)
      (ae_of_all _ (unitPoissonWeight_nonneg c z · ρ hρ hz)),
    integral_unitPoissonWeight c z ρ hρ hz, ENNReal.ofReal_one]

/-- Unit-angle Poisson integration is the actual angular weighted integral. -/
theorem integral_unitPoissonMeasure (c z : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (f : ℂ → ℝ) :
    (∫ u, f u ∂unitPoissonMeasure c ρ z) =
      ∫ u, unitPoissonWeight c ρ z u*f u ∂circleMeasure 0 0 := by
  rw [unitPoissonMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_unitPoissonWeight c z ρ).ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (unitPoissonWeight_nonneg c z _ ρ hρ hz), smul_eq_mul]

/-- The angular Poisson probability stays on the unit circle. -/
theorem ae_norm_unitPoissonMeasure (c z : ℂ) (ρ : ℝ) :
    ∀ᵐ u ∂unitPoissonMeasure c ρ z, ‖u‖ = 1 := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  filter_upwards [ae_norm_sub_center_circleMeasure 0 0] with u hu
  simpa only [sub_zero, neg_zero, Real.exp_zero] using hu

/-- The literal Cartesian collar law equals its mapped radial and angular probability mixture. -/
theorem canonicalPoissonCollarMeasure_eq_map (c z : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (k : ℕ) :
    canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k =
      ((poissonCollarRadiusMeasure ε hε k).prod (unitPoissonMeasure c ρ z)).map
        (fun a : ℝ × ℂ => c+(ρ+a.1) • a.2) := by
  let _ := canonicalPoissonCollarMeasure_isProbability c z ρ ε hρ hε hz k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := unitPoissonMeasure_isProbability c z ρ hρ hz
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hmap : Measurable (fun a : ℝ × ℂ => c+(ρ+a.1) • a.2) := by fun_prop
  have hi : Integrable (fun a : ℝ × ℂ => f (c+(ρ+a.1) • a.2))
      ((poissonCollarRadiusMeasure ε hε k).prod (unitPoissonMeasure c ρ z)) :=
    (integrable_const ‖f‖).mono' (f.continuous.measurable.comp hmap).aestronglyMeasurable
      (ae_of_all _ (fun a => f.norm_coe_le_norm _))
  rw [integral_canonicalPoissonCollarMeasure, integral_map_of_stronglyMeasurable hmap f.continuous.measurable.stronglyMeasurable,
    integral_prod _ hi, integral_poissonCollarRadiusMeasure]
  have hpolar := integral_poissonCollarTest_mul_eq_mixture c z ρ (ε/((k : ℝ)+1)) hρ hz
    (poissonCollarDensity ε hε k) (poissonCollarDensity_contDiff ε hε k)
    (tsupport_poissonCollarDensity_subset ε hε k) f f.continuous.measurable
    (((canonicalPoissonCollarTest c z ρ ε hρ hε hz k).continuous.mul f.continuous).integrable_of_hasCompactSupport
      (canonicalPoissonCollarTest c z ρ ε hρ hε hz k).hasCompactSupport.mul_right)
  change (∫ w, poissonCollarTest c z ρ _ hρ hz _ _ _ w*f w) = _
  rw [hpolar]
  apply integral_congr_ae
  filter_upwards with t
  rw [integral_unitPoissonMeasure c z ρ hρ hz]

/-- Regroup four product variables into the two radial and the two angular coordinates. -/
def poissonQuadSwap (α β γ δ : Type*) [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) where
  toEquiv := Equiv.prodProdProdComm α β γ δ
  measurable_toFun := by
    change Measurable (fun a : (α × β) × (γ × δ) => ((a.1.1,a.2.1),(a.1.2,a.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun a : (α × γ) × (β × δ) => ((a.1.1,a.2.1),(a.1.2,a.2.2)))
    fun_prop

/-- Regrouping product coordinates preserves the corresponding four-fold product law. -/
theorem measurePreserving_poissonQuadSwap {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] (μa : Measure α) (μb : Measure β)
    (μc : Measure γ) (μd : Measure δ) [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (poissonQuadSwap α β γ δ)
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μb μc μd))
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μa μc (μb.prod μd))
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

/-- The unit-angle product law equals its literal pair of Poisson weights. -/
theorem unitPoissonMeasure_pair_eq_withDensity (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) :
    (unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w) =
      ((circleMeasure 0 0).prod (circleMeasure 0 0)).withDensity
        (fun p => ENNReal.ofReal (unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2)) := by
  rw [unitPoissonMeasure, unitPoissonMeasure, prod_withDensity
    (measurable_unitPoissonWeight c z ρ).ennreal_ofReal
    (measurable_unitPoissonWeight c w ρ).ennreal_ofReal]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (unitPoissonWeight_nonneg c z p.1 ρ hρ hz)).symm

/-- Product Poisson integration is actual integration of both boundary weights. -/
theorem integral_unitPoissonMeasure_pair (c z w : ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (F : ℂ × ℂ → ℝ) :
    (∫ p : ℂ × ℂ, F p ∂(unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w)) =
      ∫ p : ℂ × ℂ, unitPoissonWeight c ρ z p.1*unitPoissonWeight c ρ w p.2*F p
        ∂(circleMeasure 0 0).prod (circleMeasure 0 0) := by
  rw [unitPoissonMeasure_pair_eq_withDensity c z w ρ hρ hz, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (mul_nonneg (unitPoissonWeight_nonneg c z _ ρ hρ hz)
      (unitPoissonWeight_nonneg c w _ ρ hρ hw)), smul_eq_mul]
  · exact (((measurable_unitPoissonWeight c z ρ).comp measurable_fst).mul
      ((measurable_unitPoissonWeight c w ρ).comp measurable_snd)).ennreal_ofReal
  · exact ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)

/-- The literal two-collar law is the mapped product of both radial laws and both angular laws. -/
theorem canonicalPoissonCollarMeasure_pair_eq_map (c z w : ℂ) (ρ ε : ℝ) (hρ : 0 < ρ)
    (hε : 0 < ε) (hz : z ∈ ball c ρ) (hw : w ∈ ball c ρ) (k l : ℕ) :
    (canonicalPoissonCollarMeasure c z ρ ε hρ hε hz k).prod
      (canonicalPoissonCollarMeasure c w ρ ε hρ hε hw l) =
      (((poissonCollarRadiusMeasure ε hε k).prod (poissonCollarRadiusMeasure ε hε l)).prod
        ((unitPoissonMeasure c ρ z).prod (unitPoissonMeasure c ρ w))).map
          (fun a : (ℝ × ℝ) × (ℂ × ℂ) => (c+(ρ+a.1.1) • a.2.1,c+(ρ+a.1.2) • a.2.2)) := by
  let _ := poissonCollarRadiusMeasure_isProbability ε hε k
  let _ := poissonCollarRadiusMeasure_isProbability ε hε l
  let _ := unitPoissonMeasure_isProbability c z ρ hρ hz
  let _ := unitPoissonMeasure_isProbability c w ρ hρ hw
  have h1 : Measurable (fun a : ℝ × ℂ => c+(ρ+a.1) • a.2) := by fun_prop
  rw [canonicalPoissonCollarMeasure_eq_map c z ρ ε hρ hε hz k,
    canonicalPoissonCollarMeasure_eq_map c w ρ ε hρ hε hw l, Measure.map_prod_map _ _ h1 h1]
  have hswap := measurePreserving_poissonQuadSwap (poissonCollarRadiusMeasure ε hε k)
    (unitPoissonMeasure c ρ z) (poissonCollarRadiusMeasure ε hε l) (unitPoissonMeasure c ρ w)
  rw [← hswap.map_eq, Measure.map_map (by fun_prop) (poissonQuadSwap ℝ ℂ ℝ ℂ).measurable]
  rfl

end DOZZ.Proofs
