/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.ExteriorScale
public import DOZZ.GMC.SharpMoments.WeightedDyadicSum

/-! # Cutoff moments of exterior power weights

Outside a disk of radius `R₀ ≥ 2`, split the plane into the dyadic annuli
`2ⁿ R₀ ≤ |x| < 2ⁿ⁺¹ R₀`. By exact exterior scaling the `t`th cutoff moment of the `n`th annulus
is `2^{-n ξ(t)}` times a cutoff moment of the base annulus, so a power weight `|x|^β` with
`ξ(t) > β t` gives a geometric series, which is summed by subadditivity for `t ≤ 1` and by
Minkowski's inequality for `t > 1`. The bound is explicit and uniform in the cutoff. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A quantitative moment bound for a series with geometrically decaying moments. -/
theorem lintegral_tsum_rpow_le_of_geometric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ n, AEMeasurable (f n) P) {t : ℝ} (ht : 0 < t)
    {K q : ℝ≥0∞} (hbound : ∀ n, ∫⁻ ω, f n ω ^ t ∂P ≤ K * q ^ n) :
    ∫⁻ ω, (∑' n, f n ω) ^ t ∂P ≤ K * ((1 - q ^ (1 / max 1 t)) ^ (max 1 t))⁻¹ := by
  rcases le_or_gt t 1 with ht1 | ht1
  · have hm : max 1 t = 1 := max_eq_left ht1
    rw [hm, div_one, ENNReal.rpow_one, ENNReal.rpow_one]
    calc ∫⁻ ω, (∑' n, f n ω) ^ t ∂P ≤ ∫⁻ ω, ∑' n, f n ω ^ t ∂P :=
          lintegral_mono fun ω => ennreal_rpow_tsum_le_tsum_rpow _ ht ht1
      _ = ∑' n, ∫⁻ ω, f n ω ^ t ∂P := lintegral_tsum fun n => (hf n).pow_const t
      _ ≤ ∑' n : ℕ, K * q ^ n := ENNReal.tsum_le_tsum hbound
      _ = K * (1 - q)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  · have hm : max 1 t = t := max_eq_right ht1.le
    rw [hm]
    have hinv : 0 < 1 / t := one_div_pos.2 ht
    have hroot (n : ℕ) :
        (∫⁻ ω, f n ω ^ t ∂P) ^ (1 / t) ≤ K ^ (1 / t) * (q ^ (1 / t)) ^ n :=
      calc (∫⁻ ω, f n ω ^ t ∂P) ^ (1 / t) ≤ (K * q ^ n) ^ (1 / t) :=
            ENNReal.rpow_le_rpow (hbound n) hinv.le
        _ = K ^ (1 / t) * (q ^ n) ^ (1 / t) := ENNReal.mul_rpow_of_nonneg _ _ hinv.le
        _ = K ^ (1 / t) * (q ^ (1 / t)) ^ n := by rw [weightedDyadicSum_pow_rpow_comm]
    calc ∫⁻ ω, (∑' n, f n ω) ^ t ∂P ≤ (∑' n, (∫⁻ ω, f n ω ^ t ∂P) ^ (1 / t)) ^ t :=
          ennreal_lintegral_rpow_tsum_le_of_roots_summable f t ht1.le hf
      _ ≤ (∑' n : ℕ, K ^ (1 / t) * (q ^ (1 / t)) ^ n) ^ t :=
          ENNReal.rpow_le_rpow (ENNReal.tsum_le_tsum hroot) ht.le
      _ = (K ^ (1 / t) * (1 - q ^ (1 / t))⁻¹) ^ t := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = K * ((1 - q ^ (1 / t)) ^ t)⁻¹ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ht.le, ← ENNReal.rpow_mul,
            one_div_mul_cancel ht.ne', ENNReal.rpow_one, ENNReal.inv_rpow]

/-- The dyadic exterior annuli `2ⁿ R₀ ≤ |x| < 2ⁿ⁺¹ R₀`. -/
def exteriorAnnulus (R0 : ℝ) (n : ℕ) : Set ℂ :=
  {x : ℂ | 2 ^ n * R0 ≤ ‖x‖ ∧ ‖x‖ < 2 ^ (n + 1) * R0}

theorem measurableSet_exteriorAnnulus (R0 : ℝ) (n : ℕ) :
    MeasurableSet (exteriorAnnulus R0 n) :=
  (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)

theorem exteriorAnnulus_eq_preimage (R0 : ℝ) (n : ℕ) :
    exteriorAnnulus R0 n =
      {y : ℂ | ((((2 : ℝ) ^ n : ℝ)) : ℂ)⁻¹ * y ∈ exteriorAnnulus R0 0} := by
  ext y
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hnorm : ‖((((2 : ℝ) ^ n : ℝ)) : ℂ)⁻¹ * y‖ = ‖y‖ / 2 ^ n := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2, inv_mul_eq_div]
  change (2 ^ n * R0 ≤ ‖y‖ ∧ ‖y‖ < 2 ^ (n + 1) * R0) ↔
    (2 ^ 0 * R0 ≤ ‖((((2 : ℝ) ^ n : ℝ)) : ℂ)⁻¹ * y‖ ∧
      ‖((((2 : ℝ) ^ n : ℝ)) : ℂ)⁻¹ * y‖ < 2 ^ (0 + 1) * R0)
  rw [hnorm, pow_zero, one_mul, zero_add, pow_one, le_div_iff₀ h2, div_lt_iff₀ h2]
  have hpow : (2 : ℝ) ^ (n + 1) * R0 = 2 * R0 * 2 ^ n := by ring
  rw [hpow, mul_comm (2 ^ n) R0]

theorem exteriorAnnulus_disjoint (R0 : ℝ) (hR0 : 0 < R0) :
    Pairwise (Function.onFun Disjoint (exteriorAnnulus R0)) := by
  intro m n hmn
  rw [Function.onFun, Set.disjoint_left]
  intro x hxm hxn
  rcases lt_or_gt_of_ne hmn with h | h
  · have hle : (2 : ℝ) ^ (m + 1) ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) h
    have := hxm.2
    have := hxn.1
    nlinarith
  · have hle : (2 : ℝ) ^ (n + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) h
    have := hxn.2
    have := hxm.1
    nlinarith

theorem iUnion_exteriorAnnulus (R0 : ℝ) (hR0 : 0 < R0) :
    (⋃ n, exteriorAnnulus R0 n) = {x : ℂ | R0 ≤ ‖x‖} := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn1, _⟩
    have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    exact le_trans (le_mul_of_one_le_left hR0.le this) hn1
  · intro hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ((one_le_div hR0).mpr hx)
      (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_, ?_⟩
    · rwa [le_div_iff₀ hR0] at hn1
    · rwa [div_lt_iff₀ hR0] at hn2

/-- The annulus coefficient: the weight bound and the exterior scaling factor combine into a
geometric factor. -/
theorem exteriorMoment_coeff_eq {R0 : ℝ} (hR0 : 0 < R0) (β t γ : ℝ) (n : ℕ) :
    ((2 ^ (n + 1) * R0) ^ β) ^ t * ((2 ^ n : ℝ) ^ (-2 * t) *
        Real.exp (γ ^ 2 * Real.log (2 ^ n) / 2 * (t ^ 2 - t))) =
      (2 * R0) ^ (β * t) *
        ((1 / 2 : ℝ) ^ (2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2 - β * t)) ^ n := by
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2R : (0 : ℝ) < 2 * R0 := by positivity
  have hsplit : (2 : ℝ) ^ (n + 1) * R0 = 2 * R0 * 2 ^ n := by ring
  have hexp : Real.exp (γ ^ 2 * Real.log (2 ^ n) / 2 * (t ^ 2 - t)) =
      (2 ^ n : ℝ) ^ (γ ^ 2 * (t ^ 2 - t) / 2) := by
    rw [Real.rpow_def_of_pos h2n]
    congr 1
    ring
  have hhalf : ((1 / 2 : ℝ) ^ (2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2 - β * t)) ^ n =
      (2 ^ n : ℝ) ^ (-(2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2 - β * t)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div,
      Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), ← Real.rpow_natCast (2 : ℝ) n,
      ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [hsplit, ← Real.rpow_mul (by positivity), Real.mul_rpow h2R.le h2n.le, hexp, hhalf]
  rw [mul_assoc, ← Real.rpow_add h2n, ← Real.rpow_add h2n]
  congr 2
  ring

/-- Exterior cutoff moments of a power weight, uniformly in the cutoff. -/
theorem cutoff_exterior_power_moment_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) {R0 : ℝ} (hR0 : 2 ≤ R0)
    {β : ℝ} (hβ : 0 ≤ β) {t : ℝ} (ht : 0 < t) {K0 : ℝ≥0∞}
    (hK0 : ∀ r' : ℝ, 0 ≤ r' →
      ∫⁻ ω, regularizedGMC P Xc γ r' ω (exteriorAnnulus R0 0) ^ t ∂P ≤ K0)
    {r : ℝ} (hr : 0 ≤ r) :
    ∫⁻ ω, (∫⁻ x in {x : ℂ | R0 ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β)
        ∂regularizedGMC P Xc γ r ω) ^ t ∂P ≤
      ENNReal.ofReal ((2 * R0) ^ (β * t)) * K0 *
        ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ (2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2 - β * t)) ^
          (1 / max 1 t)) ^ (max 1 t))⁻¹ := by
  let _ : IsProbabilityMeasure P := hX.1
  have hR0pos : 0 < R0 := by linarith
  set ζ : ℝ := 2 * t + γ ^ 2 * t / 2 - γ ^ 2 * t ^ 2 / 2 - β * t with hζ
  set A : ℕ → Set ℂ := exteriorAnnulus R0 with hA
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ENNReal.ofReal ((2 ^ (n + 1) * R0) ^ β) * regularizedGMC P Xc γ r ω (A n) with hf
  have hAm : ∀ n, MeasurableSet (A n) := measurableSet_exteriorAnnulus R0
  have hfm : ∀ n, AEMeasurable (f n) P := fun n =>
    aemeasurable_const.mul (((Measure.measurable_coe (hAm n)).comp
      (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable)
  -- the pointwise dyadic bound
  have hpt : ∀ ω, (∫⁻ x in {x : ℂ | R0 ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β)
      ∂regularizedGMC P Xc γ r ω) ≤ ∑' n, f n ω := by
    intro ω
    rw [← iUnion_exteriorAnnulus R0 hR0pos, lintegral_iUnion hAm (exteriorAnnulus_disjoint R0
      hR0pos)]
    refine ENNReal.tsum_le_tsum fun n => ?_
    calc ∫⁻ x in A n, ENNReal.ofReal (‖x‖ ^ β) ∂regularizedGMC P Xc γ r ω
        ≤ ∫⁻ _x in A n, ENNReal.ofReal ((2 ^ (n + 1) * R0) ^ β) ∂regularizedGMC P Xc γ r ω := by
          refine setLIntegral_mono' (hAm n) fun x hx => ENNReal.ofReal_le_ofReal ?_
          exact Real.rpow_le_rpow (norm_nonneg _) hx.2.le hβ
      _ = f n ω := setLIntegral_const _ _
  -- moments of the annulus terms
  have hmom : ∀ n, ∫⁻ ω, f n ω ^ t ∂P ≤
      (ENNReal.ofReal ((2 * R0) ^ (β * t)) * K0) * ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ) ^ n := by
    intro n
    have hc : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    have hscale := cutoff_exterior_scale_moment_eq P X hX Xc hXc γ hr hc (A 0) (hAm 0)
      (fun x hx => le_trans hR0 (by simpa [hA, exteriorAnnulus] using hx.1)) (fun _ => 1)
      measurable_const ⟨1, fun _ => le_rfl⟩ t
    have hone : ∀ (μ : Measure ℂ) (S : Set ℂ),
        (∫⁻ y in S, ((fun _ : ℂ => (1 : ℝ≥0)) y : ℝ≥0∞) ∂μ) = μ S := fun μ S => by simp
    simp only [hone] at hscale
    rw [← exteriorAnnulus_eq_preimage R0 n] at hscale
    calc ∫⁻ ω, f n ω ^ t ∂P
        = ENNReal.ofReal ((2 ^ (n + 1) * R0) ^ β) ^ t *
            ∫⁻ ω, regularizedGMC P Xc γ r ω (A n) ^ t ∂P := by
          have hMm : AEMeasurable (fun ω => regularizedGMC P Xc γ r ω (A n) ^ t) P :=
            ((Measure.measurable_coe (hAm n)).comp
              (regularizedGMC_measurable P X hX Xc hXc γ r)).aemeasurable.pow_const t
          rw [lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ ht.le,
            lintegral_const_mul'' _ hMm]
      _ = ENNReal.ofReal ((2 ^ (n + 1) * R0) ^ β) ^ t *
            (ENNReal.ofReal ((2 ^ n) ^ (-2 * t) * Real.exp (γ ^ 2 * Real.log (2 ^ n) / 2 *
              (t ^ 2 - t))) *
              ∫⁻ ω, regularizedGMC P Xc γ (r + Real.log (2 ^ n)) ω (A 0) ^ t ∂P) := by
          rw [hscale]
      _ ≤ ENNReal.ofReal ((2 ^ (n + 1) * R0) ^ β) ^ t *
            (ENNReal.ofReal ((2 ^ n) ^ (-2 * t) * Real.exp (γ ^ 2 * Real.log (2 ^ n) / 2 *
              (t ^ 2 - t))) * K0) := by
          gcongr
          exact hK0 _ (by have := Real.log_nonneg hc; linarith)
      _ = (ENNReal.ofReal ((2 * R0) ^ (β * t)) * K0) * ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ) ^ n := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ht.le, ← mul_assoc,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity),
            exteriorMoment_coeff_eq hR0pos β t γ n]
          rw [ENNReal.ofReal_mul (by positivity)]
          ring
  calc ∫⁻ ω, (∫⁻ x in {x : ℂ | R0 ≤ ‖x‖}, ENNReal.ofReal (‖x‖ ^ β)
        ∂regularizedGMC P Xc γ r ω) ^ t ∂P
      ≤ ∫⁻ ω, (∑' n, f n ω) ^ t ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpt ω) ht.le
    _ ≤ _ := lintegral_tsum_rpow_le_of_geometric f hfm ht hmom

end DOZZ.Proofs
