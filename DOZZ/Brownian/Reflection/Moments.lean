/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.MassBlocks
public import DOZZ.Brownian.Reflection.Entrance
public import DOZZ.Brownian.Lateral.SharpPositive
public import DOZZ.Brownian.Coupling.GridIdentification
public import DOZZ.Brownian.ReflectionRLimit
public import DOZZ.Brownian.Lateral.ReflectionInverse

/-!
# Moments of the two-sided reflection mass

With Hölder exponent `5/4` the block envelopes are summable: polynomially, uniformly for
`0 ≤ ν ≤ ν₀`, giving a uniform subunit moment, and exponentially at positive drift, giving every
moment below `4/γ²` uniformly on compact parameter ranges ([KRV, §12.3]). On the transplanted
ordered coupling the small-power moments tend to one at zero drift, given a.s. nonvanishing of the
lateral measure, and the initial unit block has inverse moments given the lateral inverse unit
moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The reciprocal power `n^{-3/2}` is at most `2^{3/2} (n+1)^{-3/2}` for `n ≥ 1`. -/
theorem nat_rpow_neg_three_halves_le (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 2 ^ (3 / 2 : ℝ) * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hle : (n : ℝ) + 1 ≤ 2 * n := by linarith
  rw [Real.rpow_neg hn0.le, Real.rpow_neg (by linarith)]
  have hpos1 : 0 < ((n : ℝ) + 1) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hpos2 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hmono : ((n : ℝ) + 1) ^ (3 / 2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) hn0.le]
    exact Real.rpow_le_rpow (by linarith) hle (by norm_num)
  rw [← div_eq_mul_inv, le_div_iff₀ hpos1, inv_mul_eq_div, div_le_iff₀ hpos2]
  linarith [hmono]

/-- One-time exponential moments of a conditioned entrance law along integer times, in the shifted
polynomial form `K (n+1)^{-3/2}` valid also at `n = 0`. -/
theorem isNegativeConditionedBrownianLaw_exp_eval_le_succ (a : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ν : ℝ, ∀ Q : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν Q →
      ∀ n : ℕ, (∫⁻ p, ENNReal.ofReal (Real.exp (a * p (n : ℝ≥0))) ∂Q) ≤
        ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) := by
  set K₀ : ℝ := Real.sqrt (2 / Real.pi) * (2 / a ^ 3) with hK₀
  have hK₀0 : 0 ≤ K₀ := by positivity
  refine ⟨max 1 (2 ^ (3 / 2 : ℝ) * K₀), le_max_left _ _, ?_⟩
  intro ν Q hQ n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine (isNegativeConditionedBrownianLaw_exp_eval_le_one ha.le hQ _).trans ?_
    simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one]
    exact ENNReal.one_le_ofReal.mpr (le_max_left _ _)
  · have hnpos : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    refine (isNegativeConditionedBrownianLaw_exp_eval_le ha hQ (n : ℝ≥0) hnpos).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hshift := nat_rpow_neg_three_halves_le n hn
    simp only [NNReal.coe_natCast]
    calc K₀ * (n : ℝ) ^ (-(3 / 2 : ℝ))
        ≤ K₀ * (2 ^ (3 / 2 : ℝ) * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hshift hK₀0
      _ = (2 ^ (3 / 2 : ℝ) * K₀) * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ max 1 (2 ^ (3 / 2 : ℝ) * K₀) * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)

/-- Polynomial block envelopes for conditioned entrance laws with bounded drift. -/
theorem negativeConditioned_blockEnvelope_le_poly (θ r ν₀ : ℝ) (hθ : 0 < θ) (hr : 1 < r) :
    ∃ K : ℝ, 1 ≤ K ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν ≤ ν₀ → ∀ Q : Measure BrownianPath,
      IsNegativeConditionedBrownianLaw ν Q → ∀ n : ℕ,
        (∫⁻ p, positiveBlockEnvelope θ n p ∂Q) ≤
          ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  obtain ⟨K, hK, hKbound⟩ := isNegativeConditionedBrownianLaw_exp_eval_le_succ (r * θ)
    (mul_pos hr0 hθ)
  obtain ⟨C, hC, hCbound⟩ := isNegativeConditionedBrownianLaw_unitIncrement_exp_le
    (r / (r - 1) * θ) ν₀ (mul_nonneg (div_nonneg hr0.le hr1.le) hθ.le)
  refine ⟨K, hK, C, hC, ?_⟩
  intro ν hν Q hQ n
  refine (positiveBlockEnvelope_lintegral_le Q θ r hθ.le hr n).trans ?_
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hKbound ν Q hQ n) (one_div_nonneg.mpr hr0.le))
    (ENNReal.rpow_le_rpow (hCbound ν hν Q hQ n) (div_nonneg hr1.le hr0.le))

/-- Exponential block envelopes for conditioned entrance laws with drift in a compact range
bounded away from zero. -/
theorem negativeConditioned_blockEnvelope_le_exp (θ r ν₁ ν₂ : ℝ) (hθ : 0 < θ) (hr : 1 < r)
    (hν₁ : 0 < ν₁) :
    ∃ K c : ℝ, 0 ≤ K ∧ 0 < c ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν₁ ≤ ν → ν ≤ ν₂ →
      ∀ Q : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν Q → ∀ n : ℕ,
        (∫⁻ p, positiveBlockEnvelope θ n p ∂Q) ≤
          ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r) := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  obtain ⟨K, c, hK, hc, hKbound⟩ :=
    isNegativeConditionedBrownianLaw_exp_eval_le_exp (ν₂ := ν₂) hν₁ (mul_pos hr0 hθ)
  obtain ⟨C, hC, hCbound⟩ := isNegativeConditionedBrownianLaw_unitIncrement_exp_le
    (r / (r - 1) * θ) ν₂ (mul_nonneg (div_nonneg hr0.le hr1.le) hθ.le)
  refine ⟨K, c, hK, hc, C, hC, ?_⟩
  intro ν hν₁ν hνν₂ Q hQ n
  refine (positiveBlockEnvelope_lintegral_le Q θ r hθ.le hr n).trans ?_
  exact mul_le_mul' (ENNReal.rpow_le_rpow (hKbound ν hν₁ν hνν₂ Q hQ n)
      (one_div_nonneg.mpr hr0.le))
    (ENNReal.rpow_le_rpow (hCbound ν hνν₂ Q hQ n) (div_nonneg hr1.le hr0.le))

/-- Shifted polynomial envelopes of order `s > 1` are summable in the extended reals. -/
theorem ennreal_tsum_ofReal_succ_rpow_lt_top (K s : ℝ) (hs : 1 < s) :
    ∑' n : ℕ, ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-s)) < ⊤ := by
  have hsum : Summable (fun n : ℕ => K * ((n : ℝ) + 1) ^ (-s)) := by
    have h := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hs)
    refine (h.mul_left K).congr fun n => ?_
    simp only [Nat.cast_add, Nat.cast_one]
    rw [Real.rpow_neg (by positivity)]
  exact hsum.tsum_ofReal_lt_top

/-- Roots of shifted polynomial envelopes, the form produced by Hölder. -/
theorem ennreal_tsum_poly_envelope_lt_top (K : ℝ) (hK : 0 ≤ K) (C : ℝ≥0∞) (hC : C < ⊤)
    {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e) (hdecay : 1 < 3 / 2 * (1 / r)) :
    ∑' n : ℕ, ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) ^ (1 / r) * C ^ e < ⊤ := by
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ (ENNReal.rpow_lt_top_of_nonneg he hC.ne)
  have heq : ∀ n : ℕ, ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) ^ (1 / r) =
      ENNReal.ofReal (K ^ (1 / r) * ((n : ℝ) + 1) ^ (-(3 / 2 * (1 / r)))) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK (Real.rpow_nonneg hn _))
      (one_div_nonneg.mpr hr.le), Real.mul_rpow hK (Real.rpow_nonneg hn _),
      ← Real.rpow_mul hn]
    ring_nf
  simp_rw [heq]
  exact ennreal_tsum_ofReal_succ_rpow_lt_top _ _ hdecay

/-- Roots of exponential envelopes are summable. -/
theorem ennreal_tsum_exp_envelope_lt_top (K c : ℝ) (hK : 0 ≤ K) (hc : 0 < c)
    (C : ℝ≥0∞) (hC : C < ⊤) {r e : ℝ} (hr : 0 < r) (he : 0 ≤ e) :
    ∑' n : ℕ, ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ e < ⊤ := by
  rw [ENNReal.tsum_mul_right]
  refine ENNReal.mul_lt_top ?_ (ENNReal.rpow_lt_top_of_nonneg he hC.ne)
  have heq : ∀ n : ℕ, ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) =
      ENNReal.ofReal (K ^ (1 / r) * Real.exp (-(c / r)) ^ n) := by
    intro n
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hK (Real.exp_pos _).le)
      (one_div_nonneg.mpr hr.le), Real.mul_rpow hK (Real.exp_pos _).le,
      ← Real.exp_mul, ← Real.exp_nat_mul]
    congr 3
    ring
  simp_rw [heq]
  have hq : Real.exp (-(c / r)) < 1 := Real.exp_lt_one_iff.mpr (by
    have : 0 < c / r := div_pos hc hr
    linarith)
  exact ((summable_geometric_of_lt_one (Real.exp_pos _).le hq).mul_left _).tsum_ofReal_lt_top

/-- Roots of Hölder exponential envelopes are again exponential envelopes. -/
theorem exp_envelope_rpow_eq (K c r e q : ℝ) (C : ℝ≥0∞) (hr : 0 < r) (hq : 0 < q) (n : ℕ) :
    (ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ e) ^ (1 / q) =
      ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / (r * q)) * C ^ (e / q) := by
  have hq' : 0 ≤ 1 / q := one_div_nonneg.mpr hq.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq', ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
  congr 2
  · field_simp
  · field_simp

/-- The pushed-forward envelope expectation of a path coordinate. -/
theorem lintegral_positiveBlockEnvelope_comp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (θ : ℝ) (n : ℝ≥0) (X : Ω → BrownianPath) (hX : AEMeasurable X P) :
    (∫⁻ ω, positiveBlockEnvelope θ n (X ω) ∂P) = ∫⁻ p, positiveBlockEnvelope θ n p ∂P.map X :=
  (lintegral_map' (measurable_positiveBlockEnvelope θ n).aemeasurable hX).symm

/-- A lateral measure has uniformly bounded closed unit-window moments at every nonnegative
subcritical order. -/
theorem lateralGMC_Icc_unit_moment_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ q : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (a : ℝ) :
    (∫⁻ ω, (Z ω (Icc a (a + 1))) ^ q ∂P) ≤ ∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P := by
  rw [lateralGMC_Icc_moment_eq_Ioc P γ Z hZ a (a + 1) q (by linarith)]
  have h := lateralGMC_interval_moment_translation_eq P γ Z hZ 0 1 q a
  simp only [zero_add] at h
  rw [add_comm 1 a] at h
  exact h.le

/-- At a fixed positive drift, every positive moment below `4/γ²` of the two-sided
reflection mass is finite. -/
theorem twoSidedReflectionMass_rpow_lintegral_lt_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν q : ℝ) (hγ : 0 < γ) (hν : 0 < ν)
    (hq0 : 0 < q) (hq : q < 4 / γ ^ 2)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) (hZ : IsLateralGMCOf P γ Z)
    (hInd : IndepFun B Z P) :
    (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P) < ⊤ := by
  set r : ℝ := 5 / 4 with hr
  have hr1 : 1 < r := by norm_num [hr]
  have hr0 : 0 < r := by norm_num [hr]
  have he : 0 ≤ (r - 1) / r := by norm_num [hr]
  obtain ⟨K, c, hK, hc, C, hC, henv⟩ :=
    negativeConditioned_blockEnvelope_le_exp (q * γ) r ν ν (mul_pos hq0 hγ) hr1 hν
  let g : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r)
  have hg₁ : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω).1 ∂P) ≤ g n := by
    intro n
    rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.1.1]
    exact henv ν le_rfl le_rfl _ hB.1.2 n
  have hg₂ : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω).2 ∂P) ≤ g n := by
    intro n
    rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.2.1.1]
    exact henv ν le_rfl le_rfl _ hB.2.1.2 n
  let L : ℝ≥0∞ := ∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P
  have hL : L < ⊤ := lateralGMC_interval_nonnegative_moment_finite P γ Z hZ 0 1 q hq0.le hq
  have hS : halfLineBlockBound q L g < ⊤ := by
    refine halfLineBlockBound_lt_top hq0 hL (fun _ => ?_) (fun _ => ?_)
    · exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC hr0 he
    · simp_rw [g, exp_envelope_rpow_eq K c r ((r - 1) / r) q C hr0 hq0]
      exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC (mul_pos hr0 hq0)
        (div_nonneg he hq0.le)
  have hbound := twoSidedReflectionMass_rpow_lintegral_le_blockBound P γ q hγ.le hq0 B Z
    (aemeasurable_of_twoSidedConditioned hB) hZ.2.2.2.1 hZ.2.2.2.2.1
    (lateralGMC_singleton_ae P γ Z hZ 0) hInd L
    (lateralGMC_Icc_unit_moment_le P γ q Z hZ) g hg₁ hg₂
  refine lt_of_le_of_lt hbound (ENNReal.mul_lt_top ?_ (ENNReal.add_lt_top.mpr ⟨hS, hS⟩))
  exact ENNReal.rpow_lt_top_of_nonneg hq0.le (by norm_num)

/-- One subunit moment of the two-sided reflection mass is bounded uniformly over all drifts
`ν ≤ ν₀`. The lateral measure enters only through measurability, local finiteness, a null origin
and a uniform bound for its closed unit-window moments. -/
theorem twoSidedReflectionMass_rpow_lintegral_le_zeroDrift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₀ q : ℝ) (hγ : 0 < γ)
    (hq0 : 0 < q) (hq1 : q ≤ 1) (Z : Ω → Measure ℝ) (hZm : AEMeasurable Z P)
    (hZfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) (hZ0 : ∀ᵐ ω ∂P, Z ω {0} = 0)
    (L : ℝ≥0∞) (hL : L < ⊤) (hLb : ∀ a : ℝ, (∫⁻ ω, (Z ω (Icc a (a + 1))) ^ q ∂P) ≤ L) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν ≤ ν₀ → ∀ B : Ω → BrownianPath × BrownianPath,
      IsTwoSidedConditionedBrownianProcess P B ν → IndepFun B Z P →
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P) ≤ C := by
  set r : ℝ := 5 / 4 with hr
  have hr1 : 1 < r := by norm_num [hr]
  have hr0 : 0 < r := by norm_num [hr]
  have he : 0 ≤ (r - 1) / r := by norm_num [hr]
  obtain ⟨K, hK, C, hC, henv⟩ :=
    negativeConditioned_blockEnvelope_le_poly (q * γ) r ν₀ (mul_pos hq0 hγ) hr1
  let g : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (K * ((n : ℝ) + 1) ^ (-(3 / 2 : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r)
  have hS : halfLineBlockBound q L g < ⊤ := by
    refine halfLineBlockBound_lt_top hq0 hL (fun _ => ?_) (fun h => absurd hq1 (not_le.mpr h))
    exact ennreal_tsum_poly_envelope_lt_top K (by linarith) C hC hr0 he (by norm_num [hr])
  refine ⟨3 ^ q * (halfLineBlockBound q L g + halfLineBlockBound q L g),
    ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le (by norm_num))
      (ENNReal.add_lt_top.mpr ⟨hS, hS⟩), ?_⟩
  intro ν hν B hB hInd
  have hg₁ : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω).1 ∂P) ≤ g n := by
    intro n
    rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.1.1]
    exact henv ν hν _ hB.1.2 n
  have hg₂ : ∀ n : ℕ, (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ω).2 ∂P) ≤ g n := by
    intro n
    rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.2.1.1]
    exact henv ν hν _ hB.2.1.2 n
  exact twoSidedReflectionMass_rpow_lintegral_le_blockBound P γ q hγ.le hq0 B Z
    (aemeasurable_of_twoSidedConditioned hB) hZm hZfin hZ0 hInd L hLb g hg₁ hg₂

/-- Half-line moments at the top order of a compact range, uniformly over a compact range of
positive drifts, for an arbitrary measure whose closed unit-window moments are bounded. -/
theorem positiveLateralMass_rpow_lintegral_le_compact_drift
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₁ ν₂ q : ℝ) (hγ : 0 < γ)
    (hν₁ : 0 < ν₁) (hq0 : 0 < q) (Z : Ω → Measure ℝ) (hZm : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Ioc a b) < ⊤)
    (L : ℝ≥0∞) (hL : L < ⊤) (hLb : ∀ n : ℕ, (∫⁻ ω, (Z ω (Ioc (n : ℝ) ((n : ℝ) + 1))) ^ q ∂P) ≤ L) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν₁ ≤ ν → ν ≤ ν₂ → ∀ X : Ω → BrownianPath,
      IsNegativeConditionedBrownianProcess P X ν → IndepFun X Z P →
        (∫⁻ ω, (positiveLateralMass γ (X ω) (Z ω)) ^ q ∂P) ≤ C := by
  set r : ℝ := 5 / 4 with hr
  have hr1 : 1 < r := by norm_num [hr]
  have hr0 : 0 < r := by norm_num [hr]
  have he : 0 ≤ (r - 1) / r := by norm_num [hr]
  obtain ⟨K, c, hK, hc, C, hC, henv⟩ :=
    negativeConditioned_blockEnvelope_le_exp (q * γ) r ν₁ ν₂ (mul_pos hq0 hγ) hr1 hν₁
  let g : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r)
  have hS : halfLineBlockBound q L g < ⊤ := by
    refine halfLineBlockBound_lt_top hq0 hL (fun _ => ?_) (fun _ => ?_)
    · exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC hr0 he
    · simp_rw [g, exp_envelope_rpow_eq K c r ((r - 1) / r) q C hr0 hq0]
      exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC (mul_pos hr0 hq0)
        (div_nonneg he hq0.le)
  refine ⟨halfLineBlockBound q L g, hS, ?_⟩
  intro ν hν₁ν hνν₂ X hX hInd
  apply positiveLateralMass_rpow_lintegral_le_blockBound P γ q hγ.le hq0 X Z hX.1 hZm hfin hInd
    L hLb g
  intro n
  rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hX.1]
  exact henv ν hν₁ν hνν₂ _ hX.2 n

/-- Two-sided reflection moments of every order in `[0, q]`, uniformly over a compact range of
positive drifts, for a lateral measure with `q < 4/γ²`. -/
theorem twoSidedReflectionMass_rpow_lintegral_le_compact
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₁ ν₂ q : ℝ) (hγ : 0 < γ)
    (hν₁ : 0 < ν₁) (hq0 : 0 < q) (hq : q < 4 / γ ^ 2)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν₁ ≤ ν → ν ≤ ν₂ → ∀ s : ℝ, 0 ≤ s → s ≤ q →
      ∀ B : Ω → BrownianPath × BrownianPath, IsTwoSidedConditionedBrownianProcess P B ν →
        IndepFun B Z P → (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) s ∂P) ≤ C := by
  have hP : IsProbabilityMeasure P := hZ.2.2.1
  set r : ℝ := 5 / 4 with hr
  have hr1 : 1 < r := by norm_num [hr]
  have hr0 : 0 < r := by norm_num [hr]
  have he : 0 ≤ (r - 1) / r := by norm_num [hr]
  obtain ⟨K, c, hK, hc, C, hC, henv⟩ :=
    negativeConditioned_blockEnvelope_le_exp (q * γ) r ν₁ ν₂ (mul_pos hq0 hγ) hr1 hν₁
  let g : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (K * Real.exp (-c * (n : ℝ))) ^ (1 / r) * C ^ ((r - 1) / r)
  let L : ℝ≥0∞ := ∫⁻ ω, (Z ω (Ioc 0 1)) ^ q ∂P
  have hL : L < ⊤ := lateralGMC_interval_nonnegative_moment_finite P γ Z hZ 0 1 q hq0.le hq
  have hS : halfLineBlockBound q L g < ⊤ := by
    refine halfLineBlockBound_lt_top hq0 hL (fun _ => ?_) (fun _ => ?_)
    · exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC hr0 he
    · simp_rw [g, exp_envelope_rpow_eq K c r ((r - 1) / r) q C hr0 hq0]
      exact ennreal_tsum_exp_envelope_lt_top K c hK hc C hC (mul_pos hr0 hq0)
        (div_nonneg he hq0.le)
  let Ctop : ℝ≥0∞ := 3 ^ q * (halfLineBlockBound q L g + halfLineBlockBound q L g)
  have hCtop : Ctop < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hq0.le (by norm_num))
    (ENNReal.add_lt_top.mpr ⟨hS, hS⟩)
  refine ⟨1 + Ctop, ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, hCtop⟩, ?_⟩
  intro ν hν₁ν hνν₂ s hs0 hsq B hB hInd
  have htop : (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P) ≤ Ctop := by
    apply twoSidedReflectionMass_rpow_lintegral_le_blockBound P γ q hγ.le hq0 B Z
      (aemeasurable_of_twoSidedConditioned hB) hZ.2.2.2.1 hZ.2.2.2.2.1
      (lateralGMC_singleton_ae P γ Z hZ 0) hInd L
      (lateralGMC_Icc_unit_moment_le P γ q Z hZ) g
    · intro n
      rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.1.1]
      exact henv ν hν₁ν hνν₂ _ hB.1.2 n
    · intro n
      rw [lintegral_positiveBlockEnvelope_comp P _ _ _ hB.2.1.1]
      exact henv ν hν₁ν hνν₂ _ hB.2.1.2 n
  calc (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) s ∂P)
      ≤ ∫⁻ ω, 1 + ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P :=
        lintegral_mono fun ω => ennreal_rpow_le_one_add_rpow _ hs0 hsq
    _ = 1 + ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ B Z ω) q ∂P := by
        rw [lintegral_add_left measurable_const]
        simp
    _ ≤ 1 + Ctop := add_le_add le_rfl htop

/-- A lateral measure has closed unit-window moments of order at most one bounded by the
corresponding power of its intensity. -/
theorem lateralGMC_Icc_unit_moment_le_intensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ q : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (a : ℝ) :
    (∫⁻ ω, (Z ω (Icc a (a + 1))) ^ q ∂P) ≤ ENNReal.ofReal (2 * Real.pi) ^ q := by
  have hP : IsProbabilityMeasure P := hZ.2.2.1
  have hm : AEMeasurable (fun ω => Z ω (Icc a (a + 1))) P :=
    (Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hZ.2.2.2.1
  refine (lintegral_rpow_le_mean_rpow P hP _ hm q hq0 hq1).trans ?_
  apply ENNReal.rpow_le_rpow _ hq0
  have he : (∫⁻ ω, Z ω (Icc a (a + 1)) ∂P) = ∫⁻ ω, Z ω (Ioc a (a + 1)) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [lateralGMC_Icc_eq_Ioc_ae P γ Z hZ a (a + 1) (by linarith)] with ω hω
    exact hω
  rw [he, hZ.2.2.2.2.2.2.2.1 a (a + 1) (by linarith)]
  simp

/-- Facts about the lateral measure on the product carrier, read off from the second
coordinate. -/
theorem lateral_prod_snd_facts {Ωc Ω : Type*} [MeasurableSpace Ωc] [MeasurableSpace Ω]
    (Pc : Measure Ωc) [IsProbabilityMeasure Pc] (P : Measure Ω) (γ q : ℝ)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    AEMeasurable (fun ω : Ωc × Ω => Z ω.2) (Pc.prod P) ∧
      (∀ᵐ ω ∂(Pc.prod P), ∀ a b : ℝ, Z ω.2 (Icc a b) < ⊤) ∧
      (∀ᵐ ω ∂(Pc.prod P), Z ω.2 {0} = 0) ∧
      ∀ a : ℝ, (∫⁻ ω, (Z ω.2 (Icc a (a + 1))) ^ q ∂(Pc.prod P)) ≤
        ENNReal.ofReal (2 * Real.pi) ^ q := by
  have hP : IsProbabilityMeasure P := hZ.2.2.1
  have hsnd := (measurePreserving_snd (μ := Pc) (ν := P))
  refine ⟨hZ.2.2.2.1.comp_quasiMeasurePreserving hsnd.quasiMeasurePreserving,
    hsnd.quasiMeasurePreserving.ae (p := fun x => ∀ a b : ℝ, Z x (Icc a b) < ⊤)
      hZ.2.2.2.2.1,
    hsnd.quasiMeasurePreserving.ae (p := fun x => Z x {0} = 0)
      (lateralGMC_singleton_ae P γ Z hZ 0), fun a => ?_⟩
  have hm : AEMeasurable (fun x : Ω => (Z x (Icc a (a + 1))) ^ q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hZ.2.2.2.1)
  have he : (∫⁻ ω, (Z ω.2 (Icc a (a + 1))) ^ q ∂(Pc.prod P)) =
      ∫⁻ x, (Z x (Icc a (a + 1))) ^ q ∂P := by
    rw [← hsnd.map_eq] at hm
    rw [← lintegral_map' hm measurable_snd.aemeasurable, hsnd.map_eq]
  rw [he]
  exact lateralGMC_Icc_unit_moment_le_intensity P γ q Z hZ hq0 hq1 a

/-- Independence is preserved by precomposition with a measure-preserving map. -/
theorem indepFun_comp_measurePreserving {Ω Ω' β β' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace β] [MeasurableSpace β'] {μ : Measure Ω}
    {ν : Measure Ω'} {φ : Ω' → Ω} (hφ : MeasurePreserving φ ν μ) {f : Ω → β} {g : Ω → β'}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) (h : IndepFun f g μ) :
    IndepFun (fun x => f (φ x)) (fun x => g (φ x)) ν := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have hfs : NullMeasurableSet (f ⁻¹' s) μ := hf.nullMeasurableSet_preimage hs
  have hgt : NullMeasurableSet (g ⁻¹' t) μ := hg.nullMeasurableSet_preimage ht
  have h1 := hφ.measure_preimage (hfs.inter hgt)
  have h2 := hφ.measure_preimage hfs
  have h3 := hφ.measure_preimage hgt
  simp only [Set.preimage_inter] at h1
  change ν (φ ⁻¹' (f ⁻¹' s) ∩ φ ⁻¹' (g ⁻¹' t)) =
    ν (φ ⁻¹' (f ⁻¹' s)) * ν (φ ⁻¹' (g ⁻¹' t))
  rw [h1, h2, h3]
  exact h s t hs ht

/-- Small-power reflection moments tend to one at the zero-drift endpoint, for any exponent
`e(ν) ↓ 0`, on the given probability space. The drift laws and independence are required only for
`0 < ν < ν₁`; the lateral measure must be almost surely nonzero. -/
theorem twoSidedReflectionMass_rpow_tendsto_one_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₁ : ℝ) (hγ : 0 < γ) (hν₁ : 0 < ν₁)
    (Z : Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → ν < ν₁ → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z) (hInd : ∀ ν : ℝ, 0 < ν → ν < ν₁ → IndepFun (B ν) Z P)
    (hZpos : ∀ᵐ ω ∂P, Z ω ≠ 0)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0)) (he0 : ∀ ν : ℝ, 0 < ν → 0 ≤ e ν) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (e ν) ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have hP : IsProbabilityMeasure P := hZ.2.2.1
  obtain ⟨Ωc, _, Pc, Bc, hPc, hcoup⟩ := twoSidedConditionedBrownian_orderedCoupling_exists
  have hfacts := lateral_prod_snd_facts Pc P γ (1 / 2) Z hZ (by norm_num) (by norm_num)
  -- one subunit moment of the coupled zero-drift mass on the product carrier
  obtain ⟨C, hC, hCbound⟩ := twoSidedReflectionMass_rpow_lintegral_le_zeroDrift (Pc.prod P) γ 0
    (1 / 2) hγ (by norm_num) (by norm_num) (fun ω : Ωc × Ω => Z ω.2) hfacts.1 hfacts.2.1
    hfacts.2.2.1 _ (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    hfacts.2.2.2
  have hBc0 : IsTwoSidedConditionedBrownianProcess (Pc.prod P) (fun ω : Ωc × Ω => Bc 0 ω.1) 0 := by
    have h := hcoup.1 0 le_rfl
    have hfst := (measurePreserving_fst (μ := Pc) (ν := P))
    have hlaw (X : Ωc → BrownianPath) (hX : AEMeasurable X Pc) :
        (Pc.prod P).map (fun ω : Ωc × Ω => X ω.1) = Pc.map X := by
      have h' := AEMeasurable.map_map_of_aemeasurable
        (by rw [hfst.map_eq]; exact hX) measurable_fst.aemeasurable (μ := Pc.prod P) (g := X)
      rw [hfst.map_eq] at h'
      exact h'.symm
    refine ⟨⟨h.1.1.comp_quasiMeasurePreserving hfst.quasiMeasurePreserving, ?_⟩,
      ⟨h.2.1.1.comp_quasiMeasurePreserving hfst.quasiMeasurePreserving, ?_⟩, ?_⟩
    · change IsNegativeConditionedBrownianLaw 0
        ((Pc.prod P).map (fun ω : Ωc × Ω => (fun x => (Bc 0 x).1) ω.1))
      rw [hlaw _ h.1.1]
      exact h.1.2
    · change IsNegativeConditionedBrownianLaw 0
        ((Pc.prod P).map (fun ω : Ωc × Ω => (fun x => (Bc 0 x).2) ω.1))
      rw [hlaw _ h.2.1.1]
      exact h.2.1.2
    · exact indepFun_comp_measurePreserving hfst h.1.1 h.2.1.1 h.2.2
  have hInd0 : IndepFun (fun ω : Ωc × Ω => Bc 0 ω.1) (fun ω : Ωc × Ω => Z ω.2) (Pc.prod P) :=
    indepFun_prod₀ (aemeasurable_of_twoSidedConditioned (hcoup.1 0 le_rfl)) hZ.2.2.2.1
  have hmom := lt_of_le_of_lt (hCbound 0 le_rfl _ hBc0 hInd0) hC
  -- dominated convergence on the coupling, then transfer back for small positive drift
  have hlim := coupling_zeroDrift_rpow_tendsto_one Pc Bc hcoup P γ hγ Z hZ hZpos (1 / 2)
    (by norm_num) hmom e he he0
  have heq : ∀ᶠ ν in 𝓝[>] (0 : ℝ),
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (fun ω : Ωc × Ω => Bc ν ω.1)
        (fun ω => Z ω.2) ω) (e ν) ∂(Pc.prod P)) =
      ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (e ν) ∂P := by
    filter_upwards [Ioo_mem_nhdsGT hν₁] with ν hν
    exact (twoSidedReflectionMass_rpow_lintegral_eq_prod_carrier P Pc γ ν (e ν) (B ν) Z
      (Bc ν) (hB ν hν.1 hν.2) hZ (hInd ν hν.1 hν.2) (hcoup.1 ν hν.1.le)).symm
  have hlim' := hlim.congr' heq
  have h1 : (1 : ℝ) = (1 : ℝ≥0∞).toReal := by simp
  rw [h1]
  exact (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp hlim'

/-- `2ν/γ`-moments at the zero-drift endpoint, assuming the lateral measure is almost surely
nonzero (`DOZZ.reflectionMoment_zeroDrift_tendsto_one` plus that input). -/
theorem reflectionMoment_zeroDrift_tendsto_one_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → IndepFun (B ν) Z P) (hZpos : ∀ᵐ ω ∂P, Z ω ≠ 0) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (2 * ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have he : Tendsto (fun ν : ℝ => 2 * ν / γ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ν : ℝ => 2 * ν / γ) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact twoSidedReflectionMass_rpow_tendsto_one_of_ne_zero P γ 1 hγ one_pos Z B
    (fun ν hν _ => hB ν hν) hZ (fun ν hν _ => hInd ν hν) hZpos _ he
    (fun ν hν => (div_pos (mul_pos two_pos hν) hγ).le)

/-- `ν/γ`-moments at the zero-drift endpoint, assuming the lateral measure is almost surely
nonzero (`DOZZ.lastone_brownian_smallPower_limit` plus that input). -/
theorem lastone_brownian_smallPower_limit_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → IndepFun (B ν) Z P) (hZpos : ∀ᵐ ω ∂P, Z ω ≠ 0) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have he : Tendsto (fun ν : ℝ => ν / γ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ν : ℝ => ν / γ) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact twoSidedReflectionMass_rpow_tendsto_one_of_ne_zero P γ 1 hγ one_pos Z B
    (fun ν hν _ => hB ν hν) hZ (fun ν hν _ => hInd ν hν) hZpos _ he
    (fun ν hν => (div_pos hν hγ).le)

/-- The full coefficient tends to `-1` at `Q`, assuming the lateral measure is almost surely
nonzero (`DOZZ.reflectionR_tendsto_Q` plus that input). -/
theorem reflectionR_tendsto_Q_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ μ : ℝ)
    (hγ : 0 < γ) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z)
    (hZpos : ∀ᵐ ω ∂P, Z ω ≠ 0) :
    Tendsto (fun α : ℝ => reflectionR P γ μ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by
  have hQ : Q γ - γ / 2 = 2 / γ := by unfold Q; ring
  have hν₁ : 0 < Q γ - γ / 2 := by rw [hQ]; positivity
  have hdata : ∀ ν : ℝ, 0 < ν → ν < Q γ - γ / 2 →
      IsReflectionData P γ (Q γ - ν) (B (Q γ - ν)) Z := fun ν hν hν₁ =>
    hData (Q γ - ν) (by linarith) (by linarith)
  have hZ : IsLateralGMCOf P γ Z := (hdata _ (half_pos hν₁) (half_lt_self hν₁)).2.1
  have he : Tendsto (fun ν : ℝ => 2 * ν / γ) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ν : ℝ => 2 * ν / γ) := by fun_prop
    simpa using (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  have hMoment := twoSidedReflectionMass_rpow_tendsto_one_of_ne_zero P γ (Q γ - γ / 2) hγ hν₁ Z
    (fun ν => B (Q γ - ν))
    (fun ν hν hν₁' => by simpa using (hdata ν hν hν₁').1) hZ
    (fun ν hν hν₁' => (hdata ν hν hν₁').2.2) hZpos _ he
    (fun ν hν => (div_pos (mul_pos two_pos hν) hγ).le)
  exact reflectionR_tendsto_Q_of_zeroDriftMoment P γ μ hγ hμ B Z hMoment

/-- The initial positive unit block of the reflection mass, as written in the statement
`DOZZ.conditionedMass_zeroDrift_uniform_moments`. -/
noncomputable def initialUnitBlockMass (γ : ℝ) (p : BrownianPath) (μ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal
    (if h : 0 ≤ t ∧ t ≤ 1 then Real.exp (γ * p ⟨t, h.1⟩) else 0) ∂μ

/-- The initial block is at least the oscillation-attenuated lateral unit mass. -/
theorem initialUnitBlockMass_ge (γ : ℝ) (hγ : 0 ≤ γ) (p : BrownianPath) (μ : Measure ℝ) :
    ENNReal.ofReal (Real.exp (γ * (p 0 - brownianUnitNorm (brownianShiftPath 0 p)))) *
        μ (Icc 0 1) ≤ initialUnitBlockMass γ p μ := by
  unfold initialUnitBlockMass
  rw [← lintegral_indicator_const measurableSet_Icc]
  apply lintegral_mono
  intro t
  beta_reduce
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem ht]
    have h : 0 ≤ t ∧ t ≤ 1 := ht
    simp only [h.1, h.2, and_self, dite_true]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hγ
    let s : ℝ≥0 := ⟨t, h.1⟩
    have hu : s ≤ 1 := by
      change (s : ℝ) ≤ 1
      exact h.2
    have hn := ((brownianShiftPath 0 p).restrict (Icc 0 (1 : ℝ≥0))).norm_coe_le_norm
      ⟨s, ⟨bot_le, hu⟩⟩
    change |p ((0 : ℝ≥0) + s) - p 0| ≤ brownianUnitNorm (brownianShiftPath 0 p) at hn
    rw [zero_add] at hn
    change p 0 - brownianUnitNorm (brownianShiftPath 0 p) ≤ p s
    have := (abs_le.mp hn).1
    linarith
  · rw [indicator_of_notMem ht]
    exact zero_le

/-- The initial block is measurable along an a.e.-measurable path and lateral measure that is
a.s. finite on bounded intervals. -/
theorem initialUnitBlockMass_aemeasurable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (X : Ω → BrownianPath) (Z : Ω → Measure ℝ) (hX : AEMeasurable X P)
    (hZ : AEMeasurable Z P) (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) :
    AEMeasurable (fun ω => initialUnitBlockMass γ (X ω) (Z ω)) P := by
  let I : Set ℝ := Icc 0 1
  let f : BrownianPath × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal
    (if 0 ≤ z.2 ∧ z.2 ≤ 1 then Real.exp (γ * z.1 (Real.toNNReal z.2)) else 0)
  have hf : Measurable f := by
    apply ENNReal.measurable_ofReal.comp
    apply Measurable.ite
    · exact (measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    · exact Real.measurable_exp.comp (measurable_const.mul
        (continuous_eval.comp (continuous_fst.prodMk
          (continuous_real_toNNReal.comp continuous_snd))).measurable)
    · exact measurable_const
  have hk := measurable_lintegral_finiteMeasure_parameter hf
  have hr : Measurable (fun μ : Measure ℝ => finiteRestrictionOnSet I μ) :=
    measurable_finiteRestrictionOnSet I measurableSet_Icc
  have hp : AEMeasurable (fun ω => (X ω, finiteRestrictionOnSet I (Z ω))) P :=
    hX.prodMk (hr.comp_aemeasurable hZ)
  apply (hk.comp_aemeasurable hp).congr
  filter_upwards [hfin] with ω hω
  have hI : Z ω I < ⊤ := hω 0 1
  have he : (finiteRestrictionOnSet I (Z ω) : Measure ℝ) = (Z ω).restrict I := by
    simp [finiteRestrictionOnSet, hI]
  change (∫⁻ s, f (X ω, s) ∂(finiteRestrictionOnSet I (Z ω) : Measure ℝ)) = _
  rw [he, initialUnitBlockMass, ← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  by_cases ht : t ∈ I
  · rw [indicator_of_mem ht]
    have h : 0 ≤ t ∧ t ≤ 1 := ht
    simp only [f, h.1, h.2, and_self, ite_true, dite_true, Real.toNNReal_of_nonneg h.1]
    rfl
  · rw [indicator_of_notMem ht]
    have h : ¬ (0 ≤ t ∧ t ≤ 1) := ht
    simp [h]

/-- Inverse moments of the initial block, uniformly over bounded drifts, from the lateral inverse
unit moment. -/
theorem initialUnitBlockMass_inverse_moment_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ν₀ v : ℝ) (hγ : 0 < γ) (hv : 0 < v) (Z : Ω → Measure ℝ) (hZm : AEMeasurable Z P)
    (hZfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Icc a b) < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, ν ≤ ν₀ → ∀ X : Ω → BrownianPath,
      IsNegativeConditionedBrownianProcess P X ν → IndepFun X Z P →
        (∫⁻ ω, ENNReal.rpow (initialUnitBlockMass γ (X ω) (Z ω)) (-v) ∂P) ≤
          C * ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-v) ∂P := by
  obtain ⟨C, hC, hCbound⟩ :=
    isNegativeConditionedBrownianLaw_unitIncrement_exp_le (v * γ) ν₀ (mul_pos hv hγ).le
  refine ⟨C, hC, ?_⟩
  intro ν hν X hX hInd
  let f : BrownianPath → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (v * γ * brownianUnitNorm (brownianShiftPath 0 p)))
  let g : Measure ℝ → ℝ≥0∞ := fun μ => (μ (Icc 0 1)) ^ (-v)
  have hshift : Continuous (fun p : BrownianPath => brownianShiftPath 0 p) :=
    continuous_brownianShiftPath.comp (continuous_const.prodMk continuous_id)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (measurable_const.mul (continuous_brownianUnitNorm.comp hshift).measurable))
  have hg : Measurable g := ENNReal.continuous_rpow_const.measurable.comp
    (Measure.measurable_coe measurableSet_Icc)
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hf.comp_aemeasurable hX.1) (hg.comp_aemeasurable hZm) (hInd.comp hf hg)
  change (∫⁻ ω, f (X ω) * g (Z ω) ∂P) = (∫⁻ ω, f (X ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) at hprod
  have hzero : ∀ᵐ ω ∂P, X ω 0 = 0 :=
    ae_of_ae_map hX.1 hX.2.2.2.1
  have hfX : (∫⁻ ω, f (X ω) ∂P) ≤ C := by
    rw [← lintegral_map' hf.aemeasurable hX.1]
    exact hCbound ν hν _ hX.2 0
  calc (∫⁻ ω, ENNReal.rpow (initialUnitBlockMass γ (X ω) (Z ω)) (-v) ∂P)
      ≤ ∫⁻ ω, f (X ω) * g (Z ω) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hzero, hZfin] with ω h0 hω
        have hlow := initialUnitBlockMass_ge γ hγ.le (X ω) (Z ω)
        rw [h0, zero_sub] at hlow
        have h := ennreal_rpow_antitone_nonpos _ _ (-v) hlow (by linarith)
        rw [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top (hω 0 1).ne, ennreal_exp_rpow] at h
        have hexp : γ * -brownianUnitNorm (brownianShiftPath 0 (X ω)) * -v =
            v * γ * brownianUnitNorm (brownianShiftPath 0 (X ω)) := by ring
        rw [hexp] at h
        exact h
    _ = (∫⁻ ω, f (X ω) ∂P) * (∫⁻ ω, g (Z ω) ∂P) := hprod
    _ ≤ C * ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-v) ∂P := mul_le_mul_left hfX _

/-- The positive half of `DOZZ.conditionedMass_zeroDrift_uniform_moments`: a subunit moment of the
full mass, uniformly for `0 ≤ ν ≤ ν₀`. -/
theorem conditionedMass_zeroDrift_positive_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₀ : ℝ)
    (hγ : 0 < γ) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ → IndepFun (B ν) Z P) :
    ∃ u : ℝ, 0 < u ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ →
      ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) u ∂P ≤ C := by
  obtain ⟨C, hC, hCbound⟩ := twoSidedReflectionMass_rpow_lintegral_le_zeroDrift P γ ν₀ (1 / 2)
    hγ (by norm_num) (by norm_num) Z hZ.2.2.2.1 hZ.2.2.2.2.1
    (lateralGMC_singleton_ae P γ Z hZ 0) _
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    (lateralGMC_Icc_unit_moment_le_intensity P γ (1 / 2) Z hZ (by norm_num) (by norm_num))
  exact ⟨1 / 2, by norm_num, C, hC, fun ν hν hνν₀ =>
    hCbound ν hνν₀ (B ν) (hB ν hν hνν₀) (hInd ν hν hνν₀)⟩

/-- Proof of `DOZZ.conditionedMass_zeroDrift_uniform_moments`, from the lateral inverse unit
moments. -/
theorem conditionedMass_zeroDrift_uniform_moments_of_inverse
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ ν₀ : ℝ)
    (hγ : 0 < γ) (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ → IndepFun (B ν) Z P)
    (hinv : ∀ v : ℝ, 0 < v → (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-v) ∂P) < ⊤) :
    (∃ u : ℝ, 0 < u ∧ ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ →
        ∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) u ∂P ≤ C) ∧
      ∀ v : ℝ, 0 < v → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ν : ℝ, 0 ≤ ν → ν ≤ ν₀ →
        ∫⁻ ω, ENNReal.rpow (∫⁻ t, ENNReal.ofReal
            (if h : 0 ≤ t ∧ t ≤ 1 then Real.exp (γ * (B ν ω).1 ⟨t, h.1⟩) else 0) ∂Z ω)
          (-v) ∂P ≤ C := by
  refine ⟨conditionedMass_zeroDrift_positive_moment P γ ν₀ hγ Z B hB hZ hInd, ?_⟩
  intro v hv
  obtain ⟨C, hC, hCbound⟩ := initialUnitBlockMass_inverse_moment_le P γ ν₀ v hγ hv Z
    hZ.2.2.2.1 hZ.2.2.2.2.1
  refine ⟨C * ∫⁻ ω, (Z ω (Icc 0 1)) ^ (-v) ∂P, ENNReal.mul_lt_top hC (hinv v hv), ?_⟩
  intro ν hν hνν₀
  exact hCbound ν hνν₀ (fun ω => (B ν ω).1) (hB ν hν hνν₀).1
    ((hInd ν hν hνν₀).comp measurable_fst measurable_id)

end DOZZ.Proofs

end
