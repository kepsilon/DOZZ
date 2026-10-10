/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.UpperConditionedBlocks

/-!
# Uniform positive half-cylinder moments

Compact charge and positive-drift ranges give one below-one normalization bound and one
Brownian increment exponential bound. The resulting geometric block sequence and its positive
roots are summable with common constants. Infinite Minkowski transfers a uniform moment of the
given lateral unit interval to the entire upper-conditioned half-cylinder. The enclosing-order
lemma keeps the full strict subcritical margin needed by the proof of the reflection
statements.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The below-one harmonic normalization increases with the positive drift. -/
theorem conditionedH_one_mono_on_positive {ν₀ ν : ℝ} (hν₀ : 0 < ν₀) (hν : ν₀ ≤ ν) :
    conditionedH ν₀ 1 ≤ conditionedH ν 1 := by
  have hνp : 0 < ν := hν₀.trans_le hν
  rw [conditionedH, ite_eq_right hν₀.ne', conditionedH, ite_eq_right hνp.ne']
  have he : Real.exp (-2 * ν * 1) ≤ Real.exp (-2 * ν₀ * 1) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

/-- A common finite prefactor for the upper-conditioned block envelope estimate. -/
noncomputable def upperConditionedUniformEnvelopeConstant (ν₀ N Θ : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (conditionedH ν₀ 1))⁻¹ * ENNReal.ofReal (Real.exp (Θ * N)) *
    brownianWindowExponentialConstant Θ

/-- Only the lower drift must be positive for finiteness of this comparison constant. -/
theorem upperConditionedUniformEnvelopeConstant_lt_top (ν₀ N Θ : ℝ) (hν₀ : 0 < ν₀) :
    upperConditionedUniformEnvelopeConstant ν₀ N Θ < ⊤ := by
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (conditionedH_one_pos ν₀ hν₀)))
    ENNReal.ofReal_lt_top) (brownianWindowExponentialConstant_lt_top _)

/-- The full actual upper-conditioned block envelope has one common exponential decay
sequence on bounded positive parameter ranges. -/
theorem upperConditioned_positiveBlockEnvelope_uniform_mean_le
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν θ ν₀ N θ₀ Θ : ℝ) (hν₀ : 0 < ν₀) (hθ₀ : 0 < θ₀)
    (hνlo : ν₀ ≤ ν) (hνhi : ν ≤ N) (hθlo : θ₀ ≤ θ) (hθhi : θ ≤ Θ) (n : ℝ≥0) :
    (∫⁻ p, positiveBlockEnvelope θ n p ∂brownianBelowConditionedLaw P ν 1) ≤
      upperConditionedUniformEnvelopeConstant ν₀ N Θ *
        (ENNReal.ofReal (Real.exp (-(θ₀ * ν₀ / 2) * (n : ℝ))) +
          ENNReal.ofReal (Real.exp (Θ - (ν₀ ^ 2 / 8) * (n : ℝ)))) := by
  have hνp : 0 < ν := hν₀.trans_le hνlo
  have hθp : 0 < θ := hθ₀.trans_le hθlo
  have hΘ : 0 < Θ := hθp.trans_le hθhi
  have hH : (ENNReal.ofReal (conditionedH ν 1))⁻¹ ≤
      (ENNReal.ofReal (conditionedH ν₀ 1))⁻¹ :=
    ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal
      (conditionedH_one_mono_on_positive hν₀ hνlo))
  have hExp : ENNReal.ofReal (Real.exp (θ * ν)) ≤ ENNReal.ofReal (Real.exp (Θ * N)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul hθhi hνhi hνp.le hΘ.le))
  have hC := brownianWindowExponentialConstant_mono hθhi
  have hDecay : ENNReal.ofReal (Real.exp (-θ * ν * n / 2)) +
        ENNReal.ofReal (Real.exp (θ - ν ^ 2 * n / 8)) ≤
      ENNReal.ofReal (Real.exp (-(θ₀ * ν₀ / 2) * (n : ℝ))) +
        ENNReal.ofReal (Real.exp (Θ - (ν₀ ^ 2 / 8) * (n : ℝ))) := by
    apply add_le_add
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hp := mul_le_mul hθlo hνlo hν₀.le hθp.le
      have hm := mul_le_mul_of_nonneg_right hp n.coe_nonneg
      linarith
    · apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hs : ν₀ ^ 2 ≤ ν ^ 2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_right hs n.coe_nonneg
      linarith
  exact (upperConditioned_positiveBlockEnvelope_mean_le P hB ν θ hνp.le hθp.le n).trans
    (mul_le_mul' (mul_le_mul' (mul_le_mul' hH hExp) hC) hDecay)

/-- The common scalar block estimate transfers to an arbitrary given lateral family and
keeps the same full lateral measure in each block. -/
theorem upperConditioned_lateralBlock_uniform_moment_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (Kγ Kν : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (hi : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, IndepFun (B ν) (Z γ) P)
    (hLaw : ∀ ν ∈ Kν, P.map (B ν) = brownianBelowConditionedLaw P₀ ν 1)
    (q γ₀ G ν₀ N : ℝ) (hq : 0 < q) (hγ₀ : 0 < γ₀) (hν₀ : 0 < ν₀)
    (hγbound : ∀ γ ∈ Kγ, γ₀ ≤ γ ∧ γ ≤ G)
    (hνbound : ∀ ν ∈ Kν, ν₀ ≤ ν ∧ ν ≤ N)
    (CZ : ℝ≥0∞) (hMoment : ∀ γ ∈ Kγ,
      (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ q ∂P) ≤ CZ) :
    ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ n : ℕ,
      (∫⁻ ω, (positiveLateralBlock γ n (B ν ω) (Z γ ω)) ^ q ∂P) ≤
        (upperConditionedUniformEnvelopeConstant ν₀ N (q * G) * CZ) *
          (ENNReal.ofReal (Real.exp (-(q * γ₀ * ν₀ / 2) * (n : ℝ))) +
            ENNReal.ofReal (Real.exp ((q * G) - (ν₀ ^ 2 / 8) * (n : ℝ)))) := by
  intro γ hγ ν hν n
  have he := lintegral_map' (measurable_positiveBlockEnvelope (q * γ) n).aemeasurable (hB ν hν)
  change (∫⁻ p, positiveBlockEnvelope (q * γ) n p ∂P.map (B ν)) =
    (∫⁻ ω, positiveBlockEnvelope (q * γ) n (B ν ω) ∂P) at he
  rw [hLaw ν hν] at he
  have hb := upperConditioned_positiveBlockEnvelope_uniform_mean_le P₀ hP₀
    ν (q * γ) ν₀ N (q * γ₀) (q * G) hν₀ (mul_pos hq hγ₀)
    (hνbound ν hν).1 (hνbound ν hν).2
    (mul_le_mul_of_nonneg_left (hγbound γ hγ).1 hq.le)
    (mul_le_mul_of_nonneg_left (hγbound γ hγ).2 hq.le) n
  rw [he] at hb
  have h := (positiveLateralBlock_moment_le_lateral_unit_moment P γ q hq.le n
    (B ν) (Z γ) (hB ν hν) (hZ γ hγ) (hi γ hγ ν hν)).trans
      (mul_le_mul' hb (hMoment γ hγ))
  convert h using 1
  simp only [NNReal.coe_natCast]
  ring

/-- A common geometric block estimate gives a common full half-mass moment estimate above
order one. The sum of block roots is controlled before applying infinite Minkowski. -/
theorem positiveLateralMass_uniform_moment_of_block_decay
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (q : ℝ) (hq : 1 ≤ q) (C : ℝ≥0∞) (hC : C < ⊤)
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hBlock : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ n : ℕ,
      (∫⁻ ω, (positiveLateralBlock γ n (B ν ω) (Z γ ω)) ^ q ∂P) ≤
        C * (ENNReal.ofReal (Real.exp (-a * (n : ℝ))) +
          ENNReal.ofReal (Real.exp (c - b * (n : ℝ))))) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C' := by
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let S : ℝ≥0∞ := ∑' n : ℕ, (C * (ENNReal.ofReal (Real.exp (-a * (n : ℝ))) +
    ENNReal.ofReal (Real.exp (c - b * (n : ℝ))))) ^ (1 / q)
  have hS : S < ⊤ := ennreal_tsum_root_exponential_decay_lt_top
    C hC a b c (1 / q) ha hb (one_div_pos.mpr hqp)
  refine ⟨S ^ q, ENNReal.rpow_lt_top_of_nonneg hqp.le hS.ne, ?_⟩
  intro γ hγ ν hν
  have hroot : (∑' n : ℕ,
      (∫⁻ ω, (positiveLateralBlock γ n (B ν ω) (Z γ ω)) ^ q ∂P) ^ (1 / q)) ≤ S :=
    ENNReal.tsum_le_tsum (fun n : ℕ =>
      ENNReal.rpow_le_rpow (hBlock γ hγ ν hν n) (one_div_pos.mpr hqp).le)
  have hmass := lintegral_tsum_rpow_le_root_moments_power P
    (fun n : ℕ => fun ω => positiveLateralBlock γ n (B ν ω) (Z γ ω))
    (fun n => positiveLateralBlock_aemeasurable P γ n (B ν) (Z γ) (hB ν hν) (hZ γ hγ)) q hq
  have hm := hmass.trans (ENNReal.rpow_le_rpow hroot hqp.le)
  simpa only [positiveLateralMass_eq_tsum_blocks] using hm

/-- Bounded charges and positive drifts transfer a uniform given lateral unit moment to a
uniform whole half-cylinder moment. This is the full positive-order analytic assembly. -/
theorem upperConditioned_positiveLateralMass_uniform_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (Kγ Kν : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (hi : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, IndepFun (B ν) (Z γ) P)
    (hLaw : ∀ ν ∈ Kν, P.map (B ν) = brownianBelowConditionedLaw P₀ ν 1)
    (q γ₀ G ν₀ N : ℝ) (hq : 1 ≤ q) (hγ₀ : 0 < γ₀) (hν₀ : 0 < ν₀)
    (hγbound : ∀ γ ∈ Kγ, γ₀ ≤ γ ∧ γ ≤ G)
    (hνbound : ∀ ν ∈ Kν, ν₀ ≤ ν ∧ ν ≤ N)
    (CZ : ℝ≥0∞) (hCZ : CZ < ⊤) (hMoment : ∀ γ ∈ Kγ,
      (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ q ∂P) ≤ CZ) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C' := by
  have hqp : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hC := ENNReal.mul_lt_top
    (upperConditionedUniformEnvelopeConstant_lt_top ν₀ N (q * G) hν₀) hCZ
  exact positiveLateralMass_uniform_moment_of_block_decay P Kγ Kν Z B hZ hB q hq
    (upperConditionedUniformEnvelopeConstant ν₀ N (q * G) * CZ) hC
    (q * γ₀ * ν₀ / 2) (ν₀ ^ 2 / 8) (q * G)
    (div_pos (mul_pos (mul_pos hqp hγ₀) hν₀) (by norm_num))
    (div_pos (sq_pos_of_pos hν₀) (by norm_num))
    (upperConditioned_lateralBlock_uniform_moment_le P P₀ hP₀ Kγ Kν Z B hZ hB hi hLaw
      q γ₀ G ν₀ N hqp hγ₀ hν₀ hγbound hνbound CZ hMoment)

/-- Compact positive drift ranges have a common positive lower endpoint and finite upper
endpoint, without prescribing a particular normalization of the parameter set. -/
theorem conditioned_compact_positive_drift_bounds
    (Kν : Set ℝ) (hKν : IsCompact Kν) (hne : Kν.Nonempty)
    (hν : ∀ ν ∈ Kν, 0 < ν) :
    ∃ ν₀ N : ℝ, 0 < ν₀ ∧ ∀ ν ∈ Kν, ν₀ ≤ ν ∧ ν ≤ N := by
  obtain ⟨ν₀, hlo, hmin⟩ := hKν.exists_isMinOn hne continuous_id.continuousOn
  obtain ⟨N, hhi, hmax⟩ := hKν.exists_isMaxOn hne continuous_id.continuousOn
  exact ⟨ν₀, N, hν ν₀ hlo, fun ν h => ⟨hmin h, hmax h⟩⟩

/-- Compact parameter sets convert the explicit bounded-parameter estimate to the usual
uniform form. Empty charge or drift sets require no choices of endpoints. -/
theorem upperConditioned_positiveLateralMass_compact_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (Kγ Kν : Set ℝ)
    (hKγ : IsCompact Kγ) (hKν : IsCompact Kν)
    (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (hi : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, IndepFun (B ν) (Z γ) P)
    (hLaw : ∀ ν ∈ Kν, P.map (B ν) = brownianBelowConditionedLaw P₀ ν 1)
    (hν : ∀ ν ∈ Kν, 0 < ν) (q : ℝ) (hq : 1 ≤ q)
    (CZ : ℝ≥0∞) (hCZ : CZ < ⊤) (hMoment : ∀ γ ∈ Kγ,
      (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ q ∂P) ≤ CZ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C := by
  classical
  by_cases hγne : Kγ.Nonempty
  · by_cases hνne : Kν.Nonempty
    · obtain ⟨γ₀, G, hγ₀, _, hγbound⟩ :=
        lateralGMC_compact_charge_bounds P Kγ hKγ hγne Z hZ
      obtain ⟨ν₀, N, hν₀, hνbound⟩ :=
        conditioned_compact_positive_drift_bounds Kν hKν hνne hν
      exact upperConditioned_positiveLateralMass_uniform_moment P P₀ hP₀ Kγ Kν Z B
        hZ hB hi hLaw q γ₀ G ν₀ N hq hγ₀ hν₀ hγbound hνbound CZ hCZ hMoment
    · refine ⟨0, bot_lt_top, ?_⟩
      intro γ hγ ν hνm
      exact (hνne ⟨ν, hνm⟩).elim
  · refine ⟨0, bot_lt_top, ?_⟩
    intro γ hγ
    exact (hγne ⟨γ, hγ⟩).elim

/-- Inserting orders zero and one before taking compact extrema gives a negative lower
endpoint and an upper endpoint above one, while preserving strict subcritical slack. This
lets the two-sided assembly use inverse bounds and infinite Minkowski at the same endpoints. -/
theorem lateralGMC_compact_moment_endpoints_across_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Kγ Kq : Set ℝ) (hKγ : IsCompact Kγ) (hKq : IsCompact Kq)
    (hγne : Kγ.Nonempty) (Z : ℝ → Ω → Measure ℝ)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2) :
    ∃ l u δ : ℝ, l < 0 ∧ 1 < u ∧ 0 < δ ∧
      (∀ q ∈ Kq, l < q ∧ q < u) ∧ (∀ γ ∈ Kγ, u + δ ≤ 4 / γ ^ 2) := by
  let K := Kq ∪ ({0, 1} : Set ℝ)
  have hK : IsCompact K := hKq.union (Set.toFinite _).isCompact
  have h0 : (0 : ℝ) ∈ K := Or.inr (by simp)
  have h1 : (1 : ℝ) ∈ K := Or.inr (by simp)
  have hsub : ∀ γ ∈ Kγ, ∀ q ∈ K, q < 4 / γ ^ 2 := by
    intro γ hγ q hqm
    have hγp := (hZ γ hγ).1
    have hγhi := (hZ γ hγ).2.1
    have hs : 0 < γ ^ 2 := sq_pos_of_pos hγp
    rcases hqm with hqm | hqm
    · exact hq γ hγ q hqm
    · have hq01 : q = 0 ∨ q = 1 := by simpa only [mem_insert_iff, mem_singleton_iff] using hqm
      rcases hq01 with rfl | rfl
      · exact div_pos (by norm_num) hs
      · apply (lt_div_iff₀ hs).mpr
        nlinarith
  obtain ⟨l, u, δ, hδ, hend, hmargin⟩ := lateralGMC_compact_moment_endpoints
    Kγ K hKγ hK hγne ⟨0, h0⟩ (fun γ hγ => (hZ γ hγ).1) hsub
  exact ⟨l, u, δ, (hend 0 h0).1, (hend 1 h1).2, hδ,
    fun q hqm => hend q (Or.inl hqm), hmargin⟩

/-- A common enclosing positive order controls every smaller nonnegative order. The zeroth
order contributes exactly one, even if the random half-mass vanishes. -/
theorem positiveLateralMass_uniform_nonnegative_orders_of_enclosing_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν Kq : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P) (u : ℝ)
    (hq : ∀ q ∈ Kq, 0 ≤ q ∧ q ≤ u)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hMoment : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ u ∂P) ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C' := by
  refine ⟨1 + C, ENNReal.add_lt_top.mpr ⟨by norm_num, hC⟩, ?_⟩
  intro γ hγ ν hν q hqm
  let _ := (hZ γ hγ).2.2.1
  have h := lintegral_rpow_le_endpoint_sum P _
    (positiveLateralMass_aemeasurable P γ (B ν) (Z γ) (hB ν hν) (hZ γ hγ))
    (hq q hqm).1 (hq q hqm).2
  simp only [ENNReal.rpow_zero, lintegral_const, measure_univ, mul_one] at h
  exact h.trans (add_le_add le_rfl (hMoment γ hγ ν hν))

/-- Positive moments under a provided radial ordering transfer with their constants. The
hypothesis is an actual almost sure path ordering, not an assertion of coupling existence. -/
theorem positiveLateralMass_moment_le_of_ordered_radial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ)
    (hγ : 0 ≤ γ) (hq : 0 ≤ q) (B B' : Ω → BrownianPath) (Z : Ω → Measure ℝ)
    (hOrder : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, B ω t ≤ B' ω t) :
    (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) ≤
      ∫⁻ ω, (positiveLateralMass γ (B' ω) (Z ω)) ^ q ∂P := by
  apply lintegral_mono_ae
  filter_upwards [hOrder] with ω hω
  apply ENNReal.rpow_le_rpow _ hq
  apply lintegral_mono
  intro s
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (hω (Real.toNNReal s)) hγ))

/-- The common positive-order half-mass bound survives any given family of ordered radial
paths, with the same original lateral chaos and every compact parameter quantified. -/
theorem positiveLateralMass_uniform_moment_of_ordered_radial
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ Kν Kq : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (B B' : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hq : ∀ q ∈ Kq, 0 ≤ q)
    (hOrder : ∀ ν ∈ Kν, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, B ν ω t ≤ B' ν ω t)
    (C : ℝ≥0∞) (hC : C < ⊤)
    (hMoment : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (positiveLateralMass γ (B' ν ω) (Z γ ω)) ^ q ∂P) ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C' := by
  refine ⟨C, hC, ?_⟩
  intro γ hγ ν hν q hqm
  exact (positiveLateralMass_moment_le_of_ordered_radial P γ q (hZ γ hγ).1.le
    (hq q hqm) (B ν) (B' ν) (Z γ) (hOrder ν hν)).trans (hMoment γ hγ ν hν q hqm)

/-- Subcritical compact moment ranges can be enclosed above one before requesting a single
lateral unit-interval input. The output controls all nonnegative moments in the original set. -/
theorem upperConditioned_positiveLateralMass_compact_orders
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (Kγ Kν Kq : Set ℝ)
    (hKγ : IsCompact Kγ) (hKν : IsCompact Kν) (hKq : IsCompact Kq)
    (hγne : Kγ.Nonempty) (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (hi : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, IndepFun (B ν) (Z γ) P)
    (hLaw : ∀ ν ∈ Kν, P.map (B ν) = brownianBelowConditionedLaw P₀ ν 1)
    (hν : ∀ ν ∈ Kν, 0 < ν)
    (hq : ∀ γ ∈ Kγ, ∀ q ∈ Kq, q < 4 / γ ^ 2)
    (hq0 : ∀ q ∈ Kq, 0 ≤ q)
    (hUnit : ∀ u : ℝ, 1 < u → (∀ γ ∈ Kγ, u < 4 / γ ^ 2) →
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ u ∂P) ≤ C) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C := by
  obtain ⟨l, u, δ, _, hu, hδ, hend, hmargin⟩ :=
    lateralGMC_compact_moment_endpoints_across_one P Kγ Kq hKγ hKq hγne Z hZ hq
  have husub : ∀ γ ∈ Kγ, u < 4 / γ ^ 2 := by
    intro γ hγ
    have hm := hmargin γ hγ
    linarith
  obtain ⟨CZ, hCZ, hMoment⟩ := hUnit u hu husub
  obtain ⟨C, hC, hhalf⟩ := upperConditioned_positiveLateralMass_compact_moment
    P P₀ hP₀ Kγ Kν hKγ hKν Z B hZ hB hi hLaw hν u hu.le CZ hCZ hMoment
  exact positiveLateralMass_uniform_nonnegative_orders_of_enclosing_moment
    P Kγ Kν Kq Z B hZ hB u (fun q hqm => ⟨hq0 q hqm, (hend q hqm).2.le⟩)
    C hC hhalf

/-- The compact subunit range under the upper-conditioned law needs no sharp GMC estimate.
The exact lateral intensity supplies a common order-one input on the unit interval. -/
theorem upperConditioned_positiveLateralMass_compact_subunit_orders
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (P₀ : Measure BrownianPath)
    (hP₀ : IsBrownianReal (fun t p => p t) P₀) (Kγ Kν Kq : Set ℝ)
    (hKγ : IsCompact Kγ) (hKν : IsCompact Kν)
    (Z : ℝ → Ω → Measure ℝ) (B : ℝ → Ω → BrownianPath)
    (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (hB : ∀ ν ∈ Kν, AEMeasurable (B ν) P)
    (hi : ∀ γ ∈ Kγ, ∀ ν ∈ Kν, IndepFun (B ν) (Z γ) P)
    (hLaw : ∀ ν ∈ Kν, P.map (B ν) = brownianBelowConditionedLaw P₀ ν 1)
    (hν : ∀ ν ∈ Kν, 0 < ν) (hq : ∀ q ∈ Kq, 0 ≤ q ∧ q ≤ 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (positiveLateralMass γ (B ν ω) (Z γ ω)) ^ q ∂P) ≤ C := by
  have hUnit : ∀ γ ∈ Kγ,
      (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ (1 : ℝ) ∂P) ≤ ENNReal.ofReal (2 * Real.pi) := by
    intro γ hγ
    simp only [ENNReal.rpow_one]
    rw [lateralGMC_interval_first_moment P γ (Z γ) (hZ γ hγ) 0 1 (by norm_num)]
    simp only [sub_zero, mul_one, le_refl]
  obtain ⟨C, hC, hhalf⟩ := upperConditioned_positiveLateralMass_compact_moment
    P P₀ hP₀ Kγ Kν hKγ hKν Z B hZ hB hi hLaw hν 1 le_rfl
    (ENNReal.ofReal (2 * Real.pi)) ENNReal.ofReal_lt_top hUnit
  exact positiveLateralMass_uniform_nonnegative_orders_of_enclosing_moment
    P Kγ Kν Kq Z B hZ hB 1 hq C hC hhalf


/-- A finite uniform positive moment also gives almost sure finiteness simultaneously for
each fixed parameter pair. No common event over an uncountable parameter range is asserted. -/
theorem positiveLateralMass_finite_ae_of_uniform_positive_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ q : ℝ) (hq : 0 < q)
    (B : Ω → BrownianPath) (Z : Ω → Measure ℝ) (hB : AEMeasurable B P)
    (hZ : IsLateralGMCOf P γ Z) (C : ℝ≥0∞) (hC : C < ⊤)
    (hMoment : (∫⁻ ω, (positiveLateralMass γ (B ω) (Z ω)) ^ q ∂P) ≤ C) :
    ∀ᵐ ω ∂P, positiveLateralMass γ (B ω) (Z ω) < ⊤ := by
  have hm : AEMeasurable (fun ω => (positiveLateralMass γ (B ω) (Z ω)) ^ q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      (positiveLateralMass_aemeasurable P γ B Z hB hZ)
  have hf := ae_lt_top' hm (hMoment.trans_lt hC).ne
  filter_upwards [hf] with ω hω
  exact (ENNReal.rpow_lt_top_iff_of_pos hq).mp hω

end DOZZ.Proofs
