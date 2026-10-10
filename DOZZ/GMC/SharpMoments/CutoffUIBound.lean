/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CoulombCutoffBounds
public import DOZZ.GMC.SharpMoments.CutoffPieces
public import DOZZ.GMC.SharpMoments.PiecesMoment
public import DOZZ.GMC.SharpMoments.WeightedCutoffCompact
public import DOZZ.GMC.SharpMoments.ExteriorMoment
public import DOZZ.GMC.SharpMoments.SeibergUniform

/-! # Uniform positive moments of regularized Coulomb masses

On a compact parameter set, with an order function that is admissible at every root charge and at
the charge at infinity, the positive moments of the regularized Coulomb masses are bounded
uniformly in the parameters and the cutoff: the root pieces are cutoff weighted masses controlled
by the γ-uniform weighted cutoff bound, the bulk piece is a cutoff disk mass, and the exterior
piece is summed over dyadic annuli by exact exterior scaling. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The supports of the partition functions are bounded. -/
theorem partition_support_bounds (partition : GMCChartPartition) :
    ∃ Rf Ri : ℝ, 1 ≤ Rf ∧ 1 ≤ Ri ∧ (∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < Rf) ∧
      ∀ u, partition.infinityWeight u ≠ 0 → ‖u‖ ≤ Ri := by
  obtain ⟨R1, hR1⟩ := partition.finite_hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R2, hR2⟩ := partition.infinity_hasCompactSupport.isCompact.isBounded.subset_closedBall 0
  refine ⟨max (R1 + 1) 1, max R2 1, le_max_right _ _, le_max_right _ _, fun x hx => ?_,
    fun u hu => ?_⟩
  · have hmem := hR1 (subset_tsupport _ (Function.mem_support.mpr hx))
    rw [mem_closedBall, dist_zero_right] at hmem
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · have hmem := hR2 (subset_tsupport _ (Function.mem_support.mpr hu))
    rw [mem_closedBall, dist_zero_right] at hmem
    exact hmem.trans (le_max_left _ _)

/-- The geometric factor of the exterior bound is monotone in the decay rate and in the order. -/
theorem geometric_factor_le {ζ ζ0 t tm : ℝ} (hζ0 : 0 < ζ0) (hζ : ζ0 ≤ ζ) (htm : t ≤ tm) :
    ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ) ^ (1 / max 1 t)) ^ (max 1 t))⁻¹ ≤
      ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ0) ^ (1 / max 1 tm)) ^ (max 1 tm))⁻¹ := by
  set q : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ) with hq
  set q0 : ℝ≥0∞ := ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ0) with hq0
  set m : ℝ := max 1 t with hm
  set mm : ℝ := max 1 tm with hmm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmm1 : 1 ≤ mm := le_max_left _ _
  have hmmm : m ≤ mm := max_le_max le_rfl htm
  have hqq0 : q ≤ q0 := ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hζ)
  have hq01 : q0 ≤ 1 := ENNReal.ofReal_le_one.mpr (Real.rpow_le_one (by norm_num) (by norm_num)
    hζ0.le)
  have hexp : 1 / mm ≤ 1 / m := one_div_le_one_div_of_le (by linarith) hmmm
  have hroot : q ^ (1 / m) ≤ q0 ^ (1 / mm) :=
    (ENNReal.rpow_le_rpow hqq0 (by positivity)).trans
      (ENNReal.rpow_le_rpow_of_exponent_ge hq01 hexp)
  have hd : 1 - q0 ^ (1 / mm) ≤ 1 - q ^ (1 / m) := tsub_le_tsub_left hroot 1
  have hd1 : 1 - q0 ^ (1 / mm) ≤ 1 := tsub_le_self
  refine ENNReal.inv_le_inv.mpr ?_
  calc (1 - q0 ^ (1 / mm)) ^ mm ≤ (1 - q0 ^ (1 / mm)) ^ m :=
        ENNReal.rpow_le_rpow_of_exponent_ge hd1 hmmm
    _ ≤ (1 - q ^ (1 / m)) ^ m := ENNReal.rpow_le_rpow hd (by linarith)

theorem geometric_factor_lt_top {ζ0 tm : ℝ} (hζ0 : 0 < ζ0) :
    ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ0) ^ (1 / max 1 tm)) ^ (max 1 tm))⁻¹ < ⊤ := by
  have hmm : 0 < max 1 tm := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hq0 : ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ0) < 1 :=
    ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) hζ0)
  have hroot : ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ0) ^ (1 / max 1 tm) < 1 :=
    ENNReal.rpow_lt_one hq0 (by positivity)
  refine ENNReal.inv_lt_top.mpr (ENNReal.rpow_pos (tsub_pos_of_lt hroot) ?_)
  exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

/-- A cutoff weighted mass with zero charge is a cutoff disk mass. -/
theorem cutoffWeightedGmcBallMass_zero_charge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ : ℝ) (z : ℂ) (R r : ℝ) (ω : Ω) :
    cutoffWeightedGmcBallMass P Xc γ 0 z R (Real.exp (-r)) ω =
      regularizedGMC P Xc γ r ω (Metric.ball z R) := by
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  rw [cutoffWeightedGmcBallMass, hlog]
  simp

/-- Cutoff weighted masses are measurable in the sample. -/
theorem measurable_cutoffWeightedGmcBallMass
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ α : ℝ) (z : ℂ) (R δ : ℝ) :
    Measurable fun ω => cutoffWeightedGmcBallMass P Xc γ α z R δ ω := by
  have hB : MeasurableSet (Metric.ball z R) := Metric.isOpen_ball.measurableSet
  have hf : Measurable fun x : ℂ => ENNReal.ofReal ((‖x - z‖ + δ) ^ (-γ * α)) :=
    ENNReal.measurable_ofReal.comp (((measurable_id.sub_const z).norm.add_const δ).pow_const _)
  have h := (Measure.measurable_lintegral (hf.indicator hB)).comp
    (regularizedGMC_measurable P X hX Xc hXc γ (Real.log (1 / δ)))
  convert h using 1
  funext ω
  simp only [Function.comp_apply, cutoffWeightedGmcBallMass, lintegral_indicator hB]

/-- Uniform positive moments of regularized Coulomb masses over a compact parameter set. -/
theorem regularizedCoulombMass_moment_uniform_pos
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (partition : GMCChartPartition)
    (N : ℕ) (S : Set (ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ))) (hS : IsCompact S)
    (τ : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ) (hτ : ContinuousOn τ S)
    (hroot : ∀ c ∈ S, ∀ k, 0 < weightedCutoffSlack (c.1, c.2.2.1 k, τ c))
    (hinf : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, max c.2.2.2 0, τ c))
    {ρs : ℝ} (hρs : 0 < ρs) (hρs1 : ρs ≤ 1)
    (hsep : ∀ c ∈ S, ∀ j k, j ≠ k → 2 * ρs ≤ ‖c.2.1 j - c.2.1 k‖) :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ c ∈ S, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, ENNReal.rpow (regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω)
        (τ c) ∂P ≤ K := by
  classical
  let _ : IsProbabilityMeasure P := hX.1
  -- admissibility facts at each parameter
  have hadmInf : ∀ c ∈ S, 0 < c.1 ∧ c.1 < 2 ∧ 0 < τ c ∧ τ c < 4 / c.1 ^ 2 ∧
      τ c < 2 / c.1 * (Q c.1 - max c.2.2.2 0) := by
    intro c hc
    have h := (weightedCutoffSlack_pos_iff _).mp (hinf c hc)
    exact ⟨h.1, h.2.1, h.2.2.2.1, (lt_min_iff.mp h.2.2.2.2).1, (lt_min_iff.mp h.2.2.2.2).2⟩
  -- uniform sizes
  obtain ⟨Zs0, hZs0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => ∑ j, ‖c.2.1 j‖) (by fun_prop)
  obtain ⟨E0, hE0⟩ := hS.exists_bound_of_continuousOn
    (f := fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
      ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2|) (by fun_prop)
  obtain ⟨tm0, htm0⟩ := hS.exists_bound_of_continuousOn hτ
  set Zs : ℝ := max Zs0 0 with hZsdef
  set E : ℝ := max E0 0 with hEdef
  set tm : ℝ := max tm0 0 with htmdef
  have hZs : 0 ≤ Zs := le_max_right _ _
  have hE : 0 ≤ E := le_max_right _ _
  have htm : 0 ≤ tm := le_max_right _ _
  have hZc : ∀ c ∈ S, ∑ j, ‖c.2.1 j‖ ≤ Zs := fun c hc => by
    have h := hZs0 c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at h
    exact h.trans (le_max_left _ _)
  have hEsum : ∀ c ∈ S, ∑ j, |c.1 * c.2.2.1 j| + |c.1 * c.2.2.2| ≤ E := fun c hc => by
    have h := hE0 c hc
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (Finset.sum_nonneg fun j _ =>
      abs_nonneg _) (abs_nonneg _))] at h
    exact h.trans (le_max_left _ _)
  have hEα : ∀ c ∈ S, ∀ j, |c.1 * c.2.2.1 j| ≤ E := fun c hc j => by
    have := Finset.single_le_sum (f := fun j => |c.1 * c.2.2.1 j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith [hEsum c hc, abs_nonneg (c.1 * c.2.2.2)]
  have hEinf : ∀ c ∈ S, |c.1 * c.2.2.2| ≤ E := fun c hc => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => abs_nonneg (c.1 * c.2.2.1 j))
    linarith [hEsum c hc]
  have hτle : ∀ c ∈ S, τ c ≤ tm := fun c hc =>
    ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using htm0 c hc)).trans (le_max_left _ _)
  -- the exterior decay rate is bounded below
  set ζf : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) → ℝ := fun c =>
    2 * τ c + c.1 ^ 2 * τ c / 2 - c.1 ^ 2 * τ c ^ 2 / 2 - max (c.1 * c.2.2.2) 0 * τ c with hζf
  have hζpos : ∀ c ∈ S, 0 < ζf c := by
    intro c hc
    obtain ⟨hγ0, -, ht0, -, htinf⟩ := hadmInf c hc
    have hmax : max (c.1 * c.2.2.2) 0 = c.1 * max c.2.2.2 0 := by
      rw [mul_max_of_nonneg _ _ hγ0.le, mul_zero]
    have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by
      rw [Q]
      field_simp
    have h1 : c.1 * τ c / 2 < Q c.1 - max c.2.2.2 0 := by
      have h := mul_lt_mul_of_pos_left htinf (by positivity : (0 : ℝ) < c.1 / 2)
      have hl : c.1 / 2 * (2 / c.1 * (Q c.1 - max c.2.2.2 0)) = Q c.1 - max c.2.2.2 0 := by
        field_simp
      rw [hl] at h
      linarith
    have hexp : ζf c = c.1 * τ c * ((Q c.1 - max c.2.2.2 0) - c.1 * τ c / 2) := by
      simp only [hζf]
      rw [hmax]
      have h2 : 2 * τ c + c.1 ^ 2 * τ c / 2 = c.1 * Q c.1 * τ c := by rw [hQ]; ring
      linear_combination h2
    rw [hexp]
    exact mul_pos (mul_pos hγ0 ht0) (by linarith)
  have hζcont : ContinuousOn ζf S := by
    have hτ2 : ContinuousOn (fun c => τ c ^ 2) S := hτ.pow 2
    have hγc : Continuous fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) => c.1 := by fun_prop
    have hm : Continuous fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
        max (c.1 * c.2.2.2) 0 := by fun_prop
    exact ((((continuousOn_const.mul hτ).add ((hγc.pow 2).continuousOn.mul hτ |>.div_const 2)).sub
      (((hγc.pow 2).continuousOn.mul hτ2).div_const 2)).sub (hm.continuousOn.mul hτ))
  obtain ⟨ζ0, hζ0b, hζ0⟩ := (eventually_le_of_isCompact_of_pos hS hζcont hζpos).and
    self_mem_nhdsWithin |>.exists
  -- partition supports and the exterior radius
  obtain ⟨Rf, Ri, hRf, hRi, hsuppf, hsuppi⟩ := partition_support_bounds partition
  set R0 : ℝ := max (2 * Zs + 2) Rf with hR0def
  have hR0Z : 2 * Zs + 2 ≤ R0 := le_max_left _ _
  have hR02 : 2 ≤ R0 := le_trans (by linarith) hR0Z
  have hsuppf' : ∀ x, partition.finiteWeight x ≠ 0 → ‖x‖ < R0 := fun x hx =>
    lt_of_lt_of_le (hsuppf x hx) (le_max_right _ _)
  -- pointwise bounds for the weight
  obtain ⟨CR, hCR0, hCR⟩ := coulombCutoffWeight_le_root partition N hZs hE hρs hρs1 hRi hsuppi
  obtain ⟨CB, hCB0, hCB⟩ := coulombCutoffWeight_le_bulk partition N hZs hE hρs hρs1
    (by linarith : (0 : ℝ) ≤ R0)
  obtain ⟨CE, hCE0, hCE⟩ := coulombCutoffWeight_le_exterior partition N hZs hE hR0Z hsuppf'
  -- the uniform weighted cutoff bounds
  have hCk : ∀ k : Fin N, ∃ C : ℝ, 0 < C ∧ ∀ c ∈ S, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      (∫⁻ ω, ENNReal.rpow (cutoffWeightedGmcBallMass P Xc c.1 (c.2.2.1 k) (c.2.1 k) 1 δ ω)
        (τ c) ∂P) ≤ ENNReal.ofReal C := by
    intro k
    have hcont : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
        (c.1, c.2.2.1 k, τ c)) S :=
      (continuous_fst.continuousOn).prodMk ((continuous_apply k |>.comp
        (continuous_fst.comp (continuous_snd.comp continuous_snd))).continuousOn.prodMk hτ)
    obtain ⟨C, hC, hCb⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
      (hS.image_of_continuousOn hcont) (by
        rintro _ ⟨c, hc, rfl⟩
        exact hroot c hc k) (closedBall 0 Zs) (isCompact_closedBall _ _) 1 one_pos
    refine ⟨C, hC, fun c hc δ hδ hδ1 => ?_⟩
    have hzk : c.2.1 k ∈ closedBall (0 : ℂ) Zs := by
      rw [mem_closedBall, dist_zero_right]
      exact (Finset.single_le_sum (f := fun j => ‖c.2.1 j‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ k)).trans (hZc c hc)
    have h := hCb _ ⟨c, hc, rfl⟩ _ hzk δ 1 hδ hδ1 le_rfl
    simpa [Real.one_rpow] using h
  choose Ck hCkpos hCkb using hCk
  have hcont0 : ContinuousOn (fun c : ℝ × ((Fin N → ℂ) × (Fin N → ℝ) × ℝ) =>
      (c.1, (0 : ℝ), τ c)) S :=
    (continuous_fst.continuousOn).prodMk (continuousOn_const.prodMk hτ)
  have hadm0 : ∀ c ∈ S, 0 < weightedCutoffSlack (c.1, (0 : ℝ), τ c) := by
    intro c hc
    obtain ⟨hγ0, hγ2, ht0, ht4, -⟩ := hadmInf c hc
    have hQ0 : 0 < Q c.1 := by rw [Q]; positivity
    refine (weightedCutoffSlack_pos_iff _).mpr ⟨hγ0, hγ2, by simpa using hQ0, ht0, ?_⟩
    refine lt_min ht4 ?_
    have : 4 / c.1 ^ 2 < 2 / c.1 * (Q c.1 - 0) := by
      rw [sub_zero, Q]
      field_simp
      linarith only [pow_pos hγ0 2]
    linarith
  obtain ⟨C0, hC0, hC0b⟩ := weightedCutoff_bound_uniform_compact P X hX Xc hXc _
    (hS.image_of_continuousOn hcont0) (by
      rintro _ ⟨c, hc, rfl⟩
      exact hadm0 c hc) (closedBall 0 0) (isCompact_closedBall _ _) (2 * R0 + 1) (by linarith)
  -- the zero-charge bound on disks about the origin
  have hdisk : ∀ c ∈ S, ∀ R : ℝ, 1 ≤ R → R ≤ 2 * R0 + 1 → ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, regularizedGMC P Xc c.1 r ω (Metric.ball 0 R) ^ τ c ∂P ≤
        ENNReal.ofReal (C0 * (2 * R0 + 1) ^ (4 * tm)) := by
    intro c hc R hR1 hR r hr
    obtain ⟨hγ0, hγ2, ht0, -, -⟩ := hadmInf c hc
    have hδ : Real.exp (-r) ≤ R := (Real.exp_le_one_iff.mpr (by linarith)).trans hR1
    have h := hC0b _ ⟨c, hc, rfl⟩ 0 (mem_closedBall_self le_rfl) (Real.exp (-r)) R
      (Real.exp_pos _) hδ hR
    simp only [cutoffWeightedGmcBallMass_zero_charge] at h
    refine h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC0.le))
    have hexp : c.1 * (Q c.1 - 0) * τ c - c.1 ^ 2 * τ c ^ 2 / 2 ≤ 4 * tm := by
      have hQ : c.1 * Q c.1 = 2 + c.1 ^ 2 / 2 := by rw [Q]; field_simp
      have hγsq : c.1 ^ 2 < 2 ^ 2 := pow_lt_pow_left₀ hγ2 hγ0.le two_ne_zero
      have htt : τ c ≤ tm := hτle c hc
      have hQt : c.1 * (Q c.1 - 0) * τ c = (2 + c.1 ^ 2 / 2) * τ c := by rw [sub_zero, hQ]
      have h1 : c.1 ^ 2 * τ c < 2 ^ 2 * τ c := mul_lt_mul_of_pos_right hγsq ht0
      have h2 : 0 ≤ c.1 ^ 2 * τ c ^ 2 := by positivity
      linarith only [hQt, h1, h2, htt]
    calc Real.rpow R (c.1 * (Q c.1 - 0) * τ c - c.1 ^ 2 * τ c ^ 2 / 2)
        ≤ R ^ (4 * tm) := Real.rpow_le_rpow_of_exponent_le hR1 hexp
      _ ≤ (2 * R0 + 1) ^ (4 * tm) := Real.rpow_le_rpow (by linarith) hR (by positivity)
  -- the uniform constant
  have hζ0pos : 0 < ζ0 := hζ0
  set two : ℝ≥0∞ := (2 : ℝ≥0∞) ^ tm with htwo
  set Nm : ℝ≥0∞ := max 1 (N : ℝ≥0∞) ^ tm with hNm
  set CRm : ℝ≥0∞ := max 1 (ENNReal.ofReal CR) ^ tm with hCRm
  set CBm : ℝ≥0∞ := max 1 (ENNReal.ofReal CB) ^ tm with hCBm
  set CEm : ℝ≥0∞ := max 1 (ENNReal.ofReal CE) ^ tm with hCEm
  set K0 : ℝ≥0∞ := ENNReal.ofReal (C0 * (2 * R0 + 1) ^ (4 * tm)) with hK0
  set Gm : ℝ≥0∞ := ((1 - ENNReal.ofReal ((1 / 2 : ℝ) ^ ζ0) ^ (1 / max 1 tm)) ^ (max 1 tm))⁻¹
    with hGm
  set Vm : ℝ≥0∞ := ENNReal.ofReal ((2 * R0) ^ (E * tm)) * K0 * Gm with hVm
  have hfin : ∀ x : ℝ≥0∞, x ≠ ⊤ → x ^ tm < ⊤ := fun x hx => ENNReal.rpow_lt_top_of_nonneg htm hx
  have hmax : ∀ x : ℝ≥0∞, x ≠ ⊤ → max 1 x ≠ ⊤ := fun x hx => max_ne_top ENNReal.one_ne_top hx
  refine ⟨two * (two * (Nm * ∑ k, CRm * ENNReal.ofReal (Ck k) + CBm * K0) + CEm * Vm), ?_, ?_⟩
  · have hGmt : Gm < ⊤ := geometric_factor_lt_top hζ0pos
    refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    · refine ENNReal.mul_lt_top (hfin _ (by norm_num)) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
      · refine ENNReal.mul_lt_top (hfin _ (hmax _ (ENNReal.natCast_ne_top N)))
          (ENNReal.sum_lt_top.mpr fun k _ => ENNReal.mul_lt_top
            (hfin _ (hmax _ ENNReal.ofReal_ne_top)) ENNReal.ofReal_lt_top)
      · exact ENNReal.mul_lt_top (hfin _ (hmax _ ENNReal.ofReal_ne_top)) ENNReal.ofReal_lt_top
    · exact ENNReal.mul_lt_top (hfin _ (hmax _ ENNReal.ofReal_ne_top))
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) hGmt)
  intro c hc r hr
  obtain ⟨hγ0, hγ2, ht0, ht4, htinf⟩ := hadmInf c hc
  have htle := hτle c hc
  -- the pieces, pointwise in the sample
  set cw : Fin N → Ω → ℝ≥0∞ := fun k ω =>
    cutoffWeightedGmcBallMass P Xc c.1 (c.2.2.1 k) (c.2.1 k) 1 (Real.exp (-r)) ω with hcw
  set MB : Ω → ℝ≥0∞ := fun ω => regularizedGMC P Xc c.1 r ω (closedBall 0 R0) with hMB
  set V : Ω → ℝ≥0∞ := fun ω => ∫⁻ x in {x : ℂ | R0 ≤ ‖x‖},
    ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) ∂regularizedGMC P Xc c.1 r ω with hV
  have hpt : ∀ ω, regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω ≤
      ∑ k, ENNReal.ofReal CR * cw k ω + ENNReal.ofReal CB * MB ω + ENNReal.ofReal CE * V ω := by
    intro ω
    rw [regularizedCoulombMass_eq_lintegral P X hX Xc hXc]
    exact cutoff_weight_integral_le_pieces P Xc c.1 c.2.2.1 c.2.1 c.2.2.2 r ω _
      (measurable_coulombCutoffWeight partition c.1 c.2.2.1 c.2.1 c.2.2.2 r) hρs1
      (fun k x hx hx0 => hCR c.1 c.2.2.1 c.2.1 c.2.2.2 r k x hr (hZc c hc) (hEα c hc)
        (hEinf c hc) (fun j hj => hsep c hc j k hj) hx hx0)
      (fun x hx hxk hx0 => hCB c.1 c.2.2.1 c.2.1 c.2.2.2 r x hr (hZc c hc) (hEα c hc)
        (hEinf c hc) hx hxk hx0)
      (fun x hx => hCE c.1 c.2.2.1 c.2.1 c.2.2.2 r x hr (hZc c hc) (hEα c hc) (hEinf c hc) hx)
  have hcwm : ∀ k, AEMeasurable (cw k) P := fun k =>
    (measurable_cutoffWeightedGmcBallMass P X hX Xc hXc _ _ _ _ _).aemeasurable
  have hMBm : AEMeasurable MB P :=
    ((Measure.measurable_coe Metric.isClosed_closedBall.measurableSet).comp
      (regularizedGMC_measurable P X hX Xc hXc c.1 r)).aemeasurable
  have hEm : MeasurableSet {x : ℂ | R0 ≤ ‖x‖} := measurableSet_le measurable_const measurable_norm
  have hVm' : AEMeasurable V P := by
    have hf : Measurable fun x : ℂ => ENNReal.ofReal (‖x‖ ^ max (c.1 * c.2.2.2) 0) :=
      ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
    have h := (Measure.measurable_lintegral (hf.indicator hEm)).comp
      (regularizedGMC_measurable P X hX Xc hXc c.1 r)
    refine Measurable.aemeasurable ?_
    convert h using 1
    funext ω
    simp only [Function.comp_apply, hV, lintegral_indicator hEm]
  have hmom := lintegral_rpow_le_of_le_pieces
    (fun ω => regularizedCoulombMass P Xc c.1 partition c.2.2.1 c.2.1 c.2.2.2 r ω) cw MB V
    (fun _ => ENNReal.ofReal CR) (ENNReal.ofReal CB) (ENNReal.ofReal CE) hcwm hMBm hVm'
    (Eventually.of_forall hpt) ht0
  refine hmom.trans ?_
  -- bound the moments of the pieces
  have hcwb : ∀ k, ∫⁻ ω, cw k ω ^ τ c ∂P ≤ ENNReal.ofReal (Ck k) := fun k =>
    hCkb k c hc (Real.exp (-r)) (Real.exp_pos _) (Real.exp_le_one_iff.mpr (by linarith))
  have hMBb : ∫⁻ ω, MB ω ^ τ c ∂P ≤ K0 := by
    refine le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow (measure_mono ?_) ht0.le)
      (hdisk c hc (R0 + 1) (by linarith) (by linarith) r hr)
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hVb : ∫⁻ ω, V ω ^ τ c ∂P ≤ Vm := by
    have hK0b : ∀ r' : ℝ, 0 ≤ r' →
        ∫⁻ ω, regularizedGMC P Xc c.1 r' ω (exteriorAnnulus R0 0) ^ τ c ∂P ≤ K0 := by
      intro r' hr'
      refine le_trans (lintegral_mono fun ω => ENNReal.rpow_le_rpow (measure_mono ?_) ht0.le)
        (hdisk c hc (2 * R0 + 1) (by linarith) le_rfl r' hr')
      intro x hx
      rw [Metric.mem_ball, dist_zero_right]
      have := hx.2
      simp only [zero_add, pow_one] at this
      linarith
    refine (cutoff_exterior_power_moment_le P X hX Xc hXc c.1 hR02 (le_max_right _ _) ht0 hK0b
      hr).trans ?_
    have hβ : max (c.1 * c.2.2.2) 0 * τ c ≤ E * tm := by
      have h1 : max (c.1 * c.2.2.2) 0 ≤ E :=
        max_le ((le_abs_self _).trans (hEinf c hc)) hE
      exact mul_le_mul h1 htle ht0.le hE
    refine mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le (by linarith) hβ)) le_rfl) ?_
    exact geometric_factor_le hζ0pos (hζ0b c hc) htle
  have h2 : (2 : ℝ≥0∞) ^ τ c ≤ two :=
    ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) htle
  have hN : (N : ℝ≥0∞) ^ τ c ≤ Nm := ennreal_rpow_le_max_one_rpow _ ht0.le htle
  have hR' : ENNReal.ofReal CR ^ τ c ≤ CRm := ennreal_rpow_le_max_one_rpow _ ht0.le htle
  have hB' : ENNReal.ofReal CB ^ τ c ≤ CBm := ennreal_rpow_le_max_one_rpow _ ht0.le htle
  have hE' : ENNReal.ofReal CE ^ τ c ≤ CEm := ennreal_rpow_le_max_one_rpow _ ht0.le htle
  exact mul_le_mul' h2 (add_le_add (mul_le_mul' h2 (add_le_add (mul_le_mul' hN
    (Finset.sum_le_sum fun k _ => mul_le_mul' hR' (hcwb k))) (mul_le_mul' hB' hMBb)))
    (mul_le_mul' hE' hVb))

end DOZZ.Proofs
