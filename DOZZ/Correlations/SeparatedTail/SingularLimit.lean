/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.WeightedLimit
public import DOZZ.Correlations.SeparatedTail.DirichletMoment

/-! Two bounded softened weights, followed by monotone removal of the two root cutoffs. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Fixed softening permits the ordinary bounded-test GMC convergence. At small cutoffs,
the softened weights are dominated by the literal cutoff singular weights. -/
theorem separatedTail_softened_mixed_moment_le_of_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z2 z3 : ℂ) (α2 α3 : ℝ) (hα2 : 0 ≤ α2) (hα3 : 0 ≤ α3)
    (a2 a3 : ℝ) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3) (C : ℝ≥0∞)
    (hbound : ∀ δ : ℝ, 0 < δ → δ < 1/4 →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ α2 z2 1 δ ω ^ a2 *
        cutoffWeightedGmcBallMass P Xc γ α3 z3 1 δ ω ^ a3 ∂P) ≤ C)
    (s : ℝ) (hs : 0 < s) :
    (∫⁻ ω, (∫⁻ x in ball z2 1, ENNReal.ofReal ((‖x-z2‖+s)^(-γ*α2)) ∂M ω)^a2 *
      (∫⁻ x in ball z3 1, ENNReal.ofReal ((‖x-z3‖+s)^(-γ*α3)) ∂M ω)^a3 ∂P) ≤ C := by
  have he2 : -γ*α2 ≤ 0 := by nlinarith
  have he3 : -γ*α3 ≤ 0 := by nlinarith
  obtain ⟨n₀, hn₀⟩ := limitWeightedFatou_exists_nat_exp_neg_le (lt_min hs (by norm_num : (0:ℝ)<1/8))
  refine separatedTail_bounded_weight_mixed_moment_limit_le P X hX γ hγ hγ2 M hM Xc hXc z2 z3
    (fun y => ((‖y‖+s)^(-γ*α2)).toNNReal) (fun y => ((‖y‖+s)^(-γ*α3)).toNNReal)
    (limitWeightedFatou_weight_measurable _ _) (limitWeightedFatou_weight_measurable _ _)
    ((s^(-γ*α2)).toNNReal) ((s^(-γ*α3)).toNNReal)
    (limitWeightedFatou_weight_le he2 hs) (limitWeightedFatou_weight_le he3 hs)
    a2 a3 ha2 ha3 C n₀ ?_
  intro n hn
  have hδ : 0 < Real.exp (-(n : ℝ)) := Real.exp_pos _
  have hδs : Real.exp (-(n : ℝ)) ≤ s := (hn₀ n hn).trans (min_le_left _ _)
  have hδ4 : Real.exp (-(n : ℝ)) < 1/4 := lt_of_le_of_lt
    ((hn₀ n hn).trans (min_le_right _ _)) (by norm_num)
  have hlog : Real.log (1/Real.exp (-(n : ℝ))) = (n : ℝ) := by
    rw [one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
  apply le_trans (lintegral_mono fun ω => mul_le_mul'
    (ENNReal.rpow_le_rpow (lintegral_mono fun x =>
      limitWeightedFatou_ofReal_rpow_le (norm_nonneg _) hδ hδs he2) ha2)
    (ENNReal.rpow_le_rpow (lintegral_mono fun x =>
      limitWeightedFatou_ofReal_rpow_le (norm_nonneg _) hδ hδs he3) ha3))
  simpa only [cutoffWeightedGmcBallMass, hlog] using hbound _ hδ hδ4

/-- Removing both root softenings preserves the mixed moment bound. The finite positive
marginal moments come from the GMC moment range
`DOZZ.equatorGFF_GMC_weighted_local_moment_range`; no limiting independence is asserted. -/
theorem separatedTail_singular_mixed_moment_le_of_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z2 z3 : ℂ) (α2 α3 : ℝ) (hα2 : 0 ≤ α2) (hα3 : 0 ≤ α3)
    (a2 a3 : ℝ) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hf2 : ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) α2 z2 1 ≠ ⊤)
    (hf3 : ∀ᵐ ω ∂P, weightedGmcBallMass γ (M ω) α3 z3 1 ≠ ⊤)
    (C : ℝ≥0∞)
    (hbound : ∀ δ : ℝ, 0 < δ → δ < 1/4 →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ α2 z2 1 δ ω ^ a2 *
        cutoffWeightedGmcBallMass P Xc γ α3 z3 1 δ ω ^ a3 ∂P) ≤ C) :
    (∫⁻ ω, weightedGmcBallMass γ (M ω) α2 z2 1 ^ a2 *
      weightedGmcBallMass γ (M ω) α3 z3 1 ^ a3 ∂P) ≤ C := by
  let s : ℕ → ℝ := fun n => 1/((n : ℝ)+1)
  have hs : ∀ n, 0 < s n := fun n => by dsimp [s]; positivity
  have hsanti : Antitone s := fun n m hnm =>
    one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    (∫⁻ x in ball z2 1, ENNReal.ofReal ((‖x-z2‖+s n)^(-γ*α2)) ∂M ω)^a2 *
    (∫⁻ x in ball z3 1, ENNReal.ofReal ((‖x-z3‖+s n)^(-γ*α3)) ∂M ω)^a3
  have hm (n : ℕ) : AEMeasurable (f n) P :=
    ((gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (limitWeightedFatou_ofReal_weight_measurable z2 _ _) _ isOpen_ball.measurableSet).pow_const a2).mul
    ((gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _
      (limitWeightedFatou_ofReal_weight_measurable z3 _ _) _ isOpen_ball.measurableSet).pow_const a3)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop
      (𝓝 (weightedGmcBallMass γ (M ω) α2 z2 1 ^ a2 * weightedGmcBallMass γ (M ω) α3 z3 1 ^ a3)) := by
    filter_upwards [hf2,hf3] with ω h2 h3
    have ht2 := (limitWeightedFatou_mass_tendsto (M ω) γ α2 hγ hα2 z2 1 hs hsanti hs0).ennrpow_const a2
    have ht3 := (limitWeightedFatou_mass_tendsto (M ω) γ α3 hγ hα3 z3 1 hs hsanti hs0).ennrpow_const a3
    exact ENNReal.Tendsto.mul ht2 (Or.inr (ENNReal.rpow_ne_top_of_nonneg ha3 h3)) ht3
      (Or.inr (ENNReal.rpow_ne_top_of_nonneg ha2 h2))
  calc
    _ = ∫⁻ ω, liminf (fun n => f n ω) atTop ∂P :=
      lintegral_congr_ae (hlim.mono fun ω hω => hω.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ ω, f n ω ∂P) atTop := lintegral_liminf_le' hm
    _ ≤ limsup (fun n => ∫⁻ ω, f n ω ∂P) atTop := liminf_le_limsup
    _ ≤ C := limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n =>
      separatedTail_softened_mixed_moment_le_of_cutoff P X hX γ hγ hγ2 M hM Xc hXc z2 z3 α2 α3
        hα2 hα3 a2 a3 ha2 ha3 C hbound (s n) (hs n))

end DOZZ.Proofs
