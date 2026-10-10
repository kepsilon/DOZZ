/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.UnpinnedCutoffIdentity
public import DOZZ.Correlations.Tails.UnpinnedGMC

/-! Source-space identification of the translated unpinned chaos, by unique cutoff limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A compact test supported in the open unit disk has a strict radial margin. -/
theorem compact_test_unit_margin (f : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1) :
    ∃ ρ : ℝ, ρ < 1 ∧ ∀ x, f x ≠ 0 → ‖x‖ ≤ ρ := by
  by_cases hne : (tsupport (f : ℂ → ℝ)).Nonempty
  · obtain ⟨x, hx, hmax⟩ := hfc.exists_isMaxOn hne continuous_norm.continuousOn
    refine ⟨‖x‖, ?_, fun y hy => hmax (subset_tsupport _ (Function.mem_support.mpr hy))⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hfU hx
  · refine ⟨0, by norm_num, ?_⟩
    intro x hx
    exact False.elim (hne ⟨x, subset_tsupport _ (Function.mem_support.mpr hx)⟩)

/-- Pin removal identifies the constructed chaos with deterministic tests of the actual GMC.
The two random quantities live on the same source space; independence is not assumed. -/
theorem unpinned_source_test_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (Metric.ball 0 1) (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ N)
    (ρ : ℝ) (hρ : ρ < 1) (f g : BoundedContinuousFunction ℂ ℝ)
    (hfc : HasCompactSupport (f : ℂ → ℝ)) (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1)
    (hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ ρ)
    (hg : ∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) :
    (fun ω => ∫ x, f x ∂N ω) =ᵐ[P]
      fun ω => Real.exp (-γ * Xc ω z 0) * ∫ w, g w ∂M ω := by
  let : IsProbabilityMeasure P := hX.1
  have hT : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have heps : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hT
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (heps.eventually (gt_mem_nhds (show 0 < 1-ρ by linarith)))
  let t : ℕ → ℝ := fun n => ((L+n : ℕ) : ℝ)
  have ht : Tendsto t atTop atTop := by
    simpa only [t, Nat.add_comm, Function.comp_def] using hT.comp (tendsto_add_atTop_nat L)
  have hb n : ρ + Real.exp (-t n) ≤ 1 := by
    have h := hL (L+n) (Nat.le_add_right L n)
    change Real.exp (-t n) < 1-ρ at h
    linarith
  let A : ℕ → Ω → ℝ := fun n ω => ∫ w, g w ∂regularizedGMC P Xc γ (t n) ω
  let W : Ω → ℝ := fun ω => Real.exp (-γ * Xc ω z 0)
  have hA n : AEStronglyMeasurable (A n) P :=
    (DOZZ.Assembly.regularizedGMC_integral_measurable P X hX Xc hc γ (t n)
      g g.continuous.measurable).aestronglyMeasurable
  have hW : AEStronglyMeasurable W P := by
    exact (((hc.1 0).comp (measurable_id.prodMk measurable_const)).const_mul (-γ)).exp.aestronglyMeasurable
  have hAlim : TendstoInMeasure P A atTop (fun ω => ∫ w, g w ∂M ω) :=
    (DOZZ.Assembly.isGMCOf_tendstoInMeasure P X hX Xc hc γ M hM g).comp ht
  have hScaled := tendstoInMeasure_mul_left A (fun ω => ∫ w, g w ∂M ω) W hA hW hAlim
  have hNlim := (hN.2.2.2 f hfc hfU).comp ht
  have hEq n : (fun ω => W ω * A n ω) =ᵐ[P]
      fun ω => regularizedLogChaosTestMass P (Metric.ball 0 1)
        (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ (t n) ω f := by
    exact ae_of_all P fun ω =>
      (unpinned_cutoff_test_identity P X Xc hX hc z hz γ (t n) ρ (hb n) f g hf hg ω).symm
  exact tendstoInMeasure_ae_unique hNlim (hScaled.congr_left hEq)

/-- Every compact test in the unit chart has a genuine deterministic transferred GMC test. -/
theorem unpinned_source_compact_test
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P (Metric.ball 0 1) (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ N)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ Metric.ball 0 1) :
    ∃ g : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (g : ℂ → ℝ) ∧
      (∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w))) ∧
      (fun ω => ∫ x, f x ∂N ω) =ᵐ[P]
        fun ω => Real.exp (-γ * Xc ω z 0) * ∫ w, g w ∂M ω := by
  obtain ⟨ρ, hρ, hf⟩ := compact_test_unit_margin f hfc hfU
  obtain ⟨g, hgc, hg⟩ := transferred_compact_test z γ f hfc
  exact ⟨g, hgc, hg, unpinned_source_test_identity P X Xc hX hc z hz γ M hM N hN
    ρ hρ f g hfc hfU hf hg⟩


end DOZZ.Proofs
