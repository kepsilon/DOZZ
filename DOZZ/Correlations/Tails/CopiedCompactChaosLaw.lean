/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CopiedTestCutoffLaw
public import DOZZ.Correlations.Tails.CopiedWeightTestLimit
public import DOZZ.Correlations.Symmetry.CorrelatedScalarLimit

/-! Equality in law of actual compact chaos masses after the pin copy. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The copied Gaussian pin and the correlated spatial multiplier survive the actual GMC
limit. This is equality in law of compact chaos tests on the given source and product spaces. -/
theorem copied_compact_chaos_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (g : BoundedContinuousFunction ℂ ℝ) (hgc : HasCompactSupport (g : ℂ → ℝ))
    (hg0 : ∀ x, 0 ≤ g x) (hgs : tsupport (g : ℂ → ℝ) ⊆ Metric.ball 0 1) :
    ∃ G : BoundedContinuousFunction ℂ ℝ, HasCompactSupport (G : ℂ → ℝ) ∧
      (∀ y, G y = g (y-z) * Real.exp ((γ^2+4)*Real.log (normPlus y))) ∧
      P.map (fun ω => Real.exp (-γ^2*Real.log ‖z‖) * ∫ y, G y ∂M ω) =
        (P.prod P).map (fun q => Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖) *
          ∫ x, g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0)) ∂N q.1) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨G, hGc, hG⟩ := transferred_compact_test z γ g hgc
  refine ⟨G, hGc, hG, ?_⟩
  obtain ⟨ρ, hρ, hgρ⟩ := compact_test_unit_margin g hgc hgs
  let ρ' := max ρ 0
  have hρ' : ρ' < 1 := max_lt hρ (by norm_num)
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  have hgρ' (x : ℂ) (hx : g x ≠ 0) : ‖x‖ ≤ ρ' := (hgρ x hx).trans (le_max_left _ _)
  have heps : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨L, hL⟩ := eventually_atTop.mp (heps.eventually
    (gt_mem_nhds (show (0 : ℝ) < 1-ρ' by linarith)))
  let t : ℕ → ℕ := fun n => L+n
  have ht : Tendsto t atTop atTop := by
    simpa only [t, Nat.add_comm] using tendsto_add_atTop_nat L
  have hmargin (n : ℕ) : ρ' + Real.exp (-(t n : ℝ)) ≤ 1 := by
    have h := hL (L+n) (Nat.le_add_right L n)
    linarith
  let Uc := fun ω x r => Xc ω (z+x) r-Xc ω z 0
  let S := fun q : Ω × Ω => Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)
  let A : ℕ → Ω → ℝ := fun n ω =>
    Real.exp (-γ^2*Real.log ‖z‖) * ∫ y, G y ∂regularizedGMC P Xc γ (t n) ω
  let B : ℕ → Ω × Ω → ℝ := fun n q => S q *
    ∫ x, g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))
      ∂regularizedGMC P Uc γ (t n) q.1
  let Alim := fun ω => Real.exp (-γ^2*Real.log ‖z‖) * ∫ y, G y ∂M ω
  let Blim := fun q : Ω × Ω => S q *
    ∫ x, g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0)) ∂N q.1
  have hS : Measurable S :=
    (((hc.1 0).comp (measurable_snd.prodMk measurable_const)).const_mul γ).sub_const _ |>.exp
  have hA (n : ℕ) : Measurable (A n) :=
    (DOZZ.Assembly.regularizedGMC_integral_measurable P X hX Xc hc γ (t n) G G.continuous.measurable).const_mul _
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hYc := translated_field_circleAverage P X Xc hX hc z
  have hB (n : ℕ) : Measurable (B n) := by
    have hV : Measurable (fun x : ℂ => ∫ ω, Uc ω x (t n) ^ 2 ∂P) :=
      (((hYc.1 (t n)).comp measurable_swap).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
    have hpin (i : Ω × Ω → Ω) (hi : Measurable i) : Measurable (fun q => Xc (i q) z 0) :=
      (hc.1 0).comp (hi.prodMk measurable_const)
    have hlocal : Measurable (fun q : (Ω × Ω) × ℂ => Uc q.1.1 q.2 (t n)) :=
      (hYc.1 (t n)).comp (measurable_fst.fst.prodMk measurable_snd)
    have hcoef : Measurable (localPinCoefficient z) := by
      unfold localPinCoefficient
      fun_prop
    have hker : Measurable (fun q : (Ω × Ω) × ℂ =>
      (g q.2 * Real.exp (γ*localPinCoefficient z q.2*(Xc q.1.2 z 0-Xc q.1.1 z 0))) *
        Real.exp (γ*Uc q.1.1 q.2 (t n)-γ^2/2*(∫ ω, Uc ω q.2 (t n)^2 ∂P)) *
          normPlus q.2 ^ (-4 : ℝ)) := by
      have h1 : Measurable (fun q : (Ω × Ω) × ℂ => Xc q.1.1 z 0) :=
        (hpin Prod.fst measurable_fst).comp measurable_fst
      have h2 : Measurable (fun q : (Ω × Ω) × ℂ => Xc q.1.2 z 0) :=
        (hpin Prod.snd measurable_snd).comp measurable_fst
      have hn : Measurable (fun q : (Ω × Ω) × ℂ => normPlus q.2 ^ (-4 : ℝ)) := by
        unfold normPlus
        fun_prop
      exact (((g.continuous.measurable.comp measurable_snd).mul
        ((((hcoef.comp measurable_snd).const_mul γ).mul (h2.sub h1)).exp)).mul
          ((hlocal.const_mul γ).sub ((hV.comp measurable_snd).const_mul _)).exp).mul hn
    have heq (q : Ω × Ω) : B n q = S q * ∫ x,
        (g x * Real.exp (γ*localPinCoefficient z x*(Xc q.2 z 0-Xc q.1 z 0))) *
          Real.exp (γ*Uc q.1 x (t n)-γ^2/2*(∫ ω, Uc ω x (t n)^2 ∂P)) *
            normPlus x ^ (-4 : ℝ) ∂volume := by
      dsimp [B]
      rw [regularized_integral_volume P _ Uc hY hYc]
    change Measurable (fun q => B n q)
    simp_rw [heq]
    exact hS.mul hker.stronglyMeasurable.integral_prod_right.measurable
  have hAc : TendstoInMeasure P A atTop Alim :=
    tendstoInMeasure_mul_same_space _ _ _ measurable_const
      ((DOZZ.Assembly.isGMCOf_tendstoInMeasure P X hX Xc hc γ M hM G).comp
        (tendsto_natCast_atTop_atTop.comp ht))
  have hgs' : tsupport (g : ℂ → ℝ) ⊆ Metric.closedBall 0 1 :=
    hgs.trans Metric.ball_subset_closedBall
  have hBc : TendstoInMeasure (P.prod P) B atTop Blim :=
    tendstoInMeasure_mul_same_space _ _ S hS
      ((translated_copied_pin_weight_test_limit P X Xc hX hc γ hγ hγ2 z hz N hN
        g hgc hgs').comp ht)
  have hmaps (n : ℕ) : P.map (A n) = (P.prod P).map (B n) :=
    copied_test_cutoff_law P X Xc hX hc hm z hz γ (t n) ρ' hρ'0 (hmargin n) g G hg0 hgρ' hG
  exact map_eq_of_seq_map_eq_of_tendstoInMeasure A B Alim Blim
    (fun n => (hA n).aemeasurable) (fun n => (hB n).aemeasurable)
      (hAc.aemeasurable (fun n => (hA n).aemeasurable))
      (hBc.aemeasurable (fun n => (hB n).aemeasurable)) hmaps hAc hBc


end DOZZ.Proofs
