/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.LateralCutoffCovariance
public import DOZZ.FourPoint.Reflected.DecouplingComparison
import Mathlib.Tactic
/-! # Comparison of the actual lateral circle field on separated compact regions -/
public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Classical
namespace DOZZ.Proofs

/-- On compact separated inner and outer charts the literal finite-circle lateral fields obey
both negative-moment comparisons, with covariance bound `2R+eta`. The weight is arbitrary and
can therefore be fixed after conditioning on a radial path. -/
theorem reflected_lateral_compact_decoupling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (ρ : ℝ) (hρ : 0 < ρ) (K : Set ℂ) (hK : IsCompact K)
    (hKU : K ⊆ originLateralChart ρ) (A : Set ℂ) (hA : MeasurableSet A)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1 / 2) (hr : 0 < r) (hη : 0 < η)
    (hinner : ∀ x ∈ K, x ∈ A → ‖x‖ ≤ R * r)
    (houter : ∀ x ∈ K, x ∉ A → r ≤ ‖x‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ ε, 0 < ε → ε ≤ min d ρ →
      ∀ (ν : Measure K) [IsFiniteMeasure ν] (h : K → ℝ≥0), Measurable h →
      (∃ b : ℝ≥0, ∀ x, h x ≤ b) → ∀ (γ q : ℝ), 0 ≤ q →
      let Φ := fun ω (x : K) => originLateralCircleRegularization Xc ρ ω ε x
      let B : Set K := Subtype.val ⁻¹' A
      let m := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * R + η) / 2 * (q ^ 2 + q)))
      (∫⁻ ω, fieldChaosMass P Φ ν h γ ω ^ (-q) ∂P) ≤
        m * (∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ B) ν h γ ω ^ (-q)
          ∂P.prod P) ∧
      (∫⁻ ω, fieldChaosMass (P.prod P) (reflected_decoupled_field Φ B) ν h γ ω ^ (-q)
          ∂P.prod P) ≤ m * (∫⁻ ω, fieldChaosMass P Φ ν h γ ω ^ (-q) ∂P) := by
  let s := (1 - R) * r
  have hs : 0 < s := mul_pos (by linarith only [hR]) hr
  obtain ⟨d, hd, hb⟩ := reflected_lateral_cutoff_cross_bound P X Xc hX hc hm
    ρ hρ K hK hKU R s η hR hs hη
  refine ⟨d, hd, ?_⟩
  intro ε hε hεδ ν _ h hh hhb γ q hq
  let Φ := fun ω (x : K) => originLateralCircleRegularization Xc ρ ω ε x
  let B : Set K := Subtype.val ⁻¹' A
  have hΦ : IsCenteredGaussianField P Φ := by
    constructor
    · exact (originLateralCircleRegularization_measurableAtScale Xc hm ρ hρ ε).comp
        (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
    · intro n x
      exact originLateralCircleRegularization_gaussian P X Xc hX hc hm ρ hρ n
        (fun i => (ε, (x i).val))
  have ho (x y : K) (hx : x.val ∉ A) (hy : y.val ∈ A) :
      |gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y)| ≤ 2 * R + η := by
    have hxo := houter x.val x.property hx
    have hyi := hinner y.val y.property hy
    have hrel : ‖y.val‖ ≤ R * ‖x.val‖ :=
      hyi.trans (mul_le_mul_of_nonneg_left hxo hR0)
    have hdist : s ≤ ‖x.val - y.val‖ := by
      have ht := norm_sub_norm_le x.val y.val
      have hg : ‖x.val‖ - ‖y.val‖ ≥ (1 - R) * r := by
        linarith only [hxo, hyi]
      exact hg.trans ht
    exact hb ε ε hε hεδ hε hεδ x.val x.property y.val y.property hdist hrel
  have hbill : 0 ≤ 2 * R + η := by linarith only [hR0, hη]
  have hcross (x y : K) (hne : ¬(x ∈ B ↔ y ∈ B)) :
      |gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y)| ≤
        (Real.sqrt (2 * R + η)) ^ 2 := by
    rw [Real.sq_sqrt hbill]
    by_cases hx : x.val ∈ A
    · have hy : y.val ∉ A := fun hy => hne ⟨fun _ => hy, fun _ => hx⟩
      have hs : gaussianCovariance P (fun ω => Φ ω x) (fun ω => Φ ω y) =
          gaussianCovariance P (fun ω => Φ ω y) (fun ω => Φ ω x) := by
        unfold gaussianCovariance
        simp only [mul_comm]
      rw [hs]
      exact ho y x hy hx
    · have hy : y.val ∈ A := by
        by_contra hy
        exact hne ⟨fun h => (hx h).elim, fun h => (hy h).elim⟩
      exact ho x y hx hy
  have ht := reflected_kahane_decoupling P Φ hΦ B
    (hA.preimage measurable_subtype_coe) ν h hh hhb γ q (Real.sqrt (2 * R + η)) hq hcross
  have he : (-q) ^ 2 - (-q) = q ^ 2 + q := by ring
  simpa only [Real.sq_sqrt hbill, he] using ht

end DOZZ.Proofs
