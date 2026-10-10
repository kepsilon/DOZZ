/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliUniformCharts
public import DOZZ.FourPoint.RetainedAnnuliClusterLimit

/-! The shared-scale joint inverse bound including the separated disk allocation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Full retained-annuli/fixed-disk bound on arbitrary bounded centers. The common outer
fluctuation acts on `a+b`; the fixed disk receives its independent allocated order `s`.
The constant precedes both scales and the whole permitted spatial geometry. -/
theorem nested_retained_disk_inverse_uniform_orders
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (B R τ σ δ d A : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hR1 : R < 1) (hτ : 0 < τ)
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8)
    (hd : 0 < d) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b s : ℝ), 0 ≤ a → a ≤ A → 0 ≤ b → b ≤ A →
      0 ≤ s → s ≤ A → ∀ (z w : ℂ), ‖z‖ ≤ B → ‖w‖ ≤ B →
      τ + δ + d ≤ ‖z - w‖ → ∀ (c : ℝ), 0 < c → c ≤ 1 → c * R ≤ τ →
      ∀ (u v : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 8 →
        ‖u‖ + ρ ≤ R → ‖v‖ + σ ≤ R → ρ + σ + d ≤ ‖u - v‖ →
        (∫⁻ ω, (M ω (Metric.ball (z + c • u) (c * ρ))) ^ (-a) *
          (M ω (Metric.ball (z + c • v) (c * σ))) ^ (-b) *
          (M ω (Metric.ball w δ)) ^ (-s) ∂P) ≤
          ENNReal.ofReal (C * c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
            ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  obtain ⟨C₀, hC₀, hnested⟩ := nested_retained_inverse_uniform_bounded_centers
    P X hX γ hγ hγ2 M hM B R σ d A hB hR hR1 hσ hσ8 hd hA
  obtain ⟨CD, hCD, hD⟩ := ball_inverse_moment_uniform_orders
    P X hX γ hγ hγ2 M hM B A hB hA
  let L : ℝ := B + τ + δ
  let k : ℝ := Real.exp (γ ^ 2 * max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 *
    ((3 * A) ^ 2 + 3 * A))
  let D : ℝ := CD * δ ^ (γ * Q γ * (-A) - γ ^ 2 * A ^ 2 / 2)
  have hk : 0 < k := Real.exp_pos _
  have hDpos : 0 < D := by dsimp only [D]; positivity
  let C : ℝ := k * C₀ * D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a b s ha haA hb hbA hs hsA z w hz hw hsep c hc hc1 hcR u v ρ hρ hρ8 hu hv hsep'
  have hsub (x : ℂ) (r : ℝ) (hx : ‖x‖ + r ≤ R) :
      Metric.ball (z + c • x) (c * r) ⊆ Metric.ball z τ := by
    intro y hy
    have hyn : ‖y - (z + c • x)‖ < c * r := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have he : y - z = (y - (z + c • x)) + c • x := by abel
    have hn := norm_add_le (y - (z + c • x)) (c • x)
    rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hn
    have hh := mul_le_mul_of_nonneg_left hx hc.le
    change dist y z < τ
    rw [dist_eq_norm]
    linarith only [hyn, hn, hh, hcR]
  have hcluster := retained_cluster_disk_inverse_bound P X hX γ hγ hγ2 M hM
    z w (z + c • u) (z + c • v) τ δ (c * ρ) (c * σ) L d a b s
    (by dsimp only [L]; positivity) hd
    (by dsimp only [L]; linarith only [hz, hδ])
    (by dsimp only [L]; linarith only [hw, hτ]) hsep
    (by positivity) (by positivity) hδ ((mul_le_of_le_one_left hρ.le hc1).trans hρ8)
    ((mul_le_of_le_one_left hσ.le hc1).trans hσ8) hδ8 (hsub u ρ hu) (hsub v σ hv) ha hb hs
  have hn := hnested a b ha haA hb hbA z hz c hc hc1 u v ρ hρ hρ8 hu hv hsep'
  have hD' := hD s hs hsA w hw δ hδ hδ8
  have hDmax : gmcMassMoment P M (Metric.ball w δ) (-s) ≤ ENNReal.ofReal D := by
    refine hD'.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hCD.le
    exact Real.rpow_le_rpow_of_exponent_ge hδ (hδ8.trans (by norm_num))
      (inverse_scale_exponent_antitone γ s A hγ hs hsA)
  have hcost := inverse_gaussian_bill_mono γ
    (max 0 (Real.log (1 / d) + gmcCircleChartRemainder L)) (a + b + s) (3 * A)
    (le_max_left _ _) (by positivity) (by linarith only [haA, hbA, hsA])
  simp only [add_assoc] at hcluster hcost
  have hh := hcluster.trans (mul_le_mul' (mul_le_mul' hcost hn) hDmax)
  change _ ≤ ENNReal.ofReal k *
    ENNReal.ofReal (C₀ * c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
      ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) * ENNReal.ofReal D at hh
  refine hh.trans_eq ?_
  rw [← ENNReal.ofReal_mul hk.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [C, D]
  ring

end DOZZ.Proofs
