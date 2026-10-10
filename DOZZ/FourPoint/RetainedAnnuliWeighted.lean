/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliUniformCluster
public import DOZZ.FourPoint.RetainedAnnuliTripleAllocation

/-! Weighted lower masses consume the full joint nested GMC estimate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A supplied random mass dominating two weighted nested disks and a weighted fixed disk
inherits the exact shared-scale inverse bound. This adapter retains the three actual orders
and places the constant before all orders, spatial parameters, and deterministic weights. -/
theorem weighted_nested_retained_inverse_bound
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
        ∀ (I : Ω → ℝ≥0∞) (wA wB wD : ℝ), 0 < wA → 0 < wB → 0 < wD →
          (∀ ω, ENNReal.ofReal wA * M ω (Metric.ball (z + c • u) (c * ρ)) ≤ I ω) →
          (∀ ω, ENNReal.ofReal wB * M ω (Metric.ball (z + c • v) (c * σ)) ≤ I ω) →
          (∀ ω, ENNReal.ofReal wD * M ω (Metric.ball w δ) ≤ I ω) →
          (∫⁻ ω, I ω ^ (-(a + b + s)) ∂P) ≤
            ENNReal.ofReal (C * (wA ^ (-a) * wB ^ (-b) * wD ^ (-s)) *
              c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
              ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  obtain ⟨C, hC, hbound⟩ := nested_retained_disk_inverse_uniform_orders
    P X hX γ hγ hγ2 M hM B R τ σ δ d A hB hR hR1 hτ hσ hσ8 hδ hδ8 hd hA
  refine ⟨C, hC, ?_⟩
  intro a b s ha haA hb hbA hs hsA z w hz hw hsep c hc hc1 hcR u v ρ hρ hρ8 hu hv hsep'
    I wA wB wD hwA hwB hwD hlA hlB hlD
  have hfinite (ω : Ω) (U : Set ℂ) : M ω U ≠ ⊤ := by
    let _ := hM.1 ω
    exact measure_ne_top _ _
  have halloc := three_retained_moment_allocation P I
    (fun ω => M ω (Metric.ball (z + c • u) (c * ρ)))
    (fun ω => M ω (Metric.ball (z + c • v) (c * σ))) (fun ω => M ω (Metric.ball w δ))
    (fun ω => hfinite ω _) (fun ω => hfinite ω _) (fun ω => hfinite ω _)
    wA wB wD a b s hwA hwB hwD ha hb hs hlA hlB hlD
  have hh := halloc.trans (mul_le_mul' le_rfl
    (hbound a b s ha haA hb hbA hs hsA z w hz hw hsep c hc hc1 hcR u v ρ hρ hρ8 hu hv hsep'))
  refine hh.trans_eq ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end DOZZ.Proofs
