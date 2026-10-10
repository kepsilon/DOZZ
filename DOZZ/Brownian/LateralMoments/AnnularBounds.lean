/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LateralMoments.ChargeComparison
public import DOZZ.Brownian.LateralMoments.CutoffBounds
public import DOZZ.Brownian.Lateral.AnnularComparison

/-! Uniform planar annular moments for source witnesses at bounded charges. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Every logarithmic annulus of positive width retains a fixed small open disk. -/
theorem latmom_annulus_retains_ball (a b : ℝ) (hab : a < b) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/8 ∧ Metric.ball c ρ ⊆ lateralLogAnnulus a b := by
  let u := Real.exp (-((a+b)/2))
  have hu : 0 < u := Real.exp_pos _
  have hlo : Real.exp (-b) < u := Real.exp_lt_exp.mpr (by linarith only [hab])
  have hhi : u < Real.exp (-a) := Real.exp_lt_exp.mpr (by linarith only [hab])
  let U : Set ℂ := {x | Real.exp (-b) < ‖x‖ ∧ ‖x‖ < Real.exp (-a)}
  have hU : IsOpen U := (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)
  have huU : (u : ℂ) ∈ U := by
    change Real.exp (-b) < ‖(u : ℂ)‖ ∧ ‖(u : ℂ)‖ < Real.exp (-a)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    exact ⟨hlo, hhi⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU (u : ℂ) huU
  refine ⟨u, min r (1/8), lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  intro x hx
  have hxU := hball ((Metric.ball_subset_ball (min_le_left _ _)) hx)
  exact (mem_lateralLogAnnulus_iff a b x).mpr ⟨hxU.1.le, hxU.2⟩

/-- One fixed source field at the maximal charge controls convex moments of every source
planar annulus in the smaller charge range. The bounds pass through the actual GMC limit. -/
theorem latmom_annular_uniform_convex_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X₀ : Ω → Distr) (hX₀ : IsEquatorGFF P X₀)
    (Xc₀ : Ω → ℂ → ℝ → ℝ) (hXc₀ : IsCircleAverage P X₀ Xc₀)
    (g : ℝ) (hg : 0 < g) (hg2 : g < 2)
    (Kγ : Set ℝ) (hγbound : ∀ γ ∈ Kγ, 0 < γ ∧ γ ≤ g)
    (p : ℝ) (hp : p ≤ 0 ∨ 1 ≤ p) (hcrit : p < 4 / g ^ 2)
    (a b : ℝ) (hab : a < b) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ X M,
      IsEquatorGFF P X → IsGMCOf P X γ M →
      (∫⁻ ω, ENNReal.rpow (M ω (lateralLogAnnulus a b)) p ∂P) ≤ C := by
  let O := lateralLogAnnulus a b
  let R := Real.exp (-a)
  have hR : 0 ≤ R := (Real.exp_pos _).le
  have hOR : O ⊆ Metric.closedBall (0 : ℂ) R :=
    (lateralLogAnnulus_subset_ball a b).trans Metric.ball_subset_closedBall
  have hO : Bornology.IsBounded O := Metric.isBounded_closedBall.subset hOR
  obtain ⟨c, ρ, hρ, hρ8, hball⟩ := latmom_annulus_retains_ball a b hab
  obtain ⟨C₀, hC₀, hbound⟩ := latmom_cutoff_bounded_moment_uniform
    P X₀ hX₀ Xc₀ hXc₀ g hg hg2 O hO c ρ hρ hρ8 hball p hcrit
  let T := ENNReal.ofReal (Real.exp
    (g ^ 2 * (Real.log (2*R+1) + gmcCircleChartRemainder R) / 2 * (p ^ 2-p)))
  refine ⟨T*C₀, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC₀, ?_⟩
  intro γ hγ X M hX hM
  obtain ⟨Xc, hXc, _⟩ := hM.2
  have hγp := (hγbound γ hγ).1
  have hγg := (hγbound γ hγ).2
  have hγ2 := hγg.trans_lt hg2
  have hfinal := gmcMassMoment_le_of_cutoff_uniform P X hX γ hγp hγ2 M hM Xc hXc
    O (measurableSet_lateralLogAnnulus a b) R hOR p (T*C₀) (fun r hr => by
      have hdom := latmom_cutoff_charge_domination P X X₀ hX hX₀ Xc Xc₀ hXc hXc₀
        γ g hγp hγg O (measurableSet_lateralLogAnnulus a b) R hR
        (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hOR hx)
        p hp r hr
      exact hdom.trans (mul_le_mul_of_nonneg_left (hbound r hr) (by positivity)))
  exact hfinal

end DOZZ.Proofs
end
