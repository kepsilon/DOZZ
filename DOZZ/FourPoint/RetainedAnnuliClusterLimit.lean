/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliClusterCutoff
public import DOZZ.FourPoint.RetainedAnnuliTripleFatou
public import DOZZ.FourPoint.RetainedAnnuliMomentConvergence
public import DOZZ.GMC.BallAnnulus.Ball

/-! The cluster/fixed-disk comparison on the actual limiting GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A fixed disk separates from the whole cluster. The joint inverse moment of the two
cluster masses is preserved; it can be supplied by the nested retained-annulus estimate. -/
theorem retained_cluster_disk_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z w u v : ℂ) (τ δ ρ σ L d a b s : ℝ)
    (hL : 0 ≤ L) (hd : 0 < d) (hz : ‖z‖ + τ ≤ L) (hw : ‖w‖ + δ ≤ L)
    (hsep : τ + δ + d ≤ ‖z - w‖)
    (hρ : 0 < ρ) (hσ : 0 < σ) (hδ : 0 < δ)
    (hρ8 : ρ ≤ 1 / 8) (hσ8 : σ ≤ 1 / 8) (hδ8 : δ ≤ 1 / 8)
    (hu : Metric.ball u ρ ⊆ Metric.ball z τ) (hv : Metric.ball v σ ⊆ Metric.ball z τ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 ≤ s) :
    (∫⁻ ω, (M ω (Metric.ball u ρ)) ^ (-a) * (M ω (Metric.ball v σ)) ^ (-b) *
      (M ω (Metric.ball w δ)) ^ (-s) ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 *
        max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 *
          ((a + b + s) ^ 2 + a + b + s))) *
        (∫⁻ ω, (M ω (Metric.ball u ρ)) ^ (-a) * (M ω (Metric.ball v σ)) ^ (-b) ∂P) *
          gmcMassMoment P M (Metric.ball w δ) (-s) := by
  have : IsProbabilityMeasure P := hX.1
  obtain ⟨Xc, hXc, -⟩ := hM.2
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 *
    max 0 (Real.log (1 / d) + gmcCircleChartRemainder L) / 2 *
      ((a + b + s) ^ 2 + a + b + s)))
  let f (c : ℂ) (r : ℝ) : ℕ → Ω → ℝ :=
    fun n ω => (regularizedGMC P Xc γ n ω (Metric.ball c r)).toReal
  let g (c : ℂ) (r : ℝ) : Ω → ℝ := fun ω => (M ω (Metric.ball c r)).toReal
  let Rn : ℕ → ℝ≥0∞ := fun n => K *
    (∫⁻ ω, (regularizedGMC P Xc γ n ω (Metric.ball u ρ)) ^ (-a) *
      (regularizedGMC P Xc γ n ω (Metric.ball v σ)) ^ (-b) ∂P) *
        gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball w δ) (-s)
  have hcrit : -s < 4 / γ ^ 2 := (neg_nonpos.mpr hs).trans_lt
    (div_pos (by norm_num) (sq_pos_of_pos hγ))
  have hDfin := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM w δ hδ hδ8 (-s) hcrit
  have hDpos := gmc_finite_measure_nonpositive_moment_pos P M hM.1 (Metric.ball w δ)
    (gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM _
      Metric.isOpen_ball.measurableSet) (-s) (neg_nonpos.mpr hs)
  have hJ := ENNReal.Tendsto.const_mul (a := K)
    (gmc_joint_ball_inverse_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc
      u v ρ σ a b hρ hσ hρ8 hσ8 ha hb) (Or.inr ENNReal.ofReal_ne_top)
  have hD := gmc_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc w δ hδ hδ8 (-s) hcrit
  have hRn : Tendsto Rn atTop (nhds (K *
      (∫⁻ ω, (M ω (Metric.ball u ρ)) ^ (-a) * (M ω (Metric.ball v σ)) ^ (-b) ∂P) *
        gmcMassMoment P M (Metric.ball w δ) (-s))) :=
    ENNReal.Tendsto.mul hJ (Or.inr hDfin.ne) hD (Or.inl hDpos.ne')
  have hconv (c : ℂ) (r : ℝ) : TendstoInMeasure P (f c r) atTop (g c r) :=
    regularizedGMC_mass_toReal_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc _
      Metric.isOpen_ball.measurableSet _ (ball_subset_closedBall_norm_add c r)
  have hm (c : ℂ) (r : ℝ) (n : ℕ) : Measurable (fun ω => ENNReal.ofReal (f c r n ω)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_regularizedGMC_apply_toReal P X hX Xc hXc γ n _ Metric.isOpen_ball.measurableSet)
  have hmeas (n : ℕ) : AEMeasurable (fun ω =>
      ENNReal.ofReal (f u ρ n ω) ^ (-a) * ENNReal.ofReal (f v σ n ω) ^ (-b) *
        ENNReal.ofReal (f w δ n ω) ^ (-s)) P :=
    (((hm u ρ n).pow_const _).mul ((hm v σ n).pow_const _)).aemeasurable.mul
      ((hm w δ n).pow_const _).aemeasurable
  have hpositive (c : ℂ) (r : ℝ) (hr : 0 < r) : ∀ᵐ ω ∂P, 0 < g c r ω := by
    filter_upwards [gmc_ball_mass_pos_ae P X hX γ hγ hγ2 M hM c r hr] with ω hω
    let _ := hM.1 ω
    exact ENNReal.toReal_pos hω.ne' (measure_ne_top _ _)
  have he (n : ℕ) : (fun ω => ENNReal.ofReal (f u ρ n ω) ^ (-a) *
      ENNReal.ofReal (f v σ n ω) ^ (-b) * ENNReal.ofReal (f w δ n ω) ^ (-s)) =ᵐ[P]
        fun ω => (regularizedGMC P Xc γ n ω (Metric.ball u ρ)) ^ (-a) *
          (regularizedGMC P Xc γ n ω (Metric.ball v σ)) ^ (-b) *
          (regularizedGMC P Xc γ n ω (Metric.ball w δ)) ^ (-s) := by
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hω
    let _ := hω
    dsimp only [f]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hbound (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (f u ρ n ω) ^ (-a) *
      ENNReal.ofReal (f v σ n ω) ^ (-b) * ENNReal.ofReal (f w δ n ω) ^ (-s) ∂P) ≤ Rn n := by
    rw [lintegral_congr_ae (he n)]
    exact retained_cluster_disk_cutoff_inverse_bound P X hX Xc hXc γ n
      (Nat.cast_nonneg n) z w u v τ δ ρ σ L d a b s hL hd hz hw hsep hu hv ha hb hs
  have hfatou := three_mass_fatou P (f u ρ) (f v σ) (f w δ) (g u ρ) (g v σ) (g w δ)
    (-a) (-b) (-s) (hconv u ρ) (hconv v σ) (hconv w δ) hmeas
    (hpositive u ρ hρ) (hpositive v σ hσ) (hpositive w δ hδ) Rn _ hRn hbound
  have hlimit : (fun ω => ENNReal.ofReal (g u ρ ω) ^ (-a) *
      ENNReal.ofReal (g v σ ω) ^ (-b) * ENNReal.ofReal (g w δ ω) ^ (-s)) =
        fun ω => (M ω (Metric.ball u ρ)) ^ (-a) * (M ω (Metric.ball v σ)) ^ (-b) *
          (M ω (Metric.ball w δ)) ^ (-s) := by
    funext ω
    let _ := hM.1 ω
    dsimp only [g]
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hlimit] at hfatou
  exact hfatou

end DOZZ.Proofs
