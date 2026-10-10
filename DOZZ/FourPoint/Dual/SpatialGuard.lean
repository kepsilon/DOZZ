/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SpatialKernel
public import DOZZ.FourPoint.Dual.OuterInverseGuard
/-! The compact guard used in spatial cutoff removal has actual GMC inverse moments. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- A closed disk about three retains the same lower mass as the fixed exterior open disk. -/
theorem dual_spatial_guard_lower (γ α₁ α₂ α₃ : ℝ) (μ : Measure ℂ)
    (hγ : γ ≠ 0) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ENNReal.ofReal ((2 : ℝ)^(-∑ i : Fin 3, |γ*(![-2/γ, α₁, α₂] : Fin 3 → ℝ) i|)*
      (4 : ℝ)^(-|γ*α₃|))*μ (Metric.ball (3 : ℂ) (1/8)) ≤
      ∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  let D := Metric.closedBall (3 : ℂ) (1/8)
  have hn (y : ℂ) (hy : ‖y‖ ≤ 1) : y ∉ D := by
    intro hd
    have hh := norm_sub_norm_le (3 : ℂ) y
    have hn3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [hn3, norm_sub_rev] at hh
    have hd' : ‖y-3‖ ≤ 1/8 := by simpa only [D, Metric.mem_closedBall, dist_eq_norm] using hd
    linarith
  have ha (y : ℂ) (hy : ‖y‖ ≤ 1) : (μ.restrict D) {y} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton y),
      singleton_inter_of_notMem (hn y hy), measure_empty]
  have he := dual_kernel_integral_eq_coulombMass γ α₁ α₂ α₃ hγ z (μ.restrict D)
    (ha z hz) (ha 0 (by simp)) (ha 1 (by simp))
  have hy : ∀ i : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) i‖ ≤ 1 := by
    intro i
    fin_cases i
    · exact hz
    · simp
    · simp
  have hl := coulombMass_fixed_disk_lower γ (μ.restrict D)
    (![-2/γ, α₁, α₂] : Fin 3 → ℝ) ![z, 0, 1] α₃ hy
  rw [Measure.restrict_apply measurableSet_ball,
    inter_eq_left.mpr Metric.ball_subset_closedBall, ← he] at hl
  exact hl

/-- The compact guard inverse moment is finite for every nonnegative order, uniformly for
moving roots in the unit disk, directly from the ball moment bound. -/
theorem dual_spatial_guard_inverse_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q)
    : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ 1 →
    (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P) ≤ ENNReal.ofReal C := by
  let w : ℝ := (2 : ℝ)^(-∑ i : Fin 3, |γ*(![-2/γ, α₁, α₂] : Fin 3 → ℝ) i|)*
    (4 : ℝ)^(-|γ*α₃|)
  have hw : 0 < w := by dsimp only [w]; positivity
  obtain ⟨C, hC, hb⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hM
    (-q) (lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)) {(3 : ℂ)} isCompact_singleton
  have hball := (hb 3 (Set.mem_singleton _) (1/8) (by norm_num) (by norm_num)).2
  let e := γ*Q γ*(-q)-γ^2*(-q)^2/2
  let Cguard := w^(-q)*(C*(1/8 : ℝ)^e)
  have hCg : 0 < Cguard := by dsimp only [Cguard]; positivity
  refine ⟨Cguard, hCg, ?_⟩
  intro z hz
  have hpoint (ω : Ω) :
      (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ≤
      ENNReal.ofReal (w^(-q))*M ω (Metric.ball (3 : ℂ) (1/8))^(-q) := by
    have hl := dual_spatial_guard_lower γ α₁ α₂ α₃ (M ω) hγ.ne' z hz
    have hanti : (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ≤
        (ENNReal.ofReal w*M ω (Metric.ball (3 : ℂ) (1/8)))^(-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hl hq)
    have hfinite : M ω (Metric.ball (3 : ℂ) (1/8)) ≠ ⊤ := by
      let _ := hM.1 ω
      exact measure_ne_top _ _
    rwa [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hfinite,
      ENNReal.ofReal_rpow_of_pos hw] at hanti
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (w^(-q))*M ω (Metric.ball (3 : ℂ) (1/8))^(-q) ∂P :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (w^(-q))*gmcMassMoment P M (Metric.ball (3 : ℂ) (1/8)) (-q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (w^(-q))*ENNReal.ofReal (C*(1/8 : ℝ)^e) :=
      mul_le_mul' le_rfl hball
    _ = ENNReal.ofReal Cguard := (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm

/-- The compact guard inverse moment is finite for every nonnegative order, uniformly for
moving roots in the unit disk, directly from the ball moment bound. -/
theorem dual_spatial_guard_inverse_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P) < ⊤ := by
  obtain ⟨C, _, hb⟩ := dual_spatial_guard_inverse_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q hq
  exact (hb z hz).trans_lt ENNReal.ofReal_lt_top

end DOZZ.Proofs
