/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorFixedDisk
public import DOZZ.FourPoint.RootedPairIdentity

/-! The one-root annular inverse mass is uniformly controlled by the same fixed supplied-GMC
disk. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Point insertion at any root in the half-unit disk leaves a fixed positive lower density
on the retained disk around 3. The original measure is retained. -/
theorem rooted_fixed_disk_lower (γ : ℝ) (u : ℂ) (hu : ‖u‖ ≤ 1 / 2) (μ : Measure ℂ) :
    ENNReal.ofReal ((5 : ℝ) ^ (-(γ ^ 2))) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
      gmcRootedMeasure γ u μ (Metric.ball (3 : ℂ) (1 / 8)) := by
  have hw (x : ℂ) (hx : x ∈ Metric.ball (3 : ℂ) (1 / 8)) :
      (5 : ℝ) ^ (-(γ ^ 2)) ≤ Real.exp (γ ^ 2 * gffKernel u x) := by
    have hdist : ‖x - 3‖ < 1 / 8 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hn3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    have hlow : 2 < ‖x‖ := by
      have hh := norm_sub_norm_le (3 : ℂ) x
      rw [hn3, norm_sub_rev] at hh
      linarith only [hh, hdist]
    have hupp : ‖x‖ ≤ 4 := by
      have hh := norm_sub_norm_le x (3 : ℂ)
      rw [hn3] at hh
      linarith only [hh, hdist]
    have hdxpos : 0 < ‖u - x‖ := by
      have hh := norm_sub_norm_le x u
      rw [norm_sub_rev] at hh
      linarith only [hh, hlow, hu]
    have hdx5 : ‖u - x‖ ≤ 5 := by
      have hh := norm_sub_le u x
      linarith only [hh, hu, hupp]
    have hlog := Real.log_le_log hdxpos hdx5
    have hlogu : 0 ≤ Real.log (normPlus u) := Real.log_nonneg (le_max_left _ _)
    have hlogx : 0 ≤ Real.log (normPlus x) := Real.log_nonneg (le_max_left _ _)
    have hker : -Real.log 5 ≤ gffKernel u x := by unfold gffKernel; linarith only [hlog, hlogu, hlogx]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 5)]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hker (sq_nonneg γ)
    nlinarith only [hh]
  unfold gmcRootedMeasure
  rw [withDensity_apply _ measurableSet_ball]
  calc
    _ = ∫⁻ x in Metric.ball (3 : ℂ) (1 / 8), ENNReal.ofReal ((5 : ℝ) ^ (-(γ ^ 2))) ∂μ := by simp
    _ ≤ _ := setLIntegral_mono' measurableSet_ball (fun x hx => ENNReal.ofReal_le_ofReal (hw x hx))

/-- A uniform inverse bound for any mass dominating one fixed positive multiple of the disk.
This adapter does not assume the compared random mass itself is a GMC. -/
theorem inverse_fixed_disk_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (w q : ℝ) (hw : 0 < w) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ω → ℝ≥0∞,
      (∀ ω, ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1 / 8)) ≤ I ω) →
        (∫⁻ ω, I ω ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  have hp : -q < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)
  obtain ⟨Cb, hCb, hball⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM
    (-q) hp {(3 : ℂ)} isCompact_singleton
  let ξ : ℝ := γ * Q γ * (-q) - γ ^ 2 * (-q) ^ 2 / 2
  let C : ℝ := w ^ (-q) * (Cb * (1 / 8 : ℝ) ^ ξ)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro I hI
  have hpoint (ω : Ω) : I ω ^ (-q) ≤
      ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) := by
    have hanti : I ω ^ (-q) ≤ (ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1 / 8))) ^ (-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (hI ω) hq)
    have hfinite : M ω (Metric.ball (3 : ℂ) (1 / 8)) ≠ ⊤ := by let _ := hM.1 ω; exact measure_ne_top _ _
    rwa [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hfinite, ENNReal.ofReal_rpow_of_pos hw] at hanti
  have hbound := (hball 3 (Set.mem_singleton _) (1 / 8) (by norm_num) (by norm_num)).2
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) ∂P := lintegral_mono hpoint
    _ = ENNReal.ofReal (w ^ (-q)) * gmcMassMoment P M (Metric.ball (3 : ℂ) (1 / 8)) (-q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (w ^ (-q)) * ENNReal.ofReal (Cb * (1 / 8 : ℝ) ^ ξ) := mul_le_mul' le_rfl hbound
    _ = _ := (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm

/-- The inserted Coulomb inverse moment is bounded uniformly in both the root and the other
bounded insertions. The root family is supplied by the one-root identity. -/
theorem rooted_coulomb_inverse_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {N : ℕ} (α : Fin N → ℝ) (αinf q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℂ, ‖u‖ ≤ 1 / 2 →
      ∀ y : Fin N → ℂ, (∀ i, ‖y i‖ ≤ 1) →
        (∫⁻ ω, (coulombMass γ (gmcRootedMeasure γ u (M ω)) α y αinf) ^ (-q) ∂P) ≤ ENNReal.ofReal C := by
  let w₀ : ℝ := (2 : ℝ) ^ (-∑ i, |γ * α i|) * (4 : ℝ) ^ (-|γ * αinf|)
  let w : ℝ := w₀ * (5 : ℝ) ^ (-(γ ^ 2))
  have hw : 0 < w := by dsimp only [w, w₀]; positivity
  obtain ⟨C, hC, hbound⟩ := inverse_fixed_disk_uniform P X hX γ hγ hγ2 M hM w q hw hq
  refine ⟨C, hC, ?_⟩
  intro u hu y hy
  apply hbound
  intro ω
  have hroot := rooted_fixed_disk_lower γ u hu (M ω)
  have hcoul := coulombMass_fixed_disk_lower γ (gmcRootedMeasure γ u (M ω)) α y αinf hy
  calc
    _ = ENNReal.ofReal w₀ * (ENNReal.ofReal ((5 : ℝ) ^ (-(γ ^ 2))) * M ω (Metric.ball (3 : ℂ) (1 / 8))) := by
      rw [ENNReal.ofReal_mul (by dsimp only [w₀]; positivity)]
      exact mul_assoc _ _ _
    _ ≤ _ := (mul_le_mul' le_rfl hroot).trans hcoul

end DOZZ.Proofs
