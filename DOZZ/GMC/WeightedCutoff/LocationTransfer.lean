module

public import DOZZ.GMC.SharpMoments.LocationTransfer
public import DOZZ.Statements.GMC.CutoffWeightedGmcBallMass

/-! # Location comparison for weighted cutoff moments -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The distance weight can be clipped outside the integration ball. Consequently the
bounded-weight location comparison applies even when the insertion charge is negative. -/
theorem cutoffWeightedGmcBallMoment_translate_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ α p : ℝ) (z z₀ : ℂ) (ρ R δ : ℝ)
    (hρ : 0 < ρ) (hR : 0 ≤ R) (hz : ‖z‖ + ρ ≤ R)
    (hz₀ : ‖z₀‖ + ρ ≤ R) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ α z ρ δ ω ^ p ∂P) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
        |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
        ∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ α z₀ ρ δ ω ^ p ∂P := by
  let f : ℝ → ℝ≥0 := fun s => ((s + δ) ^ (-γ * α)).toNNReal
  have hf : ContinuousOn f (Set.Icc 0 ρ) := by
    apply continuous_real_toNNReal.comp_continuousOn
    apply ContinuousOn.rpow_const
    · fun_prop
    · intro s hs
      exact Or.inl (ne_of_gt (by linarith [hs.1]))
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hρ.le) hf
  let w : ℂ → ℝ≥0 := fun y => f (min ‖y‖ ρ)
  have hw : Measurable w := by
    dsimp [w, f]
    fun_prop
  have hwb : ∀ y, w y ≤ f s := by
    intro y
    exact hmax ⟨le_min (norm_nonneg _) hρ.le, min_le_right _ _⟩
  have heq (a : ℂ) (ω : Ω) :
      (∫⁻ x in Metric.ball a ρ, (w (x - a) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ (Real.log (1 / δ)) ω) =
      cutoffWeightedGmcBallMass P Xc γ α a ρ δ ω := by
    apply setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro x hx
    have hx' : ‖x - a‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    simp [w, f, min_eq_left hx'.le, ENNReal.ofReal]
  have hr : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [one_div]; exact one_le_inv₀ hδ |>.mpr hδ₁)
  simpa only [heq] using cutoff_translate_moment_le P X hX Xc hXc γ
    (Real.log (1 / δ)) hr z z₀ ρ R hR hz hz₀ w hw (f s) hwb p

end DOZZ.Proofs
