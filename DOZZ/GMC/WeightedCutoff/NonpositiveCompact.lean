module

public import DOZZ.GMC.WeightedCutoff.RootUniform
public import DOZZ.GMC.Moments.WeightedCutoffSubunit

/-! # Uniform weighted cutoff estimates at nonpositive charges -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem cutoffWeightedGmcBallMoment_nonpos_compact_gamma_chart
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓpos : ∀ γ ∈ Γ, 0 < γ)
    (T : Set (ℝ × ℝ)) (hT : IsCompact T) (horders : ∀ t ∈ T, 1 ≤ t.2)
    (q : ℝ) (hq : 1 < q) (hcrit : ∀ γ ∈ Γ, q < 4 / γ ^ 2)
    (hordersBound : ∀ t ∈ T, t.2 ≤ q) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Γ, ∀ t ∈ T, t.1 ≤ 0 →
      ∀ z : ℂ, ∀ R : ℝ, 0 < R → R ≤ 1 / 2 → ‖z‖ + 2 * R ≤ 1 →
      ∀ δ : ℝ, 0 < δ → δ ≤ R →
      (∫⁻ ω, cutoffWeightedGmcBallMass P Xc γ t.1 z R δ ω ^ t.2 ∂P) ≤
        C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
  classical
  rcases Set.eq_empty_or_nonempty (Γ ×ˢ T) with hEmpty | hNonempty
  · refine ⟨0, by simp, ?_⟩
    intro γ hγ t ht
    have : (γ, t) ∈ Γ ×ˢ T := ⟨hγ, ht⟩
    simp [hEmpty] at this
  obtain ⟨A, hA, hroot⟩ := regularizedGMC_openBall_root_bound_compact_gamma_chart
    P X hX Xc hXc Γ hΓ hΓpos q hq hcrit
  let B : ℝ≥0∞ := max 1 A
  have hB : B < ⊤ := max_lt_iff.mpr ⟨ENNReal.one_lt_top, hA⟩
  have hBone : 1 ≤ B := le_max_left _ _
  let beta : ℝ × (ℝ × ℝ) → ℝ := fun u =>
    2 * u.2.2 + u.1 ^ 2 * u.2.2 / 2 - u.1 ^ 2 * u.2.2 ^ 2 / 2
  let coeff : ℝ × (ℝ × ℝ) → ℝ := fun u =>
    (2 : ℝ) ^ (-u.1 * u.2.1 * u.2.2) * (1 / 8 : ℝ) ^ (-beta u)
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have heighth : (1 / 8 : ℝ) ≠ 0 := by norm_num
  have hcoeff : Continuous coeff := by dsimp [coeff, beta]; fun_prop
  obtain ⟨umax, humax, hmax⟩ := (hΓ.prod hT).exists_isMaxOn hNonempty hcoeff.continuousOn
  let C : ℝ≥0∞ := ENNReal.ofReal (coeff umax) * B ^ q
  have hC : C < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg (by linarith) hB.ne))
  refine ⟨C, hC, ?_⟩
  intro γ hγ t ht hα z R hR hRhalf hchart δ hδ hδR
  have hp : 1 ≤ t.2 := horders t ht
  have hp0 : 0 < t.2 := lt_of_lt_of_le zero_lt_one hp
  have hγpos := hΓpos γ hγ
  have hmoment : (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ t.2 ∂P) ≤
      B ^ q * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta (γ, t)) := by
    have hr := (hroot γ hγ t.2 hp (hordersBound t ht) z R δ hR hRhalf hδ hδR hchart).1
    have hm : (∫⁻ ω, (regularizedGMC P Xc γ (Real.log (1 / δ)) ω (Metric.ball z R)) ^ t.2 ∂P) ≤
        (A * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ (beta (γ, t) / t.2))) ^ t.2 := by
      apply (ENNReal.rpow_inv_le_iff hp0).mp
      simpa only [one_div, beta] using hr
    have hAp : A ^ t.2 ≤ B ^ q := (ENNReal.rpow_le_rpow (le_max_right 1 A) hp0.le).trans
      (ENNReal.rpow_le_rpow_of_exponent_le hBone (hordersBound t ht))
    have hratio : 0 < R / (1 / 8 : ℝ) := by positivity
    have hpower : (((R / (1 / 8 : ℝ)) ^ (beta (γ, t) / t.2)) ^ t.2) =
        (R / (1 / 8 : ℝ)) ^ beta (γ, t) := by
      rw [← Real.rpow_mul hratio.le, div_mul_cancel₀ _ hp0.ne']
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hratio _), hpower] at hm
    exact hm.trans (mul_le_mul_left hAp _)
  have hbetaeta : -γ * t.1 * t.2 + beta (γ, t) = weightedCutoffMomentScaleExponent γ t.1 t.2 := by
    dsimp [beta, weightedCutoffMomentScaleExponent, Q]
    field_simp [hγpos.ne']
   ; ring
  have hcoefReal : ((2 * R) ^ (-γ * t.1)) ^ t.2 * (R / (1 / 8 : ℝ)) ^ beta (γ, t) =
      coeff (γ, t) * R ^ weightedCutoffMomentScaleExponent γ t.1 t.2 := by
    rw [← Real.rpow_mul (by positivity : 0 ≤ 2 * R), Real.mul_rpow (by norm_num) hR.le,
      div_eq_mul_inv, Real.mul_rpow hR.le (by positivity),
      Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 8),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
    calc
      _ = coeff (γ, t) * (R ^ (-γ * t.1 * t.2) * R ^ beta (γ, t)) := by dsimp [coeff]; ring
      _ = _ := by rw [← Real.rpow_add hR, hbetaeta]
  have hcoefENN : ENNReal.ofReal ((2 * R) ^ (-γ * t.1)) ^ t.2 *
      ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta (γ, t)) =
      ENNReal.ofReal (coeff (γ, t)) * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity), hcoefReal, ENNReal.ofReal_mul (by positivity)]
  have hout := cutoffWeightedGmcBallMoment_le_outer_scale_moment
    P X hX Xc hXc γ t.1 hγpos hα z R δ hδ hδR t.2 hp0.le
  calc
    _ ≤ ENNReal.ofReal ((2 * R) ^ (-γ * t.1)) ^ t.2 *
        (B ^ q * ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta (γ, t))) :=
      hout.trans (mul_le_mul_right hmoment _)
    _ = (ENNReal.ofReal ((2 * R) ^ (-γ * t.1)) ^ t.2 *
        ENNReal.ofReal ((R / (1 / 8 : ℝ)) ^ beta (γ, t))) * B ^ q := by ac_rfl
    _ = (ENNReal.ofReal (coeff (γ, t)) * ENNReal.ofReal
        (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2)) * B ^ q := by rw [hcoefENN]
    _ ≤ C * ENNReal.ofReal (R ^ weightedCutoffMomentScaleExponent γ t.1 t.2) := by
      dsimp [C]
      rw [mul_right_comm]
      apply mul_le_mul_left
      apply mul_le_mul_left
      exact ENNReal.ofReal_le_ofReal (hmax ⟨hγ, ht⟩)

end DOZZ.Proofs
